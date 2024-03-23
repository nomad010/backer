use anyhow::{Ok, Result};
use checksum::crc64::Crc64;
use clap::{Parser, Subcommand};
use flate2::Status;
use flate2::{Compress, Compression, FlushCompress};
use lru::LruCache;
use memmap2::{MmapMut, MmapOptions};
use std::fs::OpenOptions;
use std::io::Read;
use std::io::Write;
use std::io::{Error, Seek};
use std::marker::PhantomData;
use std::mem;
use std::num::NonZeroUsize;
use std::ops::{Deref, DerefMut};
use std::sync::Arc;
use std::{
    fs::File,
    path::{PathBuf, MAIN_SEPARATOR},
    sync::{
        atomic::{AtomicU32, AtomicU64, Ordering},
        Mutex,
    },
};
use walkdir::WalkDir;

#[repr(C)]
pub struct InnerArchivalState {
    magic_header: [u8; 4],
    next_free_byte: AtomicU64,
    snapshots: AtomicU64,
    last_snapshot_block: AtomicU64,
    reserved: [u8; 4051],
}

impl InnerArchivalState {
    fn request_bytes(&self, size: u64) -> u64 {
        self.next_free_byte.fetch_add(size, Ordering::SeqCst)
    }
}
pub struct ArchiveState {
    file: File,
    resize_lock: Arc<Mutex<()>>,
    header_mapping: MmapMut,
    current_len: AtomicU64,
}

impl ArchiveState {
    const ARCHIVE_GROWTH_SIZE: u64 = 1024 * 1024;

    fn new(mut file: File) -> Result<Self> {
        file.seek(std::io::SeekFrom::Start(0))?;
        file.write(&[b'B', b'A', b'K', 1])?;
        file.set_len(4096)?;
        let header_mapping = unsafe { MmapMut::map_mut(&file)? };
        let header = unsafe { &*(header_mapping[0..4096].as_ptr() as *const InnerArchivalState) };
        header.next_free_byte.store(4096, Ordering::SeqCst);
        header.snapshots.store(0, Ordering::SeqCst);
        header.last_snapshot_block.store(0, Ordering::SeqCst);
        header_mapping.flush_range(0, 4096)?;

        let result = Self {
            header_mapping,
            file,
            resize_lock: Arc::new(Mutex::new(())),
            current_len: AtomicU64::new(4096),
        };

        Ok(result)
    }

    fn request_mapping(&self, size: u64) -> Result<(MmapMut, u64)> {
        let header =
            unsafe { &*(self.header_mapping[0..4096].as_ptr() as *const InnerArchivalState) };
        let start = header.request_bytes(size);
        let end = start + size;

        if end >= self.current_len.load(Ordering::SeqCst) {
            let guard = self.resize_lock.lock().unwrap();

            let current_len = self.current_len.load(Ordering::SeqCst);

            if end >= current_len {
                let new_len = ((current_len + size + Self::ARCHIVE_GROWTH_SIZE - 1)
                    / Self::ARCHIVE_GROWTH_SIZE)
                    * Self::ARCHIVE_GROWTH_SIZE;
                self.file.set_len(new_len)?;
                self.current_len.store(new_len, Ordering::SeqCst);
            }
            mem::drop(guard);
        }

        unsafe {
            let mapping = MmapOptions::new()
                .offset(start)
                .len(size as usize)
                .map_mut(&self.file)?;
            Ok((mapping, start))
        }
    }

    fn shrink(&self) -> Result<()> {
        let header =
            unsafe { &*(self.header_mapping[0..4096].as_ptr() as *const InnerArchivalState) };
        self.file
            .set_len(header.next_free_byte.load(Ordering::SeqCst))?;
        Ok(())
    }

    fn create_snapshot(&self) -> Result<ArchiveSnapshot<'_>> {
        let header =
            unsafe { &*(self.header_mapping[0..4096].as_ptr() as *const InnerArchivalState) };
        let (snapshot_mapping, header_offset) = self.request_mapping(4096)?;
        let previous_snapshot = header
            .last_snapshot_block
            .swap(header_offset, Ordering::SeqCst);
        ArchiveSnapshot::new(self, snapshot_mapping, previous_snapshot)
    }
}

pub trait BlockDetails {
    fn initialise_block(new_map: &mut MmapMut, new_offset: u64, old_map: Option<MmapMut>) -> usize;
}

pub struct BlockManager<'a, T: BlockDetails> {
    mapping: MmapMut,
    location: u64,
    size: u64,
    lord: &'a ArchiveState,
    write_offset: usize,
    phantom: PhantomData<T>,
}

impl<'a, T: BlockDetails> BlockManager<'a, T> {
    fn new(lord: &'a ArchiveState, size: u64) -> Result<Self> {
        let (mut mapping, location) = lord.request_mapping(size)?;
        let write_offset = T::initialise_block(&mut mapping, location, None);
        Ok(Self {
            mapping,
            location,
            size,
            lord,
            write_offset,
            phantom: PhantomData,
        })
    }

    fn writable_slice(&mut self) -> Result<&mut [u8]> {
        if self.mapping.len() == self.write_offset {
            let (new_mapping, new_offset) = self.lord.request_mapping(self.size)?;
            let old_mapping = mem::replace(&mut self.mapping, new_mapping);
            self.location = new_offset;
            self.write_offset =
                T::initialise_block(&mut self.mapping, new_offset, Some(old_mapping));
        }
        Ok(&mut self.mapping[self.write_offset..])
    }
}

impl<'a, T: BlockDetails> Write for BlockManager<'a, T> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let mut position = 0;
        while position < buf.len() {
            let mut mapping = self
                .writable_slice()
                .map_err(|_| Error::other("failed to request a new block"))?;

            // Write as much as we can into the writable segment
            let bytes_written = mapping.write(&buf[position..])?;
            self.write_offset += bytes_written;
            position += bytes_written;
        }
        std::io::Result::Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.mapping.flush()
    }
}

struct SnapshotBlockDetails {}

impl BlockDetails for SnapshotBlockDetails {
    fn initialise_block(
        new_mapping: &mut MmapMut,
        new_offset: u64,
        mut old_mapping: Option<MmapMut>,
    ) -> usize {
        new_mapping[0] = b'S';
        new_mapping[1] = b'N';
        new_mapping[2] = b'P';
        new_mapping[3] = 1;
        MAIN_SEPARATOR.encode_utf8(&mut new_mapping[4..8]);

        if let Some(ref mut old_mapping) = old_mapping {
            [
                old_mapping[8 + 0],
                old_mapping[8 + 1],
                old_mapping[8 + 2],
                old_mapping[8 + 3],
                old_mapping[8 + 4],
                old_mapping[8 + 5],
                old_mapping[8 + 6],
                old_mapping[8 + 7],
            ] = new_offset.to_ne_bytes();
        }

        32
    }
}

struct ArchiveTargets {
    targets: Vec<String>,
}

impl ArchiveTargets {
    fn to_bytes(self) -> Box<[u8]> {
        let mut result = Vec::new();
        result.extend_from_slice(&self.targets.len().to_ne_bytes());
        for target in self.targets {
            result.extend_from_slice(target.as_bytes());
            result.push(0);
        }
        result.into()
    }
}

struct ArchiveTargetsBlockDetails {}

impl BlockDetails for ArchiveTargetsBlockDetails {
    fn initialise_block(
        new_mapping: &mut MmapMut,
        new_offset: u64,
        mut old_mapping: Option<MmapMut>,
    ) -> usize {
        new_mapping[0] = b'T';
        new_mapping[1] = b'A';
        new_mapping[2] = b'R';
        new_mapping[3] = 1;

        if let Some(ref mut old_mapping) = old_mapping {
            [
                old_mapping[4 + 0],
                old_mapping[4 + 1],
                old_mapping[4 + 2],
                old_mapping[4 + 3],
                old_mapping[4 + 4],
                old_mapping[4 + 5],
                old_mapping[4 + 6],
                old_mapping[4 + 7],
            ] = new_offset.to_ne_bytes();
        }

        32
    }
}

struct ArchiveTargetsManager<'a> {
    block_manager: BlockManager<'a, ArchiveTargetsBlockDetails>,
}

struct SnapshotInfo {
    time: String,
    previous_snapshot: u64,
    streams: Vec<u64>,
}

struct SnapshotManager<'a> {
    block_manager: BlockManager<'a, SnapshotBlockDetails>,
}

#[repr(C)]
struct InnerArchiveSnapshot {
    magic_header: [u8; 4],
    num_streams: AtomicU32,
    previous_snapshot: AtomicU64,
    streams: [AtomicU64; 16],
    reserved: [u8; 3892],
}

struct ArchiveSnapshot<'a> {
    lord: &'a ArchiveState,
    mapping: MmapMut,
}

impl<'a> ArchiveSnapshot<'a> {
    fn new(lord: &'a ArchiveState, mapping: MmapMut, previous_snapshot: u64) -> Result<Self> {
        let header = unsafe { &mut *(mapping[0..4096].as_ptr() as *mut InnerArchiveSnapshot) };
        header.magic_header = [b'S', b'N', b'A', b'P'];
        header.num_streams.store(0, Ordering::SeqCst);
        header
            .previous_snapshot
            .store(previous_snapshot, Ordering::SeqCst);
        mapping.flush()?;
        Ok(ArchiveSnapshot { lord, mapping })
    }

    fn create_stream(&self) -> Result<ArchiveSnapshotStreamState> {
        let header = unsafe { &mut *(self.mapping[0..4096].as_ptr() as *mut InnerArchiveSnapshot) };
        header.num_streams.fetch_add(1, Ordering::SeqCst);
        let prefixes = PrefixListManager::new(&self.lord)?;
        let index = IndexManager::new(&self.lord)?;
        let data = DataManager::new(&self.lord, 8 * 1024)?;
        // let large_data = LargeDataManager::new(&self);
        Ok(ArchiveSnapshotStreamState::new(
            prefixes,
            index,
            data,
            4 * 1024 * 1024,
        ))
    }
}

pub enum SnapshotEntry {
    /// Indicates that the compressor state should be reset
    CompressorReset { location: u64 },
    /// Indicates that a new file is to be started
    File {
        /// The prefix for the name of the file
        prefix_entry: u64,
        /// Name of the file
        name: String,
    },
    /// Marks the end of the compressed file.
    FileMetadata {
        /// Size of the uncompressed file in bytes
        uncompressed_file_size: u64,
        /// Checksum of the uncompressed file
        checksum: u64,
    },
}

impl SnapshotEntry {
    const COMPRESSOR_RESET_DISCRIMINANT: u8 = 1;
    const FILE_DISCRIMINANT: u8 = 2;
    const FILE_METADATA_DISCRIMINANT: u8 = 3;

    fn to_bytes(self) -> Box<[u8]> {
        match self {
            Self::CompressorReset { location } => {
                let mut result = Vec::new();
                result.push(Self::COMPRESSOR_RESET_DISCRIMINANT);
                result.extend_from_slice(&location.to_ne_bytes());
                result.into()
            }
            Self::File { prefix_entry, name } => {
                let mut result = Vec::new();
                result.push(Self::FILE_DISCRIMINANT);
                result.extend_from_slice(&prefix_entry.to_ne_bytes());
                result.extend_from_slice(name.as_bytes());
                result.push(0);
                result.into()
            }
            Self::FileMetadata {
                uncompressed_file_size,
                checksum,
            } => {
                let mut result = Vec::new();
                result.push(Self::FILE_METADATA_DISCRIMINANT);
                result.extend_from_slice(&uncompressed_file_size.to_ne_bytes());
                result.extend_from_slice(&checksum.to_ne_bytes());
                result.into()
            }
        }
    }
}

struct PrefixBlockDetails {}

impl BlockDetails for PrefixBlockDetails {
    fn initialise_block(
        new_mapping: &mut MmapMut,
        new_offset: u64,
        mut old_mapping: Option<MmapMut>,
    ) -> usize {
        new_mapping[0] = b'P';
        new_mapping[1] = b'F';
        new_mapping[2] = b'X';
        new_mapping[3] = 1;
        MAIN_SEPARATOR.encode_utf8(&mut new_mapping[4..8]);

        if let Some(ref mut old_mapping) = old_mapping {
            [
                old_mapping[8 + 0],
                old_mapping[8 + 1],
                old_mapping[8 + 2],
                old_mapping[8 + 3],
                old_mapping[8 + 4],
                old_mapping[8 + 5],
                old_mapping[8 + 6],
                old_mapping[8 + 7],
            ] = new_offset.to_ne_bytes();
        }

        32
    }
}

struct PrefixListManager<'a> {
    block_manager: BlockManager<'a, PrefixBlockDetails>,
    prefix_cache: LruCache<String, u64>,
    stored_prefixes: u64,
}

impl<'a> PrefixListManager<'a> {
    fn new(lord: &'a ArchiveState) -> Result<Self> {
        Ok(Self {
            block_manager: BlockManager::new(lord, 4 * 1024)?,
            prefix_cache: LruCache::new(unsafe { NonZeroUsize::new(100).unwrap_unchecked() }),
            stored_prefixes: 0,
        })
    }

    fn add_prefix(&mut self, prefix: &str) -> Result<u64> {
        if let Some(location) = self.prefix_cache.get(prefix) {
            Ok(*location)
        } else {
            self.block_manager.write(prefix.as_bytes())?;
            self.block_manager.write(&[0])?;
            let prefix_id = self.stored_prefixes;
            self.stored_prefixes += 1;
            self.prefix_cache.put(prefix.to_string(), prefix_id);
            Ok(prefix_id)
        }
    }
}

struct IndexBlockDetails {}

impl BlockDetails for IndexBlockDetails {
    fn initialise_block(
        new_mapping: &mut MmapMut,
        new_offset: u64,
        mut old_mapping: Option<MmapMut>,
    ) -> usize {
        new_mapping[0] = b'I';
        new_mapping[1] = b'D';
        new_mapping[2] = b'X';
        new_mapping[3] = 1;
        if let Some(ref mut old_mapping) = old_mapping {
            [
                old_mapping[4 + 0],
                old_mapping[4 + 1],
                old_mapping[4 + 2],
                old_mapping[4 + 3],
                old_mapping[4 + 4],
                old_mapping[4 + 5],
                old_mapping[4 + 6],
                old_mapping[4 + 7],
            ] = new_offset.to_ne_bytes();
        }

        32
    }
}

struct IndexManager<'a>(BlockManager<'a, IndexBlockDetails>);

impl<'a> IndexManager<'a> {
    fn new(lord: &'a ArchiveState) -> Result<Self> {
        Ok(Self(BlockManager::new(lord, 4 * 1024)?))
    }
}

impl<'a> Deref for IndexManager<'a> {
    type Target = BlockManager<'a, IndexBlockDetails>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> DerefMut for IndexManager<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

struct DataBlockDetails {}

impl BlockDetails for DataBlockDetails {
    fn initialise_block(
        new_mapping: &mut MmapMut,
        new_offset: u64,
        old_mapping: Option<MmapMut>,
    ) -> usize {
        new_mapping[0] = b'D';
        new_mapping[1] = b'A';
        new_mapping[2] = b'T';
        new_mapping[3] = 1;
        [
            new_mapping[4 + 0],
            new_mapping[4 + 1],
            new_mapping[4 + 2],
            new_mapping[4 + 3],
            new_mapping[4 + 4],
            new_mapping[4 + 5],
            new_mapping[4 + 6],
            new_mapping[4 + 7],
        ] = (new_mapping.len() as u64).to_ne_bytes();
        if let Some(mut old_mapping) = old_mapping {
            [
                old_mapping[12 + 0],
                old_mapping[12 + 1],
                old_mapping[12 + 2],
                old_mapping[12 + 3],
                old_mapping[12 + 4],
                old_mapping[12 + 5],
                old_mapping[12 + 6],
                old_mapping[12 + 7],
            ] = new_offset.to_ne_bytes();
        }
        32
    }
}

struct DataManager<'a>(BlockManager<'a, DataBlockDetails>);

impl<'a> DataManager<'a> {
    fn new(lord: &'a ArchiveState, size: u64) -> Result<Self> {
        Ok(Self(BlockManager::new(lord, size)?))
    }
}

impl<'a> Deref for DataManager<'a> {
    type Target = BlockManager<'a, DataBlockDetails>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> DerefMut for DataManager<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

struct ArchiveSnapshotStreamState<'a> {
    prefixes: PrefixListManager<'a>,
    index: IndexManager<'a>,
    data: DataManager<'a>,

    read_bytes_buffer: Vec<u8>,

    compressor: Compress,
    compressor_entries: u64,

    checksummer: Crc64,
}

impl<'a> ArchiveSnapshotStreamState<'a> {
    const MAX_WRITTEN_BYTES: u64 = 16 * 1024;
    const MAX_WRITTEN_ENTRIES: u64 = 10;

    pub fn new(
        prefixes: PrefixListManager<'a>,
        index: IndexManager<'a>,
        data: DataManager<'a>,
        read_buffer_size: usize,
    ) -> Self {
        let read_bytes_buffer = vec![0; read_buffer_size];
        let compressor_entries = 0;
        let checksummer = Crc64::new();
        Self {
            prefixes,
            index,
            data,
            read_bytes_buffer,
            compressor: Compress::new(Compression::new(5), false),
            compressor_entries,
            checksummer,
        }
    }

    fn finish_compressor(&mut self) -> Result<()> {
        loop {
            // The read buffer has no more data, we need to flush the stream
            let out_slice = self.data.writable_slice()?;
            let bytes_written_start = self.compressor.total_out();
            let compression_status =
                self.compressor
                    .compress(&[], out_slice, FlushCompress::Finish)?;
            let bytes_written = self.compressor.total_out() - bytes_written_start;
            self.data.write_offset += bytes_written as usize;

            if matches!(compression_status, Status::StreamEnd) {
                break;
            }
        }
        self.index.write(
            &SnapshotEntry::CompressorReset {
                location: self.data.location + self.data.write_offset as u64,
            }
            .to_bytes(),
        )?;
        self.compressor.reset();
        self.compressor_entries = 0;
        Ok(())
    }

    fn finish(mut self) -> Result<()> {
        self.finish_compressor()
    }

    fn add_item<T: Read>(&mut self, path: String, mut item: T) -> Result<()> {
        let prefix_length = path.rfind(MAIN_SEPARATOR).unwrap_or(0);
        let prefix = &path[0..prefix_length];
        let prefix_entry = self.prefixes.add_prefix(prefix)?;
        let name = path[prefix_length + 1..].to_string();

        if self.compressor.total_out() > Self::MAX_WRITTEN_BYTES
            || self.compressor_entries > Self::MAX_WRITTEN_ENTRIES
        {
            self.finish_compressor()?;
        }
        self.compressor_entries += 1;

        let mut total_size = 0_u64;

        let bytes = SnapshotEntry::File { prefix_entry, name }.to_bytes();
        self.index.write(&bytes)?;

        self.checksummer.reset();

        loop {
            // Input loop
            let bytes_total = item.read(&mut self.read_bytes_buffer)?;
            let mut progress = 0;
            if bytes_total == 0 {
                break;
            }
            self.checksummer
                .update(&self.read_bytes_buffer[..bytes_total]);
            total_size += bytes_total as u64;

            loop {
                // Output loop
                if progress == bytes_total {
                    break;
                }
                let in_slice = &self.read_bytes_buffer[progress..bytes_total];
                let out_slice = self.data.writable_slice()?;

                // Have a block to compress
                let bytes_read_start = self.compressor.total_in();
                let bytes_written_start = self.compressor.total_out();
                self.compressor
                    .compress(in_slice, out_slice, FlushCompress::None)?;
                let bytes_read = self.compressor.total_in() - bytes_read_start;
                progress += bytes_read as usize;
                let bytes_written = self.compressor.total_out() - bytes_written_start;
                self.data.write_offset += bytes_written as usize;
            }
        }

        self.index.write(
            &SnapshotEntry::FileMetadata {
                uncompressed_file_size: total_size as u64,
                checksum: self.checksummer.getsum(),
            }
            .to_bytes(),
        )?;

        Ok(())
    }
}

#[derive(Debug, Parser)] // requires `derive` feature
#[command(name = "backer")]
#[command(about = "A multiversioned backup utility", long_about = None)]
struct Cli {
    /// The target backup to create. If this file exists an error will be returned unless --overwrite is used
    #[arg(required = true)]
    backup_file: PathBuf,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Debug, Subcommand)]
enum Commands {
    /// Creates a backup file
    #[command(arg_required_else_help = true)]
    Create {
        /// The files to compress
        #[arg(required = true)]
        input: Vec<PathBuf>,
        /// Stops before taking a snapshot
        #[arg(short, long)]
        no_snapshot: bool,
        /// Overwrites the output file if it already exists
        #[arg(short, long)]
        overwrite: bool,
        /// Number of compression threads to use, defaults to one
        #[arg(short, long, default_value_t = 1)]
        compression_threads: usize,
    },
    /// Creates a snapshot for the given backup file
    #[command(arg_required_else_help = true)]
    Snapshot {
        /// Number of compression threads to use, defaults to one
        #[arg(short, long, default_value_t = 1)]
        compression_threads: usize,
    },
    #[command(arg_required_else_help = true)]
    ListSnapshots {},
    #[command(arg_required_else_help = true)]
    RestoreSnapshot {
        /// The id of the snapshot or the latest one if not given. Negative numbers are from the end
        snapshot: Option<i64>,
        /// Target directory to restore the snapshot to or the current one if not given.
        target: Option<PathBuf>,
        /// Restoring won't delete files that aren't listed in the snapshot.
        #[arg(short, long)]
        keep_new_entries: bool,
    },
}

impl Cli {
    fn open_options(&self) -> OpenOptions {
        let mut result = OpenOptions::new();
        match self.command {
            Commands::Create { overwrite, .. } => {
                if overwrite {
                    result.read(true).write(true).truncate(true);
                } else {
                    result.read(true).write(true).create_new(true);
                }
            }
            Commands::Snapshot { .. } => {
                result.append(true);
            }
            _ => {
                result.read(true);
            }
        }
        result
    }
}

fn create_archive(backup_path: PathBuf, backup: File, arguments: Commands) {
    if let Commands::Create {
        input,
        no_snapshot,
        overwrite: _overwrite,
        compression_threads,
    } = arguments
    {
        let arc = ArchiveState::new(backup).unwrap();
        let snapshot = arc.create_snapshot().unwrap();
        let mut stream = snapshot.create_stream().unwrap();

        let walker = WalkDir::new("src").sort_by_file_name().into_iter();
        for entry in walker {
            let entry = entry.unwrap();
            if entry.file_type().is_file() {
                stream
                    .add_item(
                        entry.path().to_string_lossy().into_owned(),
                        File::open(entry.path()).unwrap(),
                    )
                    .unwrap();
            }
        }
        stream.finish().unwrap();
        arc.shrink().unwrap();
    } else {
        panic!("Logical error: Commands::Create expected, received {arguments:?}");
    }
}

fn main() {
    let args = Cli::parse();

    let open_options = args.open_options();
    let mut backup_file = open_options.open(&args.backup_file).unwrap();
    match &args.command {
        Commands::Create {
            input,
            no_snapshot,
            overwrite,
            compression_threads,
        } => {
            // f
            create_archive(args.backup_file, backup_file, args.command)
        }
        Commands::Snapshot {
            compression_threads,
        } => {}
        Commands::ListSnapshots {} => {}
        Commands::RestoreSnapshot {
            snapshot,
            target,
            keep_new_entries,
        } => {}
    }

    // let arc = ArchiveState::new("lol.txt".into()).unwrap();
    // let snapshot = arc.create_snapshot().unwrap();
    // let mut stream = snapshot.create_stream().unwrap();

    // let walker = WalkDir::new("src").sort_by_file_name().into_iter();
    // for entry in walker {
    //     let entry = entry.unwrap();
    //     if entry.file_type().is_file() {
    //         stream
    //             .add_item(
    //                 entry.path().to_string_lossy().into_owned(),
    //                 File::open(entry.path()).unwrap(),
    //             )
    //             .unwrap();
    //     }
    // }
    // stream.finish().unwrap();
    // arc.shrink().unwrap();
}
