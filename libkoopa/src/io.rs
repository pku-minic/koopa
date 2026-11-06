use std::fs::File;
use std::io::{Error, ErrorKind, Result};
#[cfg(unix)]
use std::os::fd::{BorrowedFd, RawFd};
#[cfg(windows)]
use std::os::windows::io::{BorrowedHandle, RawHandle};

/// Raw file ID.
#[cfg(unix)]
pub(crate) type RawFile = RawFd;

/// Raw file ID.
#[cfg(windows)]
pub(crate) type RawFile = RawHandle;

/// Duplicates a caller-owned file descriptor without taking its ownership.
#[cfg(unix)]
pub(crate) fn file_from_raw(fd: RawFile) -> Result<File> {
  if fd < 0 {
    return Err(Error::new(
      ErrorKind::InvalidInput,
      "invalid file descriptor",
    ));
  }
  // SAFETY: the C API accepts an open descriptor, which remains borrowed for
  // this call only. The returned File owns a separate descriptor.
  unsafe { BorrowedFd::borrow_raw(fd) }
    .try_clone_to_owned()
    .map(File::from)
}

/// Duplicates a caller-owned file handle without taking its ownership.
#[cfg(windows)]
pub(crate) fn file_from_raw(handle: RawFile) -> Result<File> {
  if handle.is_null() || handle as isize == -1 {
    return Err(Error::new(ErrorKind::InvalidInput, "invalid file handle"));
  }
  // SAFETY: the C API accepts an open handle, which remains borrowed for
  // this call only. The returned File owns a separate handle.
  unsafe { BorrowedHandle::borrow_raw(handle) }
    .try_clone_to_owned()
    .map(File::from)
}

// These tests exercise OS descriptor ownership, which Miri isolation cannot access.
#[cfg(all(test, not(miri)))]
mod tests {
  use super::*;
  use crate::{
    ErrorCode, koopa_delete_program, koopa_dump_llvm_to_raw, koopa_dump_to_raw,
    koopa_parse_from_raw,
  };
  use std::io::{Read, Seek, SeekFrom, Write};
  use std::path::PathBuf;
  use std::sync::atomic::{AtomicUsize, Ordering};

  struct TestFile {
    file: Option<File>,
    path: PathBuf,
  }

  impl TestFile {
    fn new() -> Self {
      static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
      let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target");
      std::fs::create_dir_all(&dir).unwrap();
      let path = dir.join(format!(
        "raw-io-{}-{}.koopa",
        std::process::id(),
        NEXT_ID.fetch_add(1, Ordering::Relaxed)
      ));
      let file = File::options()
        .read(true)
        .write(true)
        .create_new(true)
        .open(&path)
        .unwrap();
      Self {
        file: Some(file),
        path,
      }
    }
  }

  impl std::ops::Deref for TestFile {
    type Target = File;

    fn deref(&self) -> &File {
      self.file.as_ref().unwrap()
    }
  }

  impl std::ops::DerefMut for TestFile {
    fn deref_mut(&mut self) -> &mut File {
      self.file.as_mut().unwrap()
    }
  }

  impl Drop for TestFile {
    fn drop(&mut self) {
      drop(self.file.take());
      std::fs::remove_file(&self.path).unwrap();
    }
  }

  #[cfg(unix)]
  fn raw_file(file: &File) -> RawFile {
    use std::os::fd::AsRawFd;
    file.as_raw_fd()
  }

  #[cfg(windows)]
  fn raw_file(file: &File) -> RawFile {
    use std::os::windows::io::AsRawHandle;
    file.as_raw_handle()
  }

  #[test]
  fn raw_io_keeps_the_callers_file_open() {
    let mut file = TestFile::new();
    file
      .write_all(b"fun @main(): i32 { %entry: ret 42 }")
      .unwrap();
    file.rewind().unwrap();
    let mut program = std::ptr::null_mut();
    assert!(matches!(
      koopa_parse_from_raw(raw_file(&file), &mut program),
      ErrorCode::Success
    ));

    for dump in [koopa_dump_to_raw, koopa_dump_llvm_to_raw] {
      file.set_len(0).unwrap();
      file.seek(SeekFrom::Start(0)).unwrap();
      assert!(matches!(
        dump(unsafe { &*program }, raw_file(&file)),
        ErrorCode::Success
      ));
      file.rewind().unwrap();
      let mut output = String::new();
      file.read_to_string(&mut output).unwrap();
      assert!(output.contains("@main"));
      assert!(output.contains("42"));
    }
    unsafe { koopa_delete_program(program) };
  }

  #[test]
  fn invalid_raw_file_returns_an_error() {
    #[cfg(unix)]
    let invalid = -1;
    #[cfg(windows)]
    let invalid = std::ptr::null_mut();
    let mut program = std::ptr::null_mut();
    assert!(matches!(
      koopa_parse_from_raw(invalid, &mut program),
      ErrorCode::InvalidFile
    ));
    assert!(program.is_null());
  }

  #[test]
  fn parse_error_keeps_the_callers_file_open() {
    let mut file = TestFile::new();
    file.write_all(b"invalid").unwrap();
    file.rewind().unwrap();
    let mut program = std::ptr::null_mut();
    assert!(matches!(
      koopa_parse_from_raw(raw_file(&file), &mut program),
      ErrorCode::InvalidKoopaProgram
    ));
    assert!(program.is_null());
    file.rewind().unwrap();
    file.write_all(b"still open").unwrap();
  }
}
