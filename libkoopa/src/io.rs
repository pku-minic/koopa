use std::fs::File;
use std::io::{Error, Result};
#[cfg(unix)]
use std::os::fd::{FromRawFd, RawFd};
#[cfg(windows)]
use std::os::windows::io::{FromRawHandle, RawHandle};

/// Raw file ID.
#[cfg(unix)]
pub(crate) type RawFile = RawFd;

/// Raw file ID.
#[cfg(windows)]
pub(crate) type RawFile = RawHandle;

/// Duplicates a caller-owned file descriptor without taking its ownership.
#[cfg(unix)]
pub(crate) fn file_from_raw(fd: RawFile) -> Result<File> {
  #[cfg(not(any(target_os = "espidf", target_os = "vita")))]
  let command = libc::F_DUPFD_CLOEXEC;
  #[cfg(any(target_os = "espidf", target_os = "vita"))]
  let command = libc::F_DUPFD;
  // fcntl checks the raw descriptor and returns a new, owned descriptor.
  // Keep standard input/output/error slots free when they are closed.
  let duplicate = unsafe { libc::fcntl(fd, command, 3) };
  if duplicate < 0 {
    return Err(Error::last_os_error());
  }
  Ok(unsafe { File::from_raw_fd(duplicate) })
}

/// Duplicates a caller-owned file handle without taking its ownership.
#[cfg(windows)]
pub(crate) fn file_from_raw(handle: RawFile) -> Result<File> {
  use windows_sys::Win32::Foundation::{
    DUPLICATE_SAME_ACCESS, DuplicateHandle, INVALID_HANDLE_VALUE,
  };
  use windows_sys::Win32::System::Threading::GetCurrentProcess;

  // INVALID_HANDLE_VALUE also denotes the current process to DuplicateHandle.
  if handle.is_null() || handle == INVALID_HANDLE_VALUE {
    return Err(Error::new(
      std::io::ErrorKind::InvalidInput,
      "invalid file handle",
    ));
  }
  let process = unsafe { GetCurrentProcess() };
  let mut duplicate = std::ptr::null_mut();
  // DuplicateHandle validates the source and initializes a non-inheritable,
  // owned handle on success.
  if unsafe {
    DuplicateHandle(
      process,
      handle,
      process,
      &mut duplicate,
      0,
      0,
      DUPLICATE_SAME_ACCESS,
    )
  } == 0
  {
    return Err(Error::last_os_error());
  }
  Ok(unsafe { File::from_raw_handle(duplicate) })
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
    let invalid_files = [-1, RawFd::MAX];
    #[cfg(windows)]
    let invalid_files = [
      std::ptr::null_mut(),
      windows_sys::Win32::Foundation::INVALID_HANDLE_VALUE,
      std::ptr::without_provenance_mut(isize::MAX as usize & !3),
    ];
    for invalid in invalid_files {
      let mut program = std::ptr::null_mut();
      assert!(matches!(
        koopa_parse_from_raw(invalid, &mut program),
        ErrorCode::InvalidFile
      ));
      assert!(program.is_null());
    }
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
