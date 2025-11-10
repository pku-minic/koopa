use std::fs::File;
#[cfg(unix)]
use std::os::unix::io::{FromRawFd, RawFd};
#[cfg(windows)]
use std::os::windows::io::{FromRawHandle, RawHandle};

/// Raw file ID.
#[cfg(unix)]
pub(crate) type RawFile = RawFd;

/// Raw file ID.
#[cfg(windows)]
pub(crate) type RawFile = RawHandle;

/// Returns a [`File`] object from the given raw file ID.
#[cfg(unix)]
pub(crate) fn file_from_raw(fd: RawFile) -> File {
  unsafe { File::from_raw_fd(fd) }
}

/// Returns a [`File`] object from the given raw file ID.
#[cfg(windows)]
pub(crate) fn file_from_raw(handle: RawFile) -> File {
  unsafe { File::from_raw_handle(handle) }
}
