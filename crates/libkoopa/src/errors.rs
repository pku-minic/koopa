/// C-compatible error code.
#[repr(i32)]
pub enum ErrorCode {
  /// No errors occurred.
  Success = 0,
  /// UTF-8 string conversion error.
  InvalidUtf8String,
  /// File operation error.
  InvalidFile,
  /// Koopa IR program parsing error.
  InvalidKoopaProgram,
  /// IO operation error.
  IoError,
  /// Byte array to C string conversion error.
  NullByteError,
  /// Insufficient buffer length.
  InsufficientBufferLength,
  /// Mismatch of item kind in raw slice.
  RawSliceItemKindMismatch,
}

/// Unwraps a [`Result`], or returns the given error code on error.
macro_rules! unwrap_or_return {
  ($result:expr, $err:ident) => {
    match $result {
      Ok(ok) => ok,
      Err(_) => return crate::errors::ErrorCode::$err,
    }
  };
}
pub(crate) use unwrap_or_return;
