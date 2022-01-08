/// C-compatible error code.
#[repr(i32)]
pub enum ErrorCode {
  Success = 0,
  InvalidUtf8String,
  InvalidFile,
  InvalidKoopaProgram,
  IoError,
  NullByteError,
  InsufficientBufferLength,
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
