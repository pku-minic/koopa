/// C-compatible error code.
#[repr(i32)]
pub enum ErrorCode {
  Success,
  InvalidUtf8String,
  InvalidFile,
  InvalidKoopaProgram,
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
