use crate::errors::{unwrap_or_return, ErrorCode};
use crate::io::{file_from_raw, RawFile};
use crate::utils::ffi;
use koopa::back::{koopa::Visitor as KoopaVisitor, llvm::Visitor as LlvmVisitor};
use koopa::back::{Generator, Visitor};
use koopa::ir::Program;
use std::ffi::{CStr, CString};
use std::fs::File;
use std::io::{stdout, Stdout};
use std::os::raw::c_char;
use std::slice::from_raw_parts_mut;

/// Generates the given program to the given file.
///
/// Returns the error code.
fn dump_to_file<V>(program: &Program, path: *const c_char) -> ErrorCode
where
  V: Visitor<File> + Default,
{
  let path = unwrap_or_return!(unsafe { CStr::from_ptr(path) }.to_str(), InvalidUtf8String);
  let mut gen = unwrap_or_return!(Generator::<_, V>::from_path(path), InvalidFile);
  unwrap_or_return!(gen.generate_on(program), IoError);
  ErrorCode::Success
}

/// Generates a null-terminated string of the given program to the
/// given buffer. If the given buffer is null, updates the `len` to
/// the length of the generated string (with out the null-terminator).
///
/// Returns the error code.
fn dump_to_string<V>(program: &Program, buffer: *mut c_char, len: &mut usize) -> ErrorCode
where
  V: Visitor<Vec<u8>> + Default,
{
  let mut gen = Generator::<_, V>::new(Vec::new());
  unwrap_or_return!(gen.generate_on(program), IoError);
  let s = unwrap_or_return!(CString::new(gen.writer()), NullByteError);
  let bytes = s.as_bytes_with_nul();
  if buffer.is_null() {
    *len = bytes.len() - 1;
  } else if *len < bytes.len() {
    return ErrorCode::InsufficientBufferLength;
  } else {
    let buffer = unsafe { from_raw_parts_mut(buffer as *mut u8, bytes.len()) };
    buffer.copy_from_slice(bytes);
  }
  ErrorCode::Success
}

/// Generates the given program to the standard output.
///
/// Returns the error code.
fn dump_to_stdout<V>(program: &Program) -> ErrorCode
where
  V: Visitor<Stdout> + Default,
{
  let mut gen = Generator::<_, V>::new(stdout());
  unwrap_or_return!(gen.generate_on(program), IoError);
  ErrorCode::Success
}

/// Generates the given program to the given
/// file descriptor (UNIX) or handle (Windows).
///
/// Returns the error code.
fn dump_to_raw<V>(program: &Program, file: RawFile) -> ErrorCode
where
  V: Visitor<File> + Default,
{
  let mut gen = Generator::<_, V>::new(file_from_raw(file));
  unwrap_or_return!(gen.generate_on(program), IoError);
  ErrorCode::Success
}

ffi! {
  /// Generates text-form Koopa IR program to the given file.
  ///
  /// Returns the error code.
  fn koopa_dump_to_file(program: &Program, path: *const c_char) -> ErrorCode {
    dump_to_file::<KoopaVisitor>(program, path)
  }

  /// Generates a null-terminated string of text-form Koopa IR program
  /// to the given buffer. If the given buffer is null, updates the `len`
  /// to the length of the generated string (with out the null-terminator).
  ///
  /// Returns the error code.
  fn koopa_dump_to_string(program: &Program, buffer: *mut c_char, len: &mut usize) -> ErrorCode {
    dump_to_string::<KoopaVisitor>(program, buffer, len)
  }

  /// Generates text-form Koopa IR program to the standard output.
  ///
  /// Returns the error code.
  fn koopa_dump_to_stdout(program: &Program) -> ErrorCode {
    dump_to_stdout::<KoopaVisitor>(program)
  }

  /// Generates text-form Koopa IR program to the given
  /// file descriptor (UNIX) or handle (Windows).
  ///
  /// Returns the error code.
  fn koopa_dump_to_raw(program: &Program, file: RawFile) -> ErrorCode {
    dump_to_raw::<KoopaVisitor>(program, file)
  }

  /// Generates LLVM IR to the given file.
  ///
  /// Returns the error code.
  fn koopa_dump_llvm_to_file(program: &Program, path: *const c_char) -> ErrorCode {
    dump_to_file::<LlvmVisitor>(program, path)
  }

  /// Generates a null-terminated string of LLVM IR to the given buffer.
  /// If the given buffer is null, updates the `len` to the length of
  /// the generated string (with out the null-terminator).
  ///
  /// Returns the error code.
  fn koopa_dump_llvm_to_string(program: &Program, buffer: *mut c_char, len: &mut usize) -> ErrorCode {
    dump_to_string::<LlvmVisitor>(program, buffer, len)
  }

  /// Generates LLVM IR to the standard output.
  ///
  /// Returns the error code.
  fn koopa_dump_llvm_to_stdout(program: &Program) -> ErrorCode {
    dump_to_stdout::<LlvmVisitor>(program)
  }

  /// Generates LLVM IR to the given
  /// file descriptor (UNIX) or handle (Windows).
  ///
  /// Returns the error code.
  fn koopa_dump_llvm_to_raw(program: &Program, file: RawFile) -> ErrorCode {
    dump_to_raw::<LlvmVisitor>(program, file)
  }
}
