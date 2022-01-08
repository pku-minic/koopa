use crate::errors::{unwrap_or_return, ErrorCode};
use crate::io::{file_from_raw, RawFile};
use crate::utils::{drop_pointer, ffi, new_pointer};
use koopa::front::{span::FileType, Driver};
use koopa::ir::Program;
use std::ffi::CStr;
use std::io::stdin;
use std::os::raw::c_char;

ffi! {
  /// Parses text-form Koopa IR program from the given file.
  /// Updates the `program` if no error occurred.
  ///
  /// Returns the error code.
  fn koopa_parse_from_file(path: *mut c_char, program: &mut *mut Program) -> ErrorCode {
    let path = unwrap_or_return!(unsafe { CStr::from_ptr(path) }.to_str(), InvalidUtf8String);
    let driver = unwrap_or_return!(Driver::from_path(path), InvalidFile);
    let prog = unwrap_or_return!(driver.generate_program(), InvalidKoopaProgram);
    *program = new_pointer(prog);
    ErrorCode::Success
  }

  /// Parses text-form Koopa IR program from the given string.
  /// Updates the `program` if no error occurred.
  ///
  /// Returns the error code.
  fn koopa_parse_from_string(s: *mut c_char, program: &mut *mut Program) -> ErrorCode {
    let s = unwrap_or_return!(unsafe { CStr::from_ptr(s) }.to_str(), InvalidUtf8String);
    let driver = Driver::from(s);
    let prog = unwrap_or_return!(driver.generate_program(), InvalidKoopaProgram);
    *program = new_pointer(prog);
    ErrorCode::Success
  }

  /// Parses text-form Koopa IR program from the standard input.
  /// Updates the `program` if no error occurred.
  ///
  /// Returns the error code.
  fn koopa_parse_from_stdin(program: &mut *mut Program) -> ErrorCode {
    let driver = Driver::from(stdin());
    let prog = unwrap_or_return!(driver.generate_program(), InvalidKoopaProgram);
    *program = new_pointer(prog);
    ErrorCode::Success
  }

  /// Parses text-form Koopa IR program from the given
  /// file descriptor (UNIX) or handle (Windows).
  /// Updates the `program` if no error occurred.
  ///
  /// Returns the error code.
  fn koopa_parse_from_raw(file: RawFile, program: &mut *mut Program) -> ErrorCode {
    let file = file_from_raw(file);
    let driver = Driver::new(FileType::Buffer, file);
    let prog = unwrap_or_return!(driver.generate_program(), InvalidKoopaProgram);
    *program = new_pointer(prog);
    ErrorCode::Success
  }

  /// Deletes the given program.
  fn koopa_delete_program(program: *mut Program) {
    drop_pointer(program);
  }
}
