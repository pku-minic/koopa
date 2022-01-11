use crate::errors::ErrorCode;
use crate::raw::{generate_program, RawProgram, RawProgramBuilder};
use crate::utils::{drop_pointer, ffi, new_pointer};
use koopa::ir::Program;

ffi! {
  /// Creates a new raw program builder. Returns its pointer.
  fn koopa_new_raw_program_builder() -> *mut RawProgramBuilder {
    new_pointer(RawProgramBuilder::new())
  }

  /// Frees allocated memory of the given raw program builder.
  fn koopa_delete_raw_program_builder(builder: *mut RawProgramBuilder) {
    unsafe { drop_pointer(builder) };
  }

  /// Builds a raw program of the given Koopa IR program
  /// using the given raw program builder.
  fn koopa_build_raw_program<'rpb>(
    builder: &'rpb mut RawProgramBuilder,
    program: &Program,
  ) -> RawProgram<'rpb> {
    builder.build_on(program)
  }

  /// Generates the given raw program to the Koopa IR program.
  /// Updates the `program` if no errors occurred.
  ///
  /// Returns the error code.
  fn koopa_generate_raw_to_koopa(raw: &RawProgram, program: &mut *mut Program) -> ErrorCode {
    match generate_program(raw) {
      Ok(p) => {
        *program = new_pointer(p);
        ErrorCode::Success
      }
      Err(e) => e,
    }
  }
}
