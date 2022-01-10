use crate::raw::{RawProgram, RawProgramBuilder};
use crate::utils::{drop_pointer, ffi, new_pointer};
use koopa::ir::Program;

ffi! {
  /// Creates a new raw program builder. Returns its pointer.
  fn koopa_new_raw_program_builder() -> *mut RawProgramBuilder {
    new_pointer(RawProgramBuilder::new())
  }

  /// Frees allocated memory of the given raw program builder.
  fn koopa_delete_raw_program_builder(builder: *mut RawProgramBuilder) {
    drop_pointer(builder)
  }

  /// Builds a raw program of the given Koopa IR program
  /// using the given raw program builder.
  fn koopa_build_raw_program(builder: &mut RawProgramBuilder, program: &Program) -> RawProgram {
    builder.build_on(program)
  }
}
