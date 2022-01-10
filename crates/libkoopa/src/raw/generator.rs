use super::entities::*;
use crate::errors::ErrorCode;
use koopa::ir::Program;

/// Result returned by raw program generator functions.
pub(crate) type Result<T> = std::result::Result<T, ErrorCode>;

/// Generates the given raw program to Koopa IR program.
pub(crate) fn generate_program(raw: &RawProgram) -> Result<Program> {
  let mut program = Program::new();
  raw.generate(&mut program)?;
  Ok(program)
}

/// Trait for generating on raw structures.
trait GenerateOnRaw {
  /// The type of generated entity.
  type Entity;

  /// Generates a new entity.
  fn generate(&self, program: &mut Program) -> Result<Self::Entity>;
}

impl GenerateOnRaw for RawProgram {
  type Entity = ();

  fn generate(&self, program: &mut Program) -> Result<Self::Entity> {
    //
    Ok(())
  }
}
