use super::entities::*;
use koopa::ir::Program;

/// Raw progarm generator that generates raw programs to Koopa IR programs.
#[derive(Default)]
pub struct RawProgramGenerator {
  program: Program,
}

impl RawProgramGenerator {
  /// Creates a new raw program generator.
  pub fn new() -> Self {
    Self::default()
  }

  /// Consumes this generator and returns the generated Koopa IR program.
  pub fn program(self) -> Program {
    self.program
  }

  /// Generates on the given raw program.
  pub fn generate_on(&mut self, raw: &RawProgram) {
    todo!()
  }
}
