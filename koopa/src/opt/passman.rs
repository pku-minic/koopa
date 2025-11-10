//! Pass manager ([`PassManager`]) related implementations.

use crate::ir::Program;
use crate::opt::pass::Pass;

/// The Koopa IR pass manager.
///
/// Pass manager manages all registed passes, and processes the input
/// IR program by using registered passes.
#[derive(Default)]
pub struct PassManager {
  passes: Vec<Pass>,
}

impl PassManager {
  /// Creates a new pass manager.
  pub fn new() -> Self {
    Self::default()
  }

  /// Registers a new pass to the current pass manager.
  pub fn register(&mut self, pass: Pass) {
    self.passes.push(pass);
  }

  /// Runs all registered passes on the given IR program.
  pub fn run_passes(&mut self, program: &mut Program) {
    for pass in &mut self.passes {
      match pass {
        Pass::Module(p) => p.run_on(program),
        Pass::Function(p) => {
          for (func, data) in program.funcs_mut() {
            p.run_on(*func, data);
          }
        }
      }
    }
  }
}

/// Creates a new pass manager from a [`Vec`] of passes.
impl From<Vec<Pass>> for PassManager {
  fn from(passes: Vec<Pass>) -> Self {
    Self { passes }
  }
}
