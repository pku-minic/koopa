use crate::ir::Program;
use crate::opt::pass::Pass;

/// Manages all registed passes.
pub struct PassManager {
  passes: Vec<Pass>,
}

impl PassManager {
  /// Creates a new `PassManager`.
  pub fn new() -> Self {
    Self { passes: Vec::new() }
  }

  /// Registers a new pass to the current pass manager.
  pub fn register(&mut self, pass: Pass) {
    self.passes.push(pass);
  }

  /// Runs on the specific IR program.
  pub fn run_passes(&mut self, program: &mut Program) {
    for pass in &mut self.passes {
      match pass {
        Pass::Module(p) => p.run_on(program),
        Pass::Function(p) => {
          for func in program.funcs() {
            p.run_on(func);
          }
        }
        Pass::BasicBlock(p) => {
          for func in program.funcs() {
            for bb in func.inner().bbs() {
              p.run_on(bb);
            }
          }
        }
      }
    }
  }
}

impl Default for PassManager {
  fn default() -> Self {
    Self::new()
  }
}

/// Creates a new `PassManager` from a `Vec` of passes.
impl From<Vec<Pass>> for PassManager {
  fn from(passes: Vec<Pass>) -> Self {
    Self { passes }
  }
}
