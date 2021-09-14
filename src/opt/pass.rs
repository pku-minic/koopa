use crate::ir::structs::{BasicBlock, Function, Program};

/// A Koopa IR pass.
pub enum Pass {
  Module(Box<dyn ModulePass>),
  Function(Box<dyn FunctionPass>),
  BasicBlock(Box<dyn BasicBlockPass>),
}

/// Module pass, runs on IR programs.
pub trait ModulePass {
  /// Runs on the specific IR program.
  fn run_on(&mut self, program: &mut Program);
}

/// Function pass, runs on functions.
pub trait FunctionPass {
  /// Runs on the specific Function.
  fn run_on(&mut self, func: &Function);
}

/// Basic block pass, runs on basic blocks.
pub trait BasicBlockPass {
  /// Runs on the specific basic block.
  fn run_on(&mut self, bb: &BasicBlock);
}
