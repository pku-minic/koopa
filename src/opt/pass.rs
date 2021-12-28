use crate::ir::{Function, FunctionData, Program};

/// A Koopa IR pass.
///
/// Pass can be a [`ModulePass`] or a [`FunctionPass`].
pub enum Pass {
  Module(Box<dyn ModulePass>),
  Function(Box<dyn FunctionPass>),
}

/// Trait of a module pass.
///
/// Module passes can run on IR programs.
pub trait ModulePass {
  /// Runs on the specific IR program.
  fn run_on(&mut self, program: &mut Program);
}

/// Trait of a function pass.
///
/// Function passes can run on functions.
pub trait FunctionPass {
  /// Runs on the specific function data.
  fn run_on(&mut self, func: Function, data: &mut FunctionData);
}
