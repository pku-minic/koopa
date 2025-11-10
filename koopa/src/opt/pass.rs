//! Koopa IR pass traits related implementations.
//!
//! The concept of Koopa IR pass is like the LLVM pass. As stated in the
//! [LLVM documentation](https://llvm.org/docs/WritingAnLLVMPass.html#introduction-what-is-a-pass),
//! passes perform the transformations and optimizations that
//! make up the compiler.

use crate::ir::{Function, FunctionData, Program};

/// A Koopa IR pass.
///
/// Pass can be a [`ModulePass`] or a [`FunctionPass`].
pub enum Pass {
  /// Module pass, runs on IR programs.
  Module(Box<dyn ModulePass>),
  /// Function pass, runs on functions.
  Function(Box<dyn FunctionPass>),
}

/// Trait of a module pass.
///
/// Module passes can run on IR programs.
pub trait ModulePass {
  /// Runs on the given IR program.
  fn run_on(&mut self, program: &mut Program);
}

/// Trait of a function pass.
///
/// Function passes can run on functions.
pub trait FunctionPass {
  /// Runs on the given function data.
  fn run_on(&mut self, func: Function, data: &mut FunctionData);
}
