//! The optimizer of the in-memory form Koopa IR.
//!
//! This module provides pass traits and the pass manager for optimizing
//! in-memory form Koopa IR programs, including:
//!
//! * The module pass trait ([`ModulePass`](pass::ModulePass)) and the
//!   function pass trait ([`FunctionPass`](pass::FunctionPass)).
//! * The pass manager ([`PassManager`]) that holds all registered passes,
//!   and uses them to optimize the given Koopa IR program.
//!
//! # Example
//!
//! Implement a pass that converts all function names to uppercase:
//!
//! ```
//! use koopa::opt::*;
//! use koopa::ir::Program;
//!
//! struct FunctionNameToUpper;
//!
//! impl ModulePass for FunctionNameToUpper {
//!   fn run_on(&mut self, program: &mut Program) {
//!     // convert all function names to uppercase
//!     for func in program.funcs_mut().values_mut() {
//!       let new_name = func.name().to_uppercase();
//!       func.set_name(new_name);
//!     }
//!   }
//! }
//!
//! // register pass
//! let mut passman = PassManager::new();
//! passman.register(Pass::Module(Box::new(FunctionNameToUpper)));
//!
//! // run passes on the Koopa IR program
//! # let mut program = Program::new();
//! passman.run_passes(&mut program);
//! ```

mod pass;
mod passman;

pub use pass::*;
pub use passman::PassManager;
