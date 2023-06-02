//! The backend of the in-memory form Koopa IR.
//!
//! This modules provides generators for generating in-memory form
//! Koopa IR to other forms, including:
//!
//! * The Koopa IR generator ([`Generator`]), name manager ([`NameManager`])
//!   and the Koopa IR visitor trait ([`Visitor`]).
//! * The text form Koopa IR generator ([`KoopaGenerator`]).
//! * The LLVM IR generator ([`LlvmGenerator`]).
//!
//! # Examples
//!
//! Convert the in-memory form Koopa IR program into the text form:
//!
//! ```
//! use koopa::ir::{*, builder_traits::*};
//! use koopa::back::KoopaGenerator;
//!
//! let mut program = Program::new();
//! let main = program.new_func(
//!   FunctionData::new("@main".into(), Vec::new(), Type::get_i32()),
//! );
//! let main_data = program.func_mut(main);
//!
//! let bb = main_data.dfg_mut().new_bb().basic_block(None);
//! main_data.layout_mut().bbs_mut().push_key_back(bb);
//!
//! let lhs = main_data.dfg_mut().new_value().integer(11);
//! let rhs = main_data.dfg_mut().new_value().integer(31);
//! let add = main_data.dfg_mut().new_value().binary(BinaryOp::Add, lhs, rhs);
//! let ret = main_data.dfg_mut().new_value().ret(Some(add));
//! main_data.layout_mut().bb_mut(bb).insts_mut().extend([add, ret]);
//!
//! // convert to text form
//! let mut gen = KoopaGenerator::new(Vec::new());
//! gen.generate_on(&program).unwrap();
//! let text_form_ir = std::str::from_utf8(&gen.writer()).unwrap().to_string();
//! println!("{}", text_form_ir);
//! ```
//!
//! Convert the in-memory form Koopa IR program into the text-form LLVM IR,
//! and save the result to a file:
//!
//! ```no_run
//! use koopa::back::LlvmGenerator;
//!
//! # fn main() -> std::io::Result<()> {
//! # let program = koopa::ir::Program::new();
//! let mut gen = LlvmGenerator::from_path("/path/to/the/output/file")?;
//! gen.generate_on(&program).unwrap();
//! # Ok(())
//! # }
//! ```

pub mod generator;
pub mod koopa;
pub mod llvm;

pub use generator::{Generator, NameManager, Prefix, Visitor};

/// Generator for generating Koopa IR structures into text formatted Koopa IR.
pub type KoopaGenerator<W> = Generator<W, koopa::Visitor>;

/// Generator for generating Koopa IR into LLVM IR.
pub type LlvmGenerator<W> = Generator<W, llvm::Visitor>;
