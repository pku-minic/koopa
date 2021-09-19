pub mod generator;
pub mod koopa;
pub mod llvm;

pub use generator::{Generator, NameManager, Prefix, Visitor};

/// Generator for generating Koopa IR structures into text formatted Koopa IR.
pub type KoopaGenerator<W> = Generator<W, koopa::Visitor>;

/// Generator for generating Koopa IR into LLVM IR.
pub type LlvmGenerator<W> = Generator<W, llvm::Visitor>;
