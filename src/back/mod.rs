pub mod generator;
pub mod koopa;

use generator::Generator;

/// Generator for generating Koopa IR structures into text formatted Koopa IR.
pub type KoopaGenerator<W> = Generator<W, koopa::Visitor>;
