use crate::front::span::Span;

/// AST of Koopa IR.
pub struct Ast {
  pub span: Span,
  pub kind: AstKind,
}

/// Box of AST.
pub type AstBox = Box<Ast>;

impl Ast {
  // TODO
}

/// Kind of AST.
pub enum AstKind {
  /// End of file.
  End,
}
