use crate::front::lexer::Lexer;
use crate::front::ast::AstBox;
use std::io::Read;

/// Parser of Koopa IR.
pub struct Parser<T: Read> {
  lexer: Lexer<T>,
}

/// Result returned by `Parser`
pub type Result = std::result::Result<AstBox, String>;

impl<T: Read> Parser<T> {
  /// Creates a new `Parser` from the specific `Lexer`.
  pub fn new(lexer: Lexer<T>) -> Self {
    Self { lexer }
  }

  // TODO
}
