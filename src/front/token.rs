use crate::front::span::{Pos, Span};
use crate::ir::instructions::{BinaryOp, UnaryOp};
use std::{default::Default, fmt};

/// Tokens that will be generated by the lexer.
pub struct Token {
  pub span: Span,
  pub kind: TokenKind,
}

impl Token {
  /// Creates a new token.
  pub fn new(span: Span, kind: TokenKind) -> Self {
    Self { span, kind }
  }
}

impl Default for Token {
  fn default() -> Self {
    Self {
      span: Span::default(),
      kind: TokenKind::End,
    }
  }
}

/// Kind of token.
#[derive(Debug, PartialEq)]
pub enum TokenKind {
  Int(i64),
  Symbol(String),
  Keyword(Keyword),
  BinaryOp(BinaryOp),
  UnaryOp(UnaryOp),
  Other(char),
  End,
}

impl fmt::Display for TokenKind {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      TokenKind::Int(v) => write!(f, "integer '{}'", v),
      TokenKind::Symbol(v) => write!(f, "symbol '{}'", v),
      TokenKind::Keyword(v) => write!(f, "keyword '{}'", v),
      TokenKind::BinaryOp(v) => write!(f, "binary operator '{}'", v),
      TokenKind::UnaryOp(v) => write!(f, "unary operator '{}'", v),
      TokenKind::Other(v) => write!(f, "character '{}'", v),
      TokenKind::End => write!(f, "end of file"),
    }
  }
}

/// Keywords of Koopa IR.
#[rustfmt::skip]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Keyword {
  I32,
  Undef, ZeroInit,
  Global, Alloc, Load, Store, GetPtr,
  Br, Jump, Call, Ret, Fun, Decl, Phi,
}

impl fmt::Display for Keyword {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Keyword::I32 => f.write_str("i32"),
      Keyword::Undef => f.write_str("undef"),
      Keyword::ZeroInit => f.write_str("zeroinit"),
      Keyword::Global => f.write_str("global"),
      Keyword::Alloc => f.write_str("alloc"),
      Keyword::Load => f.write_str("load"),
      Keyword::Store => f.write_str("store"),
      Keyword::GetPtr => f.write_str("getptr"),
      Keyword::Br => f.write_str("br"),
      Keyword::Jump => f.write_str("jump"),
      Keyword::Call => f.write_str("call"),
      Keyword::Ret => f.write_str("ret"),
      Keyword::Fun => f.write_str("fun"),
      Keyword::Decl => f.write_str("decl"),
      Keyword::Phi => f.write_str("phi"),
    }
  }
}
