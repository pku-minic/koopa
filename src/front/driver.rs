use crate::front::builder::Builder;
use crate::front::lexer::Lexer;
use crate::front::parser::Parser;
use crate::front::span::{FileType, Span};
use std::fs::File;
use std::io::Read;

/// Driver can convert IR in string form to structures.
pub struct Driver<T: Read> {
  parser: Parser<T>,
  builder: Builder,
}

impl<T: Read> Driver<T> {
  /// Creates a new `Driver`.
  pub fn new(ft: FileType, reader: T) -> Self {
    Span::reset(ft);
    Self {
      parser: Parser::new(Lexer::new(reader)),
      builder: Builder::new(),
    }
  }
}
