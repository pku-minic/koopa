//! Koopa IR lexer ([`Lexer`]) related implementations.

use crate::front::span::{Error, Pos, Span};
use crate::front::token::{Keyword, Token, TokenKind};
use crate::ir::BinaryOp;
use crate::{log_raw_fatal_error, return_error};
use std::collections::HashMap;
use std::io::Read;

/// A lexer for lexing text form Koopa IR.
///
/// `Lexer` scans the input text form Koopa IR, and produces
/// token stream for the [`Parser`](crate::front::parser::Parser).
pub struct Lexer<T: Read> {
  reader: T,
  pos: Pos,
  // `None` if EOF
  last_char: Option<char>,
}

/// Result that returned by [`Lexer`].
pub type Result = std::result::Result<Token, Error>;

impl<T: Read> Lexer<T> {
  /// Creates a new lexer from the given reader.
  pub fn new(reader: T) -> Self {
    Self {
      reader,
      pos: Pos::new(),
      last_char: Some(' '),
    }
  }

  /// Returns the next token from file, or a lexer error.
  pub fn next_token(&mut self) -> Result {
    // skip spaces
    while self.last_char.map_or(false, |c| c.is_whitespace()) {
      self.next_char()?;
    }
    // check the last character
    if let Some(c) = self.last_char {
      if c == '/' {
        // skip comments
        self.handle_comment()
      } else if c == '@' || c == '%' {
        // symbols
        self.handle_symbol()
      } else if c.is_alphabetic() {
        // keywords or operands
        self.handle_keyword()
      } else if c.is_numeric() || c == '-' {
        // integer literals
        self.handle_integer()
      } else {
        // other characters
        let pos = self.pos;
        self.next_char()?;
        Ok(Token::new(Span::new(pos), TokenKind::Other(c)))
      }
    } else {
      // may be EOF, or other file errors
      Ok(Token::new(Span::new(self.pos), TokenKind::End))
    }
  }

  /// Reads a character from reader.
  ///
  /// If fails, this method will always return a fatal error.
  fn next_char(&mut self) -> std::result::Result<(), Error> {
    // NOTE: UTF-8 characters will not be handled here.
    let mut single_char = [0];
    self.last_char = (self
      .reader
      .read(&mut single_char)
      .map_err(|err| log_raw_fatal_error!("{}", err))?
      != 0)
      .then(|| {
        let c = single_char[0] as char;
        // update the current position
        self.pos.update(c);
        c
      });
    Ok(())
  }

  /// Handles integer literals.
  fn handle_integer(&mut self) -> Result {
    let mut span = Span::new(self.pos);
    // read to string
    let mut num = String::from(self.last_char.unwrap());
    self.next_char()?;
    while self.last_char.map_or(false, |c| c.is_numeric()) {
      num.push(self.last_char.unwrap());
      span.update(self.pos);
      self.next_char()?;
    }
    // convert to integer
    if let Ok(i) = num.parse() {
      Ok(Token::new(span, TokenKind::Int(i)))
    } else {
      self.log_err_and_skip(span, &format!("invalid integer literal '{}'", num))
    }
  }

  /// Handles symbols.
  fn handle_symbol(&mut self) -> Result {
    let mut span = Span::new(self.pos);
    let tag = self.last_char.unwrap();
    // read the first char to string
    let mut symbol = String::from(tag);
    self.next_char()?;
    // check if number
    if self.last_char.map_or(false, |c| c.is_numeric()) {
      // check if is named symbol
      if tag == '@' {
        return self.log_err_and_skip(span, "invalid named symbol");
      }
      // check the first digit
      let digit = self.last_char.unwrap();
      symbol.push(digit);
      span.update(self.pos);
      self.next_char()?;
      if digit != '0' {
        // read the rest numbers to string
        while self.last_char.map_or(false, |c| c.is_numeric()) {
          symbol.push(self.last_char.unwrap());
          span.update(self.pos);
          self.next_char()?;
        }
      }
    } else {
      // read letters, numbers or underscores
      while self
        .last_char
        .map_or(false, |c| c.is_alphanumeric() || c == '_')
      {
        symbol.push(self.last_char.unwrap());
        span.update(self.pos);
        self.next_char()?;
      }
    }
    // check if only the prefix
    if symbol.len() == 1 {
      self.log_err_and_skip(span, &format!("invalid symbol '{}'", symbol))
    } else {
      Ok(Token::new(span, TokenKind::Symbol(symbol)))
    }
  }

  /// Handles keywords or operands.
  fn handle_keyword(&mut self) -> Result {
    let mut span = Span::new(self.pos);
    // read to string
    let mut keyword = String::new();
    while self.last_char.map_or(false, |c| c.is_alphanumeric()) {
      keyword.push(self.last_char.unwrap());
      span.update(self.pos);
      self.next_char()?;
    }
    // check the string
    if let Some(keyword) = KEYWORDS.with(|m| m.get(keyword.as_str()).copied()) {
      Ok(Token::new(span, TokenKind::Keyword(keyword)))
    } else if let Some(op) = BINARY_OPS.with(|m| m.get(keyword.as_str()).copied()) {
      Ok(Token::new(span, TokenKind::BinaryOp(op)))
    } else {
      self.log_err_and_skip(span, &format!("invalid keyword/operator '{}'", keyword))
    }
  }

  /// Handles comments.
  fn handle_comment(&mut self) -> Result {
    let span = Span::new(self.pos);
    // eat '/'
    self.next_char()?;
    // check if is block comment
    if self.last_char == Some('*') {
      self.handle_block_comment(span)
    } else if self.last_char == Some('/') {
      // skip the current line
      while self.last_char.map_or(false, |c| c != '\r' && c != '\n') {
        self.next_char()?;
      }
      // return the next token
      self.next_token()
    } else {
      self.log_err_and_skip(span.into_updated(self.pos), "invalid comment")
    }
  }

  /// Handles block comments.
  fn handle_block_comment(&mut self, span: Span) -> Result {
    // eat '*'
    self.next_char()?;
    // read until there is '*/' in stream
    let mut star = false;
    while self.last_char.is_some() && !(star && self.last_char == Some('/')) {
      star = self.last_char == Some('*');
      self.next_char()?;
    }
    // check unclosed block comment
    if self.last_char.is_none() {
      self.log_err_and_skip(span.into_updated(self.pos), "comment unclosed at EOF")
    } else {
      // eat '/'
      self.next_char()?;
      self.next_token()
    }
  }

  /// Logs error message to stderr, and skip to the next space character.
  ///
  /// For error recovery support.
  fn log_err_and_skip(&mut self, span: Span, message: &str) -> Result {
    while self.last_char.map_or(false, |c| !c.is_whitespace()) {
      self.next_char()?;
    }
    return_error!(span, "{}", message)
  }
}

macro_rules! hash_map {
  ($($k:expr => $v:expr),* $(,)?) => {{
    let mut map = HashMap::new();
    $(map.insert($k, $v);)*
    map
  }};
}

thread_local! {
  /// All supported keywords.
  static KEYWORDS: HashMap<&'static str, Keyword> = hash_map! {
    "i32" => Keyword::I32,
    "undef" => Keyword::Undef,
    "zeroinit" => Keyword::ZeroInit,
    "global" => Keyword::Global,
    "alloc" => Keyword::Alloc,
    "load" => Keyword::Load,
    "store" => Keyword::Store,
    "getptr" => Keyword::GetPtr,
    "getelemptr" => Keyword::GetElemPtr,
    "br" => Keyword::Br,
    "jump" => Keyword::Jump,
    "call" => Keyword::Call,
    "ret" => Keyword::Ret,
    "fun" => Keyword::Fun,
    "decl" => Keyword::Decl,
  };

  /// All supported binary operators.
  static BINARY_OPS: HashMap<&'static str, BinaryOp> = hash_map! {
    "ne" => BinaryOp::NotEq,
    "eq" => BinaryOp::Eq,
    "gt" => BinaryOp::Gt,
    "lt" => BinaryOp::Lt,
    "ge" => BinaryOp::Ge,
    "le" => BinaryOp::Le,
    "add" => BinaryOp::Add,
    "sub" => BinaryOp::Sub,
    "mul" => BinaryOp::Mul,
    "div" => BinaryOp::Div,
    "mod" => BinaryOp::Mod,
    "and" => BinaryOp::And,
    "or" => BinaryOp::Or,
    "xor" => BinaryOp::Xor,
    "shl" => BinaryOp::Shl,
    "shr" => BinaryOp::Shr,
    "sar" => BinaryOp::Sar,
  };
}

#[cfg(test)]
mod test {
  use super::*;
  use std::io::Cursor;

  #[test]
  fn read_tokens() {
    let buf = Cursor::new(
      r#"
      // comment
      fun @main(): i32 {
      %entry:
        %ret /**/ = alloc i32
        store 0, %ret
        %0 = load %ret
        %1 = add %0, 1
        ret %1
      /*
      block
      comment
      */
      }
      // comment2
      "#,
    );
    let mut lexer = Lexer::new(buf);
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Keyword(Keyword::Fun)
    );
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Symbol("@main".into())
    );
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other('('));
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other(')'));
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other(':'));
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Keyword(Keyword::I32)
    );
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other('{'));
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Symbol("%entry".into())
    );
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other(':'));
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Symbol("%ret".into())
    );
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other('='));
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Keyword(Keyword::Alloc)
    );
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Keyword(Keyword::I32)
    );
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Keyword(Keyword::Store)
    );
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Int(0));
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other(','));
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Symbol("%ret".into())
    );
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Symbol("%0".into())
    );
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other('='));
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Keyword(Keyword::Load)
    );
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Symbol("%ret".into())
    );
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Symbol("%1".into())
    );
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other('='));
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::BinaryOp(BinaryOp::Add)
    );
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Symbol("%0".into())
    );
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other(','));
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Int(1));
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Keyword(Keyword::Ret)
    );
    assert_eq!(
      lexer.next_token().unwrap().kind,
      TokenKind::Symbol("%1".into())
    );
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Other('}'));
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::End);
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::End);
    assert_eq!(lexer.next_token().unwrap().kind, TokenKind::End);
  }
}
