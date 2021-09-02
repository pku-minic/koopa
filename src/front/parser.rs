use crate::front::ast::{self, AstBox};
use crate::front::lexer::Lexer;
use crate::front::span::{Error, Span};
use crate::front::token::{Keyword, Token, TokenKind};
use std::io::Read;

/// Parser of Koopa IR.
pub struct Parser<T: Read> {
  lexer: Lexer<T>,
  cur_token: Token,
}

/// Result returned by `Parser`
pub type Result = std::result::Result<AstBox, Error>;

/// Reads the value of the specific kind of token from lexer.
macro_rules! read {
  ($self:ident, $p:path, $prompt:expr) => {{
    let Token { span, kind } = &$self.cur_token;
    if let $p(v) = kind {
      let v = v.clone();
      $self.next_token()?;
      Ok(v)
    } else {
      span.log_error(&format!("expected {}, found {}", $prompt, kind))
    }
  }};
}

/// Performs token matching, and automatically recovers from errors.
macro_rules! match_token {
  {
    use $self:ident, $span:ident, $kind:ident;
    $($p:pat => $e:expr,)*
    ? => $default:expr,
  } => {{
    let ($span, $kind) = ($self.cur_token.span, &$self.cur_token.kind);
    let result = match $self.cur_token.kind {
      $($p => $e,)*
      _ => $default,
    };
    match &result {
      Err(e) if !e.is_fatal() => {
        let mut span = $span;
        while !matches!($self.cur_token.kind, $($p)|+) {
          match $self.next_token() {
            Err(e) if e.is_fatal() => return Err(e),
            _ => {}
          }
          span = span.update_span($self.cur_token.span);
        }
        Ok(ast::Error::new(span))
      }
      _ => result,
    }
  }};
}

impl<T: Read> Parser<T> {
  /// Creates a new `Parser` from the specific `Lexer`.
  pub fn new(lexer: Lexer<T>) -> Self {
    let mut parser = Self {
      lexer,
      cur_token: Token::default(),
    };
    parser.next_token().unwrap();
    parser
  }

  /// Parses the next AST.
  pub fn parse_next(&mut self) -> Result {
    match_token! {
      use self, span, kind;
      TokenKind::End => Ok(ast::End::new(span)),
      TokenKind::Keyword(Keyword::Global) => self.parse_global_def(),
      TokenKind::Keyword(Keyword::Fun) => self.parse_fun_def(),
      TokenKind::Keyword(Keyword::Decl) => self.parse_fun_decl(),
      ? => span.log_error(&format!(
        "expected global definition/declaration, found {}",
        kind
      )),
    }
  }

  /// Gets the next token.
  fn next_token(&mut self) -> std::result::Result<(), Error> {
    self.cur_token = self.lexer.next_token()?;
    Ok(())
  }

  /// Gets the current span.
  fn span(&self) -> Span {
    self.cur_token.span
  }

  /// Parses global symbol definitions.
  fn parse_global_def(&mut self) -> Result {
    let span = self.span();
    // eat 'global'
    self.next_token()?;
    // get symbol name
    let name = read!(self, TokenKind::Symbol, "symbol name")?;
    // check & eat '= alloc'
    self.expect(TokenKind::Other('='))?;
    let span_alloc = self.expect(TokenKind::Keyword(Keyword::Alloc))?;
    // get type
    let ty = self.parse_type()?;
    // check & eat ','
    self.expect(TokenKind::Other(','))?;
    // get initializer
    self.parse_init().map(|init| {
      let span_last = init.span;
      // create global memory declaration
      let value = ast::GlobalDecl::new(span_alloc.update_span(span_last), ty, init);
      // create global symbol definition
      ast::GlobalDef::new(span.update_span(span_last), name, value)
    })
  }

  /// Parses function definitions.
  fn parse_fun_def(&mut self) -> Result {
    let span = self.span();
    // eat 'fun'
    self.next_token()?;
    // get function name
    let name = read!(self, TokenKind::Symbol, "function name")?;
    // get parameters
    let (params, _) = self.parse_list(|s| {
      // get parameter name
      let name = read!(s, TokenKind::Symbol, "parameter name")?;
      // check & eat ':'
      s.expect(TokenKind::Other(':'))?;
      // get parameter type
      Ok((name, s.parse_type()?))
    })?;
    // get return type
    let mut ret = None;
    if self.is_token(TokenKind::Other(':')) {
      self.next_token()?;
      ret = Some(self.parse_type()?);
    }
    // check & eat '{'
    self.expect(TokenKind::Other('{'))?;
    // get basic blocks
    let mut bbs = Vec::new();
    while !self.is_token(TokenKind::Other('}')) {
      bbs.push(self.parse_block()?);
    }
    // eat '}'
    let span = span.update_span(self.span());
    self.next_token()?;
    // create function definition
    if bbs.is_empty() {
      span.log_error("expected at least one basic block in function definition")
    } else {
      Ok(ast::FunDef::new(span, name, params, ret, bbs))
    }
  }

  /// Parses function declarations.
  fn parse_fun_decl(&mut self) -> Result {
    let mut span = self.span();
    // eat 'fun'
    self.next_token()?;
    // get function name
    let name = read!(self, TokenKind::Symbol, "function name")?;
    // get parameters
    let (params, sp) = self.parse_list(|s| s.parse_type())?;
    span = span.update_span(sp);
    // get return type
    let mut ret = None;
    if self.is_token(TokenKind::Other(':')) {
      self.next_token()?;
      let ty = self.parse_type()?;
      span = span.update_span(ty.span);
      ret = Some(ty);
    }
    // create function declaration
    Ok(ast::FunDecl::new(span, name, params, ret))
  }

  /// Parses types.
  fn parse_type(&mut self) -> Result {
    let Token { span, kind } = &self.cur_token;
    match kind {
      TokenKind::Keyword(Keyword::I32) => self.parse_int_type(),
      TokenKind::Other('[') => self.parse_array_type(),
      TokenKind::Other('*') => self.parse_pointer_type(),
      TokenKind::Other('(') => self.parse_fun_type(),
      _ => span.log_error(&format!("expected type, found {}", kind)),
    }
  }

  /// Parses 32-bit integer types.
  fn parse_int_type(&mut self) -> Result {
    let span = self.span();
    self.next_token()?;
    Ok(ast::IntType::new(span))
  }

  /// Parses array types.
  fn parse_array_type(&mut self) -> Result {
    let span = self.span();
    // eat '['
    self.next_token()?;
    // get base type
    let base = self.parse_type()?;
    // check & eat ','
    self.expect(TokenKind::Other(','))?;
    // get length
    let len = read!(self, TokenKind::Int, "length")? as usize;
    // check & eat ']'
    let span = span.update_span(self.expect(TokenKind::Other(']'))?);
    Ok(ast::ArrayType::new(span, base, len))
  }

  /// Parses pointer types.
  fn parse_pointer_type(&mut self) -> Result {
    let span = self.span();
    // eat '*'
    self.next_token()?;
    // get base type
    self
      .parse_type()
      .map(|base| ast::PointerType::new(span.update_span(base.span), base))
  }

  /// Parses function types.
  fn parse_fun_type(&mut self) -> Result {
    let mut span = self.span();
    // get parameter type list
    let (params, sp) = self.parse_list(|s| s.parse_type())?;
    span = span.update_span(sp);
    // get return type
    let mut ret = None;
    if self.is_token(TokenKind::Other(':')) {
      self.next_token()?;
      let ty = self.parse_type()?;
      span = span.update_span(ty.span);
      ret = Some(ty);
    }
    // create function type
    Ok(ast::FunType::new(span, params, ret))
  }

  /// Parses basic blocks.
  fn parse_block(&mut self) -> Result {
    let span = self.span();
    // get block name
    let name = read!(self, TokenKind::Symbol, "basic block name")?;
    // check & eat ':'
    self.expect(TokenKind::Other(':'))?;
    // get statements
    let mut stmts = Vec::new();
    let mut exit_flag = false;
    while !exit_flag {
      stmts.push(match_token! {
        use self, span, kind;
        TokenKind::Symbol(_) => self.parse_symbol_def(),
        TokenKind::Keyword(Keyword::Store) => self.parse_store(),
        TokenKind::Keyword(Keyword::Call) => self.parse_fun_call(),
        TokenKind::Keyword(Keyword::Br) => { exit_flag = true; self.parse_branch() },
        TokenKind::Keyword(Keyword::Jump) => { exit_flag = true; self.parse_jump() },
        TokenKind::Keyword(Keyword::Ret) => { exit_flag = true; self.parse_return() },
        ? => span.log_error(&format!("expected statement, found {}", kind)),
      }?);
    }
    // create basic block
    Ok(ast::Block::new(
      span.update_span(stmts.last().unwrap().span),
      name,
      stmts,
    ))
  }

  /// Parses local symbol definitions.
  fn parse_symbol_def(&mut self) -> Result {
    let span = self.span();
    // get symbol name
    let name = read!(self, TokenKind::Symbol, "symbol name")?;
    // check & eat '='
    self.expect(TokenKind::Other('='))?;
    // get value
    let Token { span: sp, kind } = &self.cur_token;
    match kind {
      TokenKind::Keyword(Keyword::Alloc) => self.parse_mem_decl(),
      TokenKind::Keyword(Keyword::Load) => self.parse_load(),
      TokenKind::Keyword(Keyword::GetPtr) => self.parse_get_pointer(),
      TokenKind::BinaryOp(_) => self.parse_binary_expr(),
      TokenKind::UnaryOp(_) => self.parse_unary_expr(),
      TokenKind::Keyword(Keyword::Call) => self.parse_fun_call(),
      TokenKind::Keyword(Keyword::Phi) => self.parse_phi(),
      _ => sp.log_error(&format!("expected expression, found {}", kind)),
    }
    .map(|value| ast::SymbolDef::new(span.update_span(value.span), name, value))
  }

  /// Parses memory declarations.
  fn parse_mem_decl(&mut self) -> Result {
    let span = self.span();
    // eat 'alloc'
    self.next_token()?;
    // get type
    self
      .parse_type()
      .map(|ty| ast::MemDecl::new(span.update_span(ty.span), ty))
  }

  /// Parses loads.
  fn parse_load(&mut self) -> Result {
    let span = self.span();
    // eat 'load'
    self.next_token()?;
    // get symbol name
    let span = span.update_span(self.span());
    read!(self, TokenKind::Symbol, "symbol").map(|symbol| ast::Load::new(span, symbol))
  }

  /// Parses stores.
  fn parse_store(&mut self) -> Result {
    let span = self.span();
    // eat 'store'
    self.next_token()?;
    // get value
    let value = if let Token {
      span,
      kind: TokenKind::Symbol(symbol),
    } = &self.cur_token
    {
      ast::SymbolRef::new(*span, symbol.clone())
    } else {
      self.parse_init()?
    };
    // check & eat ','
    self.expect(TokenKind::Other(','))?;
    // get symbol name
    let span = span.update_span(self.span());
    read!(self, TokenKind::Symbol, "symbol").map(|symbol| ast::Store::new(span, value, symbol))
  }

  /// Parses pointer calculations.
  fn parse_get_pointer(&mut self) -> Result {
    let mut span = self.span();
    // eat 'getptr'
    self.next_token()?;
    // get symbol name
    let symbol = read!(self, TokenKind::Symbol, "symbol")?;
    // check & eat ','
    self.expect(TokenKind::Other(','))?;
    // get value
    let value = self.parse_value()?;
    span = span.update_span(value.span);
    // get step
    let mut step = None;
    if self.is_token(TokenKind::Other(',')) {
      self.next_token()?;
      span = span.update_span(self.span());
      step = Some(read!(self, TokenKind::Int, "step")? as i32);
    }
    // create get pointer
    Ok(ast::GetPointer::new(span, symbol, value, step))
  }

  /// Parses binary expressions.
  fn parse_binary_expr(&mut self) -> Result {
    let span = self.span();
    // get operator
    let op = read!(self, TokenKind::BinaryOp, "binary operator")?;
    // get lhs & rhs
    let lhs = self.parse_value()?;
    self.expect(TokenKind::Other(','))?;
    self
      .parse_value()
      .map(|rhs| ast::BinaryExpr::new(span.update_span(rhs.span), op, lhs, rhs))
  }

  /// Parses unary expressions.
  fn parse_unary_expr(&mut self) -> Result {
    let span = self.span();
    // get operator
    let op = read!(self, TokenKind::UnaryOp, "unary operator")?;
    // get operand
    self
      .parse_value()
      .map(|opr| ast::UnaryExpr::new(span.update_span(opr.span), op, opr))
  }

  /// Parses branches.
  fn parse_branch(&mut self) -> Result {
    let span = self.span();
    // eat 'branch'
    self.next_token()?;
    // get condition
    let cond = self.parse_value()?;
    // check & eat ','
    self.expect(TokenKind::Other(','))?;
    // get true target basic block
    let tbb = read!(self, TokenKind::Symbol, "basic block name")?;
    // check & eat ','
    self.expect(TokenKind::Other(','))?;
    // get false target basic block
    let span = span.update_span(self.span());
    read!(self, TokenKind::Symbol, "basic block name")
      .map(|fbb| ast::Branch::new(span, cond, tbb, fbb))
  }

  /// Parses jumps.
  fn parse_jump(&mut self) -> Result {
    let span = self.span();
    // eat 'jump'
    self.next_token()?;
    // get symbol
    let span = span.update_span(self.span());
    read!(self, TokenKind::Symbol, "basic block name").map(|target| ast::Jump::new(span, target))
  }

  /// Parses function calls.
  fn parse_fun_call(&mut self) -> Result {
    let span = self.span();
    // eat 'call'
    self.next_token()?;
    // get function name
    let fun = read!(self, TokenKind::Symbol, "function name")?;
    // get arguments
    let (args, sp) = self.parse_list(|s| s.parse_value())?;
    // create function call
    Ok(ast::FunCall::new(span.update_span(sp), fun, args))
  }

  /// Parses returns.
  fn parse_return(&mut self) -> Result {
    let mut span = self.span();
    // eat 'ret'
    self.next_token()?;
    // get value
    let mut value = None;
    if span.is_in_same_line_as(&self.span()) {
      let val = self.parse_value()?;
      span = span.update_span(val.span);
      value = Some(val);
    }
    // create function call
    Ok(ast::Return::new(span, value))
  }

  /// Parses phi functions.
  fn parse_phi(&mut self) -> Result {
    let mut span = self.span();
    // eat 'phi'
    self.next_token()?;
    // get the first operand
    let (first, sp) = self.parse_phi_opr()?;
    span = span.update_span(sp);
    let mut oprs = vec![first];
    // get the rest operands
    while self.is_token(TokenKind::Other(',')) {
      self.next_token()?;
      let (opr, sp) = self.parse_phi_opr()?;
      oprs.push(opr);
      span = span.update_span(sp);
    }
    // create phi function
    Ok(ast::Phi::new(span, oprs))
  }

  /// Parses phi operands.
  fn parse_phi_opr(&mut self) -> std::result::Result<((AstBox, String), Span), Error> {
    let span = self.span();
    // check & eat '('
    self.expect(TokenKind::Other('('))?;
    // get value
    let value = self.parse_value()?;
    // check & eat ','
    self.expect(TokenKind::Other(','))?;
    // get symbol name
    let symbol = read!(self, TokenKind::Symbol, "symbol")?;
    Ok((
      (value, symbol),
      span.update_span(self.expect(TokenKind::Other(')'))?),
    ))
  }

  /// Parses values.
  fn parse_value(&mut self) -> Result {
    let Token { span, kind } = &self.cur_token;
    let ret = match kind {
      // symbol reference
      TokenKind::Symbol(s) => ast::SymbolRef::new(*span, s.clone()),
      // integer literal
      TokenKind::Int(i) => ast::IntVal::new(*span, *i as i32),
      // undefined value
      TokenKind::Keyword(Keyword::Undef) => ast::UndefVal::new(*span),
      // unknown
      _ => span.log_error(&format!("expected value, found {}", kind))?,
    };
    self.next_token()?;
    Ok(ret)
  }

  /// Parses initializers.
  fn parse_init(&mut self) -> Result {
    let Token { span, kind } = &self.cur_token;
    match kind {
      // integer literal
      TokenKind::Int(i) => {
        let ast = ast::IntVal::new(*span, *i as i32);
        self.next_token()?;
        Ok(ast)
      }
      // undefined value
      TokenKind::Keyword(Keyword::Undef) => {
        let ast = ast::UndefVal::new(*span);
        self.next_token()?;
        Ok(ast)
      }
      // zero initializer
      TokenKind::Keyword(Keyword::ZeroInit) => {
        let ast = ast::ZeroInit::new(*span);
        self.next_token()?;
        Ok(ast)
      }
      // aggregate
      TokenKind::Other('{') => self.parse_aggregate(),
      // unknown
      _ => span.log_error(&format!("expected initializer, found {}", kind)),
    }
  }

  /// Parses aggregates.
  fn parse_aggregate(&mut self) -> Result {
    let span = self.span();
    // eat '{'
    self.expect(TokenKind::Other('{'))?;
    // get elements
    let mut elems = vec![self.parse_init()?];
    while self.is_token(TokenKind::Other(',')) {
      self.next_token()?;
      elems.push(self.parse_init()?);
    }
    // check & eat '}'
    Ok(ast::Aggregate::new(
      span.update_span(self.expect(TokenKind::Other('}'))?),
      elems,
    ))
  }

  /// Parses comma-seperated lists.
  fn parse_list<F, U>(&mut self, parser: F) -> std::result::Result<(Vec<U>, Span), Error>
  where
    F: Fn(&mut Self) -> std::result::Result<U, Error>,
  {
    // check & eat left bracket
    self.expect(TokenKind::Other('('))?;
    // get items
    let mut items = Vec::new();
    if !self.is_token(TokenKind::Other(')')) {
      loop {
        // get item
        items.push(parser(self)?);
        // eat ','
        if !self.is_token(TokenKind::Other(',')) {
          break;
        }
        self.next_token()?;
      }
    }
    // check & eat ')'
    Ok((items, self.expect(TokenKind::Other(')'))?))
  }

  /// Checks if the current token is the specific token.
  fn is_token(&self, tk: TokenKind) -> bool {
    self.cur_token.kind == tk
  }

  /// Expects the specific token from lexer.
  fn expect(&mut self, tk: TokenKind) -> std::result::Result<Span, Error> {
    let Token { span, kind } = &self.cur_token;
    if kind == &tk {
      let span = *span;
      self.next_token()?;
      Ok(span)
    } else {
      span.log_error(&format!("expected {}, found {}", tk, kind))
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::ir::instructions::BinaryOp;
  use std::io::Cursor;

  macro_rules! new_ast {
    ($name:ident { $($field:ident: $value:expr),+ $(,)? }) => {
      ast::$name::new(Span::default(), $($value),+)
    };
    ($name:ident) => {
      ast::$name::new(Span::default())
    };
  }

  #[test]
  fn parse_string() {
    let mut parser = Parser::new(Lexer::new(Cursor::new(
      r#"
      global @x = alloc [i32, 10], zeroinit

      fun @test(@i: i32): i32 {
      %entry:
        %0 = getptr @x, 2
        store -1, %0
        %1 = getptr @x, @i, 4
        %2 = load %1
        %3 = mul %2, 7
        ret %3
      }
      "#,
    )));
    let ast = parser.parse_next().unwrap();
    let expected = new_ast!(GlobalDef {
      name: "@x".into(),
      value: new_ast!(GlobalDecl {
        ty: new_ast!(ArrayType {
          base: new_ast!(IntType),
          len: 10,
        }),
        init: new_ast!(ZeroInit),
      }),
    });
    assert_eq!(ast, expected);
    let ast = parser.parse_next().unwrap();
    let expected = new_ast!(FunDef {
      name: "@test".into(),
      params: vec![("@i".into(), new_ast!(IntType))],
      ret: Some(new_ast!(IntType)),
      bbs: vec![new_ast!(Block {
        name: "%entry".into(),
        stmts: vec![
          new_ast!(SymbolDef {
            name: "%0".into(),
            value: new_ast!(GetPointer {
              symbol: "@x".into(),
              value: new_ast!(IntVal { value: 2 }),
              step: None,
            }),
          }),
          new_ast!(Store {
            value: new_ast!(IntVal { value: -1 }),
            symbol: "%0".into(),
          }),
          new_ast!(SymbolDef {
            name: "%1".into(),
            value: new_ast!(GetPointer {
              symbol: "@x".into(),
              value: new_ast!(SymbolRef {
                symbol: "@i".into(),
              }),
              step: Some(4),
            }),
          }),
          new_ast!(SymbolDef {
            name: "%2".into(),
            value: new_ast!(Load {
              symbol: "%1".into(),
            }),
          }),
          new_ast!(SymbolDef {
            name: "%3".into(),
            value: new_ast!(BinaryExpr {
              op: BinaryOp::Mul,
              lhs: new_ast!(SymbolRef {
                symbol: "%2".into(),
              }),
              rhs: new_ast!(IntVal { value: 7 }),
            }),
          }),
          new_ast!(Return {
            value: Some(new_ast!(SymbolRef {
              symbol: "%3".into(),
            })),
          }),
        ],
      })],
    });
    assert_eq!(ast, expected);
    let ast = parser.parse_next().unwrap();
    let expected = new_ast!(End);
    assert_eq!(ast, expected);
    let ast = parser.parse_next().unwrap();
    let expected = new_ast!(End);
    assert_eq!(ast, expected);
  }

  #[test]
  fn parse_error() {
    let mut parser = Parser::new(Lexer::new(Cursor::new(
      r#"
      global @x = alloc [i32, 10, zeroinit

      fun @test(@i: i32): i32 {
      %entry:
        %0 = getptr @x, 2
        store -1, %
        %1 = getptr @x, @i, 4
        %2 = load %1
        %3 = mul , 7
        ret %3
      }
      "#,
    )));
    assert_eq!(parser.parse_next().unwrap(), new_ast!(Error));
    let ast = parser.parse_next().unwrap();
    let expected = new_ast!(FunDef {
      name: "@test".into(),
      params: vec![("@i".into(), new_ast!(IntType))],
      ret: Some(new_ast!(IntType)),
      bbs: vec![new_ast!(Block {
        name: "%entry".into(),
        stmts: vec![
          new_ast!(SymbolDef {
            name: "%0".into(),
            value: new_ast!(GetPointer {
              symbol: "@x".into(),
              value: new_ast!(IntVal { value: 2 }),
              step: None,
            }),
          }),
          new_ast!(Error),
          new_ast!(SymbolDef {
            name: "%1".into(),
            value: new_ast!(GetPointer {
              symbol: "@x".into(),
              value: new_ast!(SymbolRef {
                symbol: "@i".into(),
              }),
              step: Some(4),
            }),
          }),
          new_ast!(SymbolDef {
            name: "%2".into(),
            value: new_ast!(Load {
              symbol: "%1".into(),
            }),
          }),
          new_ast!(Error),
          new_ast!(Return {
            value: Some(new_ast!(SymbolRef {
              symbol: "%3".into(),
            })),
          }),
        ],
      })],
    });
    assert_eq!(ast, expected);
    assert_eq!(parser.parse_next().unwrap(), new_ast!(End));
    assert_eq!(parser.parse_next().unwrap(), new_ast!(End));
  }
}
