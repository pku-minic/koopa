use crate::front::ast::AstKind;
use crate::front::builder::Builder;
use crate::front::lexer::Lexer;
use crate::front::parser::Parser;
use crate::front::span::{Error, FileType, Span};
use crate::ir::structs::Program;
use crate::log_raw_error;
use std::fs::File;
use std::io::{self, Read};

/// Driver can convert IR in string form to structures.
pub struct Driver<T: Read> {
  parser: Parser<T>,
  builder: Builder,
}

impl<T: Read> Driver<T> {
  /// Maximum number of errors allowed.
  const MAX_ERR_NUM: usize = 20;
  /// Creates a new `Driver`.
  pub fn new(ft: FileType, reader: T) -> Self {
    Span::reset(ft);
    Self {
      parser: Parser::new(Lexer::new(reader)),
      builder: Builder::new(),
    }
  }

  /// Creates a new `Driver` from the specific path.
  pub fn from_file(path: String) -> io::Result<Driver<File>> {
    File::open(&path).map(|f| Driver::new(FileType::File(path), f))
  }

  /// Generates IR program.
  pub fn generate_program(mut self) -> Result<Program, Error> {
    loop {
      // parse & get the next AST
      let ast = self.parser.parse_next()?;
      // check if is end of file
      if matches!(ast.kind, AstKind::End(_)) {
        break;
      }
      // build on the current AST
      self.builder.build_on(&ast);
      // exit if too many errors are generated
      if Span::error_num() > Self::MAX_ERR_NUM {
        return log_raw_error!("too many errors are generated, aborted").into();
      }
    }
    // log global information
    if Span::error_num() + Span::warning_num() != 0 {
      Span::log_global();
    }
    // exit if any errors are generated
    if Span::error_num() != 0 {
      Error::default().into()
    } else {
      Ok(self.builder.program())
    }
  }
}

/// Creates `Driver` from standard input.
impl From<io::Stdin> for Driver<io::Stdin> {
  fn from(stdin: io::Stdin) -> Self {
    Driver::new(FileType::Stdin, stdin)
  }
}

/// Creates `Driver` from `String`s.
impl From<String> for Driver<io::Cursor<String>> {
  fn from(buf: String) -> Self {
    Driver::new(FileType::Buffer, io::Cursor::new(buf))
  }
}

/// Creates `Driver` from strings.
impl<'a> From<&'a str> for Driver<io::Cursor<&'a str>> {
  fn from(buf: &'a str) -> Self {
    Driver::new(FileType::Buffer, io::Cursor::new(buf))
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::ir::core::ValueKind;
  use crate::ir::types::Type;

  #[test]
  fn generate_ir() {
    let driver: Driver<_> = r#"
      global @x = alloc [i32, 10], zeroinit

      fun @test(@i: i32): i32 {
      %entry:
        %0 = getptr @x, 0
        store {1, 2, 3, 4, 5, 0, 0, 0, 0, 10}, %0
        %1 = getelemptr @x, @i
        %2 = load %1
        %3 = mul %2, 7
        ret %3
      }
    "#
    .into();
    let program = driver.generate_program().unwrap();
    assert_eq!(Span::error_num() + Span::warning_num(), 0);
    for var in program.vars() {
      assert_eq!(var.borrow().name(), &Some("@x".into()));
      assert_eq!(
        var.ty(),
        &Type::get_pointer(Type::get_array(Type::get_i32(), 10))
      );
      match var.kind() {
        ValueKind::GlobalAlloc(alloc) => {
          assert!(matches!(
            alloc.init().value().unwrap().kind(),
            ValueKind::ZeroInit(..)
          ));
        }
        _ => panic!(),
      }
    }
    for func in program.funcs() {
      assert_eq!(func.name(), "@test");
      assert_eq!(
        func.ty(),
        &Type::get_function(vec![Type::get_i32()], Type::get_i32())
      );
    }
  }

  #[test]
  fn generate_ir_phi() {
    let driver: Driver<_> = r#"
      //! version: 0.0.1

      decl @getint(): i32
      
      fun @main(): i32 {
      %entry:
        %ans_0 = call @getint()
        jump %while_entry
      
      %while_entry: //! pred: %entry, %while_body
        %ind_var_0 = phi i32 (0, %entry), (%ind_var_1, %while_body)
        %ans_1 = phi i32 (%ans_0, %entry), (%ans_2, %while_body)
        %cond = lt %ind_var_0, 10
        br %cond, %while_body, %while_end
      
      %while_body: //! pred: %while_entry
        %ans_2 = add %ans_1, %ind_var_0
        %ind_var_1 = add %ind_var_0, 1
        jump %while_entry
      
      %while_end: //! pred: %while_entry
        ret %ans_1
      }
    "#
    .into();
    let _ = driver.generate_program().unwrap();
    assert_eq!(Span::error_num() + Span::warning_num(), 0);
  }
}
