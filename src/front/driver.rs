use crate::front::ast::AstKind;
use crate::front::builder::Builder;
use crate::front::lexer::Lexer;
use crate::front::parser::Parser;
use crate::front::span::{Error, FileType, Span};
use crate::ir::Program;
use crate::log_raw_error;
use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

/// A driver for converting text form Koopa IR to IR structures.
pub struct Driver<T: Read> {
  parser: Parser<T>,
  builder: Builder,
}

impl<T: Read> Driver<T> {
  /// Maximum number of errors allowed.
  const MAX_ERR_NUM: usize = 20;

  /// Creates a new driver.
  pub fn new(ft: FileType, reader: T) -> Self {
    Span::reset(ft);
    Self {
      parser: Parser::new(Lexer::new(reader)),
      builder: Builder::new(),
    }
  }

  /// Generates Koopa IR program from the reader.
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

impl Driver<File> {
  /// Creates a new driver from the specific path.
  pub fn from_path<P>(path: P) -> io::Result<Self>
  where
    P: AsRef<Path> + Clone,
  {
    File::open(path.clone()).map(|f| Driver::new(FileType::File(path.as_ref().to_path_buf()), f))
  }
}

impl From<io::Stdin> for Driver<io::Stdin> {
  /// Creates a new driver from the standard input.
  fn from(stdin: io::Stdin) -> Self {
    Driver::new(FileType::Stdin, stdin)
  }
}

impl From<String> for Driver<io::Cursor<String>> {
  /// Creates a new driver from the given [`String`].
  fn from(buf: String) -> Self {
    Driver::new(FileType::Buffer, io::Cursor::new(buf))
  }
}

impl<'a> From<&'a str> for Driver<io::Cursor<&'a str>> {
  /// Creates a new driver from the given [`&str`].
  fn from(buf: &'a str) -> Self {
    Driver::new(FileType::Buffer, io::Cursor::new(buf))
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::ir::{Type, ValueKind};

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
    for var in program.borrow_values().values() {
      assert_eq!(var.name(), &Some("@x".into()));
      assert_eq!(
        var.ty(),
        &Type::get_pointer(Type::get_array(Type::get_i32(), 10))
      );
      match var.kind() {
        ValueKind::GlobalAlloc(alloc) => {
          assert!(matches!(
            program.borrow_value(alloc.init()).kind(),
            ValueKind::ZeroInit(..)
          ));
        }
        _ => panic!(),
      }
    }
    for func in program.funcs().values() {
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

  #[test]
  fn generate_nested_loop() {
    let driver: Driver<_> = r#"
      decl @getint(): i32

      fun @main(): i32 {
      %args_0:
        %7 = call @getint()
        %8 = call @getint()
        jump %while_cond_2

      %while_end_1: //! preds: %while_cond_2
        ret %9

      %while_cond_2: //! preds: %args_0, %while_end_5
        %9 = phi i32 (0, %args_0), (%10, %while_end_5)
        %11 = phi i32 (0, %args_0), (%12, %while_end_5)
        %13 = lt %11, %8
        br %13, %while_body_3, %while_end_1

      %while_body_3: //! preds: %while_cond_2
        jump %while_cond_4

      %while_cond_4: //! preds: %while_body_3, %while_body_6
        %10 = phi i32 (%9, %while_body_3), (%14, %while_body_6)
        %15 = phi i32 (0, %while_body_3), (%16, %while_body_6)
        %17 = lt %15, %7
        br %17, %while_body_6, %while_end_5

      %while_end_5: //! preds: %while_cond_4
        %12 = add %11, 1
        jump %while_cond_2

      %while_body_6: //! preds: %while_cond_4
        %18 = add %10, %11
        %14 = add %18, %15
        %16 = add %15, 1
        jump %while_cond_4
      }
    "#
    .into();
    let _ = driver.generate_program().unwrap();
    assert_eq!(Span::error_num() + Span::warning_num(), 0);
  }
}
