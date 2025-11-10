//! The frontend of text form Koopa IR.
//!
//! This module provides text form IR related implementations, including:
//!
//! * Tokens ([`token`]) and abstract syntax tree ([`ast`]) of Koopa IR.
//! * [`Span`](span::Span) struct for holding source code locations.
//! * Lexer ([`Lexer`](lexer::Lexer)), parser ([`Parser`](parser::Parser))
//!   and analyzer ([`Builder`](builder::Builder)) of Koopa IR.
//! * Koopa IR frontend driver ([`Driver`]).
//!
//! # Examples
//!
//! Convert text form Koopa IR program into the in-memory form:
//!
//! ```
//! use koopa::front::Driver;
//!
//! let driver: Driver<_> = r#"
//!   fun @fib(@n: i32): i32 {
//!   %entry:
//!     %cond = le @n, 2
//!     br %cond, %then, %else
//!   
//!   %then:
//!     ret 1
//!   
//!   %else:
//!     %0 = sub @n, 1
//!     %x = call @fib(%0)
//!     %1 = sub @n, 2
//!     %y = call @fib(%1)
//!     %ans = add %x, %y
//!     ret %ans
//!   }
//! "#.into();
//! let program = driver.generate_program().unwrap();
//! ```
//!
//! Build Koopa IR program from a text file:
//!
//! ```no_run
//! use koopa::front::Driver;
//!
//! # fn main() -> std::io::Result<()> {
//! let driver = Driver::from_path("/path/to/file")?;
//! let program = driver.generate_program().unwrap();
//! # Ok(())
//! # }
//! ```

pub mod ast;
pub mod builder;
pub mod driver;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;

pub use driver::Driver;
