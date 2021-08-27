use colored::*;
use std::cell::RefCell;
use std::fmt;

/// A span.
///
/// Used to print error messages.
pub struct Span {
  from: Mark,
  to: Mark,
}

impl Span {
  thread_local! {
    static STATE: RefCell<GlobalState> = RefCell::new(GlobalState {
      file: FileType::Buffer,
      err_num: 0,
      warn_num: 0,
    });
  }

  /// Resets the global state.
  pub fn reset(file: FileType) {
    Self::STATE.with(|gs| {
      *gs.borrow_mut() = GlobalState {
        file,
        err_num: 0,
        warn_num: 0,
      }
    });
  }

  /// Creates a new span from `Mark`.
  pub fn new(from: Mark, to: Mark) -> Self {
    Self { from, to }
  }

  /// Logs error message.
  pub fn log_error(&self, message: &str) {
    // TODO: rustc-like error message
    Self::STATE.with(|gs| {
      let gs = gs.borrow();
      eprintln!("{}: {}", "error".red(), message);
      eprintln!("   {} {}:{}", "at".blue().dimmed(), gs.file, self.from);
    });
  }

  /// Logs warning message.
  pub fn log_warning(&self, message: &str) {
    // TODO: rustc-like warning message
    Self::STATE.with(|gs| {
      let gs = gs.borrow();
      eprintln!("{}: {}", "warning".red(), message);
      eprintln!("     {} {}:{}", "at".blue().dimmed(), gs.file, self.from);
    });
  }

  /// Consumes and then updates the `to` mark.
  pub fn update(self, to: Mark) -> Self {
    self.to = to;
    self
  }

  /// Consumes and then updates the `to` mark according to another span.
  pub fn update_span(self, span: Span) -> Self {
    self.to = span.to;
    self
  }
}

/// Line-column mark.
#[derive(Clone, Copy)]
pub struct Mark {
  line: u32,
  col: u32,
}

impl Mark {
  /// Creates a new mark.
  pub fn new() -> Self {
    Self { line: 1, col: 1 }
  }

  /// Increases the line number and resets the column number.
  pub fn increase_line(&mut self) {
    self.col = 1;
    self.line += 1;
  }

  /// Increases the column number.
  pub fn increase_col(&mut self) {
    self.col += 1;
  }
}

impl fmt::Display for Mark {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}:{}", self.line, self.col)
  }
}

/// Type of input file.
#[derive(Debug, PartialEq)]
pub enum FileType {
  File(String),
  Stdin,
  Buffer,
}

impl fmt::Display for FileType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      FileType::File(file) => f.write_str(file),
      FileType::Stdin => f.write_str("stdin"),
      FileType::Buffer => f.write_str("buffer"),
    }
  }
}

/// Global state for `Span`.
struct GlobalState {
  file: FileType,
  err_num: usize,
  warn_num: usize,
}
