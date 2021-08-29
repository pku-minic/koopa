use colored::*;
use std::cell::RefCell;
use std::fmt;
use std::result::Result;

/// A span.
///
/// Used to print error messages.
#[derive(Clone, Copy)]
pub struct Span {
  start: Pos,
  end: Pos,
}

impl Span {
  thread_local! {
    static STATE: RefCell<GlobalState> = RefCell::new(GlobalState {
      file: FileType::Buffer,
      err_num: 0,
      warn_num: 0,
    });
  }

  /// Creates a new span from `Pos`.
  pub fn new(start: Pos) -> Self {
    Self { start, end: start }
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

  /// Logs error with no span provided.
  pub fn log_raw_error(message: &str) {
    Self::STATE.with(|gs| {
      // update error number
      let mut gs = gs.borrow_mut();
      gs.err_num += 1;
      // print message to stderr
      eprintln!("{}: {}", "error".red(), message);
    });
  }

  /// Logs warning with no span provided.
  pub fn log_raw_warning(message: &str) {
    Self::STATE.with(|gs| {
      // update warning number
      let mut gs = gs.borrow_mut();
      gs.warn_num += 1;
      // print message to stderr
      eprintln!("{}: {}", "warning".yellow(), message);
    });
  }

  /// Logs global information (total error/warning number).
  pub fn log_global() {
    Self::STATE.with(|gs| {
      let gs = gs.borrow();
      // error info
      if gs.err_num != 0 {
        eprint!("{} {}", gs.err_num, "error".red());
        if gs.err_num > 1 {
          eprint!("{}", "s".red());
        }
      }
      // seperator
      if gs.err_num != 0 && gs.warn_num != 0 {
        eprint!(" and ");
      }
      // warning info
      if gs.warn_num != 0 {
        eprint!("{} {}", gs.warn_num, "warning".yellow());
        if gs.warn_num > 1 {
          eprint!("{}", "s".red());
        }
      }
      // ending
      eprintln!(" emitted");
    });
  }

  /// Logs error message.
  pub fn log_error<T>(&self, message: &str) -> Result<T, ()> {
    // TODO: rustc-like error message
    Self::log_raw_error(message);
    Self::STATE.with(|gs| {
      let file = &gs.borrow().file;
      eprintln!("   {} {}:{}", "at".blue().dimmed(), file, self.start);
    });
    Err(())
  }

  /// Logs warning message.
  pub fn log_warning<T>(&self, message: &str) -> Result<T, ()> {
    // TODO: rustc-like warning message
    Self::log_raw_warning(message);
    Self::STATE.with(|gs| {
      let file = &gs.borrow().file;
      eprintln!("     {} {}:{}", "at".blue().dimmed(), file, self.start);
    });
    Err(())
  }

  /// Consumes and then updates the end position.
  pub fn update(self, end: Pos) -> Self {
    Self {
      start: self.start,
      end,
    }
  }

  /// Consumes and then updates the ens position according to another span.
  pub fn update_span(self, span: Span) -> Self {
    Self {
      start: self.start,
      end: span.end,
    }
  }
}

/// Line-column mark.
#[derive(Clone, Copy)]
pub struct Pos {
  line: u32,
  col: u32,
}

impl Pos {
  /// Creates a new mark.
  pub fn new() -> Self {
    Self { line: 1, col: 1 }
  }

  /// Updates the line number and resets the column number.
  pub fn update_line(&mut self) {
    self.col = 1;
    self.line += 1;
  }

  /// Updates the column number.
  pub fn update_col(&mut self) {
    self.col += 1;
  }
}

impl fmt::Display for Pos {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      FileType::File(file) => f.write_str(file),
      FileType::Stdin => f.write_str("<stdin>"),
      FileType::Buffer => f.write_str("<buffer>"),
    }
  }
}

/// Global state for `Span`.
struct GlobalState {
  file: FileType,
  err_num: usize,
  warn_num: usize,
}
