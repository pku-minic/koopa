use colored::*;
use std::cell::RefCell;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::result::Result;
use std::{default, fmt};

/// The type of error returned by logger methods of `Span`.
#[cfg(feature = "no-front-logger")]
pub type Error = String;

/// The type of error returned by logger methods of `Span`.
#[cfg(not(feature = "no-front-logger"))]
pub type Error = ();

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
  #[cfg(feature = "no-front-logger")]
  pub fn log_raw_error<T>(message: &str) -> Result<T, Error> {
    // update error number
    Self::STATE.with(|gs| gs.borrow_mut().err_num += 1);
    Err(message.into())
  }

  /// Logs error with no span provided.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_raw_error<T>(message: &str) -> Result<T, Error> {
    Self::STATE.with(|gs| {
      // update error number
      gs.borrow_mut().err_num += 1;
      // print message to stderr
      eprintln!("{}: {}", "error".bright_red(), message);
    });
    Err(())
  }

  /// Logs warning with no span provided.
  #[cfg(feature = "no-front-logger")]
  pub fn log_raw_warning(_: &str) {
    // update warning number
    Self::STATE.with(|gs| gs.borrow_mut().warn_num += 1);
  }

  /// Logs warning with no span provided.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_raw_warning(message: &str) {
    Self::STATE.with(|gs| {
      // update warning number
      gs.borrow_mut().warn_num += 1;
      // print message to stderr
      eprintln!("{}: {}", "warning".yellow(), message);
    });
  }

  /// Logs global information (total error/warning number).
  #[cfg(feature = "no-front-logger")]
  pub fn log_global() {}

  /// Logs global information (total error/warning number).
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_global() {
    Self::STATE.with(|gs| {
      let gs = gs.borrow();
      // error info
      if gs.err_num != 0 {
        eprint!("{} {}", gs.err_num, "error".bright_red());
        if gs.err_num > 1 {
          eprint!("{}", "s".bright_red());
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
          eprint!("{}", "s".yellow());
        }
      }
      // ending
      eprintln!(" emitted");
    });
  }

  /// Checks if there are some errors.
  pub fn has_error() -> bool {
    Self::STATE.with(|gs| gs.borrow().err_num != 0)
  }

  /// Logs error message.
  #[cfg(feature = "no-front-logger")]
  pub fn log_error<T>(&self, message: &str) -> Result<T, Error> {
    Self::log_raw_error::<()>(message).unwrap_err();
    Err(message.into())
  }

  /// Logs error message.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_error<T>(&self, message: &str) -> Result<T, Error> {
    Self::log_raw_error::<()>(message).unwrap_err();
    Self::STATE.with(|gs| self.print_file_info(&gs.borrow().file, Color::BrightRed));
    Err(())
  }

  /// Logs warning message.
  #[cfg(feature = "no-front-logger")]
  pub fn log_warning(&self, message: &str) {
    Self::log_raw_warning(message);
  }

  /// Logs warning message.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_warning(&self, message: &str) {
    Self::log_raw_warning(message);
    Self::STATE.with(|gs| self.print_file_info(&gs.borrow().file, Color::Yellow));
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

  /// Checks if the current span is in the same line as the specific span.
  pub fn is_in_same_line_as(&self, span: &Span) -> bool {
    self.end.line == span.start.line
  }

  /// Prints file information.
  #[cfg(not(feature = "no-front-logger"))]
  fn print_file_info(&self, file: &FileType, color: Color) {
    eprintln!("  {} {}:{}", "at".blue(), file, self.start);
    if let FileType::File(path) = file {
      // open file and get lines
      let mut lines = BufReader::new(File::open(path).unwrap()).lines();
      if self.start.line == self.end.line {
        // get some parameters
        let width = ((self.start.line + 1) as f32).log10().ceil() as usize;
        let leading = self.start.col as usize - 1;
        let len = (self.end.col - self.start.col) as usize + 1;
        // print the current line to stderr
        let line_num = self.start.line as usize;
        let line = lines.nth(line_num - 1).unwrap().unwrap();
        eprintln!("{:w$} {}", "", "|".blue(), w = width);
        eprintln!("{:w$} {} {}", line_num, "|".blue(), line, w = width);
        eprint!("{:w$} {} {:l$}", "", "|".blue(), "", w = width, l = leading);
        eprintln!("{}", format!("{:^>w$}", "", w = len).color(color));
      } else {
        // get some parameters
        let width = ((self.end.line + 1) as f32).log10().ceil() as usize;
        let start = self.start.col as usize;
        let end = self.end.col as usize;
        // print the first line to stderr
        let line_num = self.start.line as usize;
        let mut lines = lines.skip(line_num - 1);
        let line = lines.next().unwrap().unwrap();
        eprintln!("{:w$} {}", "", "|".blue(), w = width);
        eprintln!("{:w$} {}   {}", line_num, "|".blue(), line, w = width);
        eprint!("{:w$} {}  ", "", "|".blue(), w = width);
        eprintln!("{}", format!("{:_>w$}^", "", w = start).color(color));
        // print the middle lines to stderr
        let mid_lines = (self.end.line - self.start.line) as usize - 1;
        if mid_lines <= 4 {
          for i in 0..mid_lines {
            let line = lines.next().unwrap().unwrap();
            eprint!("{:w$} {} ", line_num + i + 1, "|".blue(), w = width);
            eprintln!("{} {}", "|".color(color), line);
          }
        } else {
          for i in 0..2usize {
            let line = lines.next().unwrap().unwrap();
            eprint!("{:w$} {} ", line_num + i + 1, "|".blue(), w = width);
            eprintln!("{} {}", "|".color(color), line);
          }
          eprint!("{:.>w$} {} {}", "", "|".blue(), "|".color(color), w = width);
          let line = lines.nth(mid_lines - 3).unwrap().unwrap();
          eprintln!("{:w$} {} ", self.end.line - 1, "|".blue(), w = width);
          eprintln!("{} {}", "|".color(color), line);
        }
        // print the last line to stderr
        let line_num = self.end.line as usize;
        let line = lines.next().unwrap().unwrap();
        eprint!("{:w$} {} ", line_num, "|".blue(), w = width);
        eprintln!("{} {}", "|".color(color), line);
        eprint!("{:w$} {} {}", "", "|".blue(), "|".color(color), w = width);
        eprintln!("{}", format!("{:_>w$}^", "", w = end).color(color));
      }
    }
    eprintln!();
  }
}

impl default::Default for Span {
  fn default() -> Self {
    Self::new(Pos::default())
  }
}

impl fmt::Debug for Span {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}-{}", self.start, self.end)
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

impl default::Default for Pos {
  fn default() -> Self {
    Self::new()
  }
}

impl fmt::Display for Pos {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}:{}", self.line, self.col)
  }
}

/// Global state for `Span`.
struct GlobalState {
  file: FileType,
  err_num: usize,
  warn_num: usize,
}

/// Type of input file.
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

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn pos_update() {
    let mut pos = Pos::new();
    assert_eq!(format!("{}", pos), "1:1");
    pos.update_col();
    pos.update_col();
    assert_eq!(format!("{}", pos), "1:3");
    pos.update_line();
    assert_eq!(format!("{}", pos), "2:1");
    pos.update_line();
    pos.update_line();
    assert_eq!(format!("{}", pos), "4:1");
  }

  #[test]
  fn span_update() {
    let mut pos = Pos::new();
    let sp1 = Span::new(pos);
    pos.update_col();
    pos.update_col();
    let sp2 = sp1.update(pos);
    assert_eq!(sp1.is_in_same_line_as(&sp2), true);
    sp2.log_error::<()>("test error").unwrap_err();
    sp2.log_warning("test warning");
    sp2.log_warning("test warning 2");
    Span::log_global();
    assert_eq!(format!("{}", sp2.start), "1:1");
    assert_eq!(format!("{}", sp2.end), "1:3");
    let sp = Span::new(Pos { line: 10, col: 10 });
    let sp = sp.update(Pos { line: 10, col: 15 });
    assert_eq!(sp2.is_in_same_line_as(&sp), false);
    let sp3 = sp2.update_span(sp);
    assert_eq!(sp2.is_in_same_line_as(&sp3), true);
    assert_eq!(format!("{}", sp3.start), "1:1");
    assert_eq!(format!("{}", sp3.end), "10:15");
  }
}
