//! Span ([`Span`]) and error ([`Error`]) related implementations.

use std::cell::RefCell;
use std::fmt::{self, Arguments};
use std::path::PathBuf;

#[cfg(not(feature = "no-front-logger"))]
use colored::*;
#[cfg(not(feature = "no-front-logger"))]
use std::{fs::File, io::BufRead, io::BufReader, io::Result as IoResult};

/// The type of error returned by logger methods of [`Span`].
#[cfg(feature = "no-front-logger")]
#[derive(Debug)]
pub enum Error {
  /// Normal error.
  Normal(String),
  /// Fatal error.
  Fatal(String),
}

/// The type of error returned by logger methods of [`Span`].
#[cfg(not(feature = "no-front-logger"))]
#[derive(Debug)]
pub enum Error {
  /// Normal error.
  Normal,
  /// Fatal error.
  Fatal,
}

impl Error {
  /// Returns `true` if the current error is fatal.
  #[cfg(feature = "no-front-logger")]
  pub fn is_fatal(&self) -> bool {
    matches!(self, Error::Fatal(..))
  }

  /// Returns `true` if the current error is fatal.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn is_fatal(&self) -> bool {
    matches!(self, Error::Fatal)
  }
}

impl Default for Error {
  /// Creates a normal error.
  #[cfg(feature = "no-front-logger")]
  fn default() -> Self {
    Error::Normal(String::default())
  }

  /// Creates a normal error.
  #[cfg(not(feature = "no-front-logger"))]
  fn default() -> Self {
    Error::Normal
  }
}

impl<T> From<Error> for Result<T, Error> {
  /// Creates a result from the given error,
  /// which the value is always [`Err`].
  fn from(error: Error) -> Self {
    Err(error)
  }
}

/// A span that records source code locations.
///
/// Used to print error messages.
#[derive(Clone, Copy)]
pub struct Span {
  start: Pos,
  end: Pos,
}

/// Gets the string of the given line.
#[cfg(not(feature = "no-front-logger"))]
macro_rules! get_line_str {
  ($line:expr) => {
    $line
      .map_or("".into(), |r| r.unwrap())
      .replace('\t', &format!("{:w$}", "", w = Span::TAB_WIDTH))
  };
  ($line:expr, $col:expr) => {{
    let line = $line.map_or("".into(), |r| r.unwrap());
    let col = $col as usize;
    let tabs = (&line[..col]).matches('\t').count();
    (
      line.replace('\t', &format!("{:w$}", "", w = Span::TAB_WIDTH)),
      col + tabs * (Span::TAB_WIDTH - 1),
    )
  }};
  ($line:expr, $col1:expr, $col2:expr) => {{
    let line = $line.map_or("".into(), |r| r.unwrap());
    let col1 = $col1 as usize;
    let col2 = $col2 as usize;
    let tabs1 = (&line[..col1]).matches('\t').count();
    let tabs2 = tabs1 + (&line[col1..col2]).matches('\t').count();
    (
      line.replace('\t', &format!("{:w$}", "", w = Span::TAB_WIDTH)),
      col1 + tabs1 * (Span::TAB_WIDTH - 1),
      col2 + tabs2 * (Span::TAB_WIDTH - 1),
    )
  }};
}

impl Span {
  /// The column width occupied by the tab character.
  #[cfg(not(feature = "no-front-logger"))]
  const TAB_WIDTH: usize = 2;

  thread_local! {
    static STATE: RefCell<GlobalState> = RefCell::new(GlobalState {
      file: FileType::Buffer,
      err_num: 0,
      warn_num: 0,
    });
  }

  /// Creates a new span from [`Pos`].
  pub fn new(start: Pos) -> Self {
    Self { start, end: start }
  }

  /// Resets the global state in all spans.
  pub fn reset(file: FileType) {
    Self::STATE.with(|gs| {
      *gs.borrow_mut() = GlobalState {
        file,
        err_num: 0,
        warn_num: 0,
      }
    });
  }

  /// Logs normal error with no span provided.
  #[cfg(feature = "no-front-logger")]
  pub fn log_raw_error(args: Arguments) -> Error {
    // update error number
    Self::STATE.with(|gs| gs.borrow_mut().err_num += 1);
    Error::Normal(format!("{}", args))
  }

  /// Logs normal error with no span provided.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_raw_error(args: Arguments) -> Error {
    Self::STATE.with(|gs| {
      // update error number
      gs.borrow_mut().err_num += 1;
      // print message to stderr
      eprintln!("{}: {}", "error".bright_red(), args);
    });
    Error::Normal
  }

  /// Logs fatal error with no span provided.
  #[cfg(feature = "no-front-logger")]
  pub fn log_raw_fatal_error(args: Arguments) -> Error {
    // update error number
    Self::STATE.with(|gs| gs.borrow_mut().err_num += 1);
    Error::Fatal(format!("{}", args))
  }

  /// Logs fatal error with no span provided.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_raw_fatal_error(args: Arguments) -> Error {
    Self::STATE.with(|gs| {
      // update error number
      gs.borrow_mut().err_num += 1;
      // print message to stderr
      eprintln!("{}: {}", "error".bright_red(), args);
    });
    Error::Fatal
  }

  /// Logs warning with no span provided.
  #[cfg(feature = "no-front-logger")]
  pub fn log_raw_warning(_: Arguments) {
    // update warning number
    Self::STATE.with(|gs| gs.borrow_mut().warn_num += 1);
  }

  /// Logs warning with no span provided.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_raw_warning(args: Arguments) {
    Self::STATE.with(|gs| {
      // update warning number
      gs.borrow_mut().warn_num += 1;
      // print message to stderr
      eprintln!("{}: {}", "warning".yellow(), args);
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
      let mut msg = String::new();
      // error info
      if gs.err_num != 0 {
        msg += &format!("{} error", gs.err_num);
        if gs.err_num > 1 {
          msg += "s";
        }
      }
      // seperator
      if gs.err_num != 0 && gs.warn_num != 0 {
        msg += " and ";
      }
      // warning info
      if gs.warn_num != 0 {
        msg += &format!("{} warning", gs.warn_num);
        if gs.warn_num > 1 {
          msg += "s";
        }
      }
      // ending
      msg += " emitted";
      eprintln!("{}", msg.bold());
    });
  }

  /// Gets the number of errors.
  pub fn error_num() -> usize {
    Self::STATE.with(|gs| gs.borrow().err_num)
  }

  /// Gets the number of warnings.
  pub fn warning_num() -> usize {
    Self::STATE.with(|gs| gs.borrow().warn_num)
  }

  /// Logs normal error message.
  #[cfg(feature = "no-front-logger")]
  pub fn log_error(&self, args: Arguments) -> Error {
    Self::log_raw_error(args);
    Error::Normal(self.error_message(args))
  }

  /// Logs normal error message.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_error(&self, args: Arguments) -> Error {
    Self::log_raw_error(args);
    Self::STATE.with(|gs| self.print_file_info(&gs.borrow().file, Color::BrightRed));
    Error::Normal
  }

  /// Logs fatal error message.
  #[cfg(feature = "no-front-logger")]
  pub fn log_fatal_error(&self, args: Arguments) -> Error {
    Self::log_raw_error(args);
    Error::Fatal(self.error_message(args))
  }

  /// Logs fatal error message.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_fatal_error(&self, args: Arguments) -> Error {
    Self::log_raw_error(args);
    Self::STATE.with(|gs| self.print_file_info(&gs.borrow().file, Color::BrightRed));
    Error::Fatal
  }

  /// Logs warning message.
  #[cfg(feature = "no-front-logger")]
  pub fn log_warning(&self, args: Arguments) {
    Self::log_raw_warning(args);
  }

  /// Logs warning message.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_warning(&self, args: Arguments) {
    Self::log_raw_warning(args);
    Self::STATE.with(|gs| self.print_file_info(&gs.borrow().file, Color::Yellow));
  }

  /// Converts the current span into a new one
  /// where the end position has been updated.
  pub fn into_updated(self, end: Pos) -> Self {
    Self {
      start: self.start,
      end,
    }
  }

  /// Updates the end position.
  pub fn update(&mut self, end: Pos) {
    self.end = end;
  }

  /// Converts the current span into a new one where the end position
  /// has been updated according to another span.
  pub fn into_updated_span(self, span: Span) -> Self {
    Self {
      start: self.start,
      end: span.end,
    }
  }

  /// Updates the end position according to another span.
  pub fn update_span(&mut self, span: Span) {
    self.end = span.end;
  }

  /// Checks if the current span is in the same line as the given span.
  pub fn is_in_same_line_as(&self, span: &Span) -> bool {
    self.end.line == span.start.line
  }

  /// Returns the error message.
  #[cfg(feature = "no-front-logger")]
  fn error_message(&self, args: Arguments) -> String {
    Self::STATE.with(|gs| format!("{}:{}: {}", gs.borrow().file, self.start, args))
  }

  /// Prints the file information.
  #[cfg(not(feature = "no-front-logger"))]
  fn print_file_info(&self, file: &FileType, color: Color) {
    eprintln!("  {} {}:{}", "at".blue(), file, self.start);
    if self.start.col > 0 && self.end.col > 0 {
      if let FileType::File(path) = file {
        // open file and get lines
        let mut lines = BufReader::new(File::open(path).unwrap()).lines();
        if self.start.line == self.end.line {
          self.print_single_line_info(&mut lines, color);
        } else {
          self.print_multi_line_info(&mut lines, color);
        }
      }
    }
    eprintln!();
  }

  /// Prints the single line information.
  ///
  /// Used by method `print_file_info`.
  #[cfg(not(feature = "no-front-logger"))]
  fn print_single_line_info<T>(&self, lines: &mut T, color: Color)
  where
    T: Iterator<Item = IoResult<String>>,
  {
    // get some parameters
    let line_num = self.start.line as usize;
    let (line, c1, c2) = get_line_str!(lines.nth(line_num - 1), self.start.col, self.end.col);
    let width = ((line_num + 1) as f32).log10().ceil() as usize;
    let leading = c1 - 1;
    let len = c2 - c1 + 1;
    // print the current line to stderr
    eprintln!("{:w$} {}", "", "|".blue(), w = width);
    eprint!("{} ", format!("{:w$}", line_num, w = width).blue());
    eprintln!("{} {}", "|".blue(), line);
    eprint!("{:w$} {} {:l$}", "", "|".blue(), "", w = width, l = leading);
    eprintln!("{}", format!("{:^>w$}", "", w = len).color(color));
  }

  /// Prints the multi-line information.
  ///
  /// Used by method `print_file_info`.
  #[cfg(not(feature = "no-front-logger"))]
  fn print_multi_line_info<T>(&self, lines: &mut T, color: Color)
  where
    T: Iterator<Item = IoResult<String>>,
  {
    // get some parameters
    let width = ((self.end.line + 1) as f32).log10().ceil() as usize;
    // print the first line to stderr
    let line_num = self.start.line as usize;
    let mut lines = lines.skip(line_num - 1);
    let (line, start) = get_line_str!(lines.next(), self.start.col);
    eprintln!("{:w$} {}", "", "|".blue(), w = width);
    eprint!("{} ", format!("{:w$}", line_num, w = width).blue());
    eprintln!("{}   {}", "|".blue(), line);
    eprint!("{:w$} {}  ", "", "|".blue(), w = width);
    eprintln!("{}", format!("{:_>w$}^", "", w = start).color(color));
    // print the middle lines to stderr
    let mid_lines = (self.end.line - self.start.line) as usize - 1;
    if mid_lines <= 4 {
      for i in 0..mid_lines {
        let line = get_line_str!(lines.next());
        eprint!("{} ", format!("{:w$}", line_num + i + 1, w = width).blue());
        eprintln!("{} {} {}", "|".blue(), "|".color(color), line);
      }
    } else {
      for i in 0..2usize {
        let line = get_line_str!(lines.next());
        eprint!("{} ", format!("{:w$}", line_num + i + 1, w = width).blue());
        eprintln!("{} {} {}", "|".blue(), "|".color(color), line);
      }
      eprint!("{:.>w$} {} {}", "", "|".blue(), "|".color(color), w = width);
      let line = get_line_str!(lines.nth(mid_lines - 3));
      eprint!("{} ", format!("{:w$}", self.end.line - 1, w = width).blue());
      eprintln!("{} {} {}", "|".blue(), "|".color(color), line);
    }
    // print the last line to stderr
    let line_num = self.end.line as usize;
    let (line, end) = get_line_str!(lines.next(), self.end.col);
    eprint!("{} ", format!("{:w$}", line_num, w = width).blue());
    eprintln!("{} {} {}", "|".blue(), "|".color(color), line);
    eprint!("{:w$} {} {}", "", "|".blue(), "|".color(color), w = width);
    eprintln!("{}", format!("{:_>w$}^", "", w = end).color(color));
  }
}

impl Default for Span {
  /// Creates a span with the default source code locations.
  fn default() -> Self {
    Self::new(Pos::default())
  }
}

impl fmt::Debug for Span {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}-{}", self.start, self.end)
  }
}

/// A line-column mark.
#[derive(Clone, Copy)]
pub struct Pos {
  line: u32,
  col: u32,
}

impl Pos {
  /// Creates a new mark.
  pub fn new() -> Self {
    Self { line: 1, col: 0 }
  }

  /// Updates the line number ans column number based on the given character.
  pub fn update(&mut self, c: char) {
    match c {
      '\n' => {
        self.col = 0;
        self.line += 1;
      }
      _ => self.col += 1,
    }
  }
}

impl Default for Pos {
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
  /// File with a path.
  File(PathBuf),
  /// Standard input file.
  Stdin,
  /// A buffer in the memory.
  Buffer,
}

impl fmt::Display for FileType {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      FileType::File(path) => write!(f, "{}", path.display()),
      FileType::Stdin => f.write_str("<stdin>"),
      FileType::Buffer => f.write_str("<buffer>"),
    }
  }
}

/// Logs normal error with no span provided.
#[macro_export]
macro_rules! log_raw_error {
  ($($arg:tt)+) => {
    Span::log_raw_error(format_args!($($arg)+))
  };
}

/// Logs fatal error with no span provided.
#[macro_export]
macro_rules! log_raw_fatal_error {
  ($($arg:tt)+) => {
    Span::log_raw_fatal_error(format_args!($($arg)+))
  };
}

/// Logs warning with no span provided.
#[macro_export]
macro_rules! log_raw_warning {
  ($($arg:tt)+) => {
    Span::log_raw_warning(format_args!($($arg)+))
  };
}

/// Logs normal error message.
#[macro_export]
macro_rules! log_error {
  ($span:expr, $($arg:tt)+) => {
    $span.log_error(format_args!($($arg)+))
  };
}

/// Logs fatal error message.
#[macro_export]
macro_rules! log_fatal_error {
  ($span:expr, $($arg:tt)+) => {
    $span.log_fatal_error(format_args!($($arg)+))
  };
}

/// Logs warning message.
#[macro_export]
macro_rules! log_warning {
  ($span:expr, $($arg:tt)+) => {
    $span.log_warning(format_args!($($arg)+))
  };
}

/// Logs error message and returns a result.
#[macro_export]
macro_rules! return_error {
  ($span:expr, $($arg:tt)+) => {
    return $span.log_error(format_args!($($arg)+)).into()
  };
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn pos_update() {
    let mut pos = Pos::new();
    assert_eq!(format!("{}", pos), "1:0");
    pos.update(' ');
    pos.update(' ');
    assert_eq!(format!("{}", pos), "1:2");
    pos.update('\n');
    assert_eq!(format!("{}", pos), "2:0");
    pos.update('\n');
    pos.update('\n');
    assert_eq!(format!("{}", pos), "4:0");
  }

  #[test]
  fn span_update() {
    let mut pos = Pos::new();
    pos.update(' ');
    let sp1 = Span::new(pos);
    pos.update(' ');
    pos.update(' ');
    let sp2 = sp1.into_updated(pos);
    assert!(sp1.is_in_same_line_as(&sp2));
    log_error!(sp2, "test error");
    log_warning!(sp2, "test warning");
    log_warning!(sp2, "test warning 2");
    Span::log_global();
    assert_eq!(format!("{}", sp2.start), "1:1");
    assert_eq!(format!("{}", sp2.end), "1:3");
    let mut sp = Span::new(Pos { line: 10, col: 10 });
    sp.update(Pos { line: 10, col: 15 });
    assert!(!sp2.is_in_same_line_as(&sp));
    let sp3 = sp2.into_updated_span(sp);
    assert!(sp2.is_in_same_line_as(&sp3));
    assert_eq!(format!("{}", sp3.start), "1:1");
    assert_eq!(format!("{}", sp3.end), "10:15");
  }
}
