use std::cell::RefCell;
use std::fmt;
use std::result::Result;

#[cfg(not(feature = "no-front-logger"))]
use colored::*;
#[cfg(not(feature = "no-front-logger"))]
use std::{fs::File, io::BufRead, io::BufReader, io::Result as IoResult};

/// The type of error returned by logger methods of `Span`.
#[cfg(feature = "no-front-logger")]
#[derive(Debug)]
pub enum Error {
  Normal(String),
  Fatal(String),
}

/// The type of error returned by logger methods of `Span`.
#[cfg(not(feature = "no-front-logger"))]
#[derive(Debug)]
pub enum Error {
  Normal,
  Fatal,
}

impl Error {
  /// Checks if the current error is fatal.
  #[cfg(feature = "no-front-logger")]
  pub fn is_fatal(&self) -> bool {
    matches!(self, Error::Fatal(..))
  }

  /// Checks if the current error is fatal.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn is_fatal(&self) -> bool {
    matches!(self, Error::Fatal)
  }
}

/// A span.
///
/// Used to print error messages.
#[derive(Clone, Copy)]
pub struct Span {
  start: Pos,
  end: Pos,
}

/// Gets the string of the specific line.
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

  /// Logs normal error with no span provided.
  #[cfg(feature = "no-front-logger")]
  pub fn log_raw_error<T>(message: &str) -> Result<T, Error> {
    // update error number
    Self::STATE.with(|gs| gs.borrow_mut().err_num += 1);
    Err(Error::Normal(message.into()))
  }

  /// Logs normal error with no span provided.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_raw_error<T>(message: &str) -> Result<T, Error> {
    Self::STATE.with(|gs| {
      // update error number
      gs.borrow_mut().err_num += 1;
      // print message to stderr
      eprintln!("{}: {}", "error".bright_red(), message);
    });
    Err(Error::Normal)
  }

  /// Logs fatal error with no span provided.
  #[cfg(feature = "no-front-logger")]
  pub fn log_raw_fatal_error<T>(message: &str) -> Result<T, Error> {
    // update error number
    Self::STATE.with(|gs| gs.borrow_mut().err_num += 1);
    Err(Error::Fatal(message.into()))
  }

  /// Logs fatal error with no span provided.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_raw_fatal_error<T>(message: &str) -> Result<T, Error> {
    Self::STATE.with(|gs| {
      // update error number
      gs.borrow_mut().err_num += 1;
      // print message to stderr
      eprintln!("{}: {}", "error".bright_red(), message);
    });
    Err(Error::Fatal)
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

  /// Logs normal error message.
  #[cfg(feature = "no-front-logger")]
  pub fn log_error<T>(&self, message: &str) -> Result<T, Error> {
    Self::log_raw_error::<()>(message).unwrap_err();
    Err(Error::Normal(self.get_error_message(message)))
  }

  /// Logs normal error message.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_error<T>(&self, message: &str) -> Result<T, Error> {
    Self::log_raw_error::<()>(message).unwrap_err();
    Self::STATE.with(|gs| self.print_file_info(&gs.borrow().file, Color::BrightRed));
    Err(Error::Normal)
  }

  /// Logs fatal error message.
  #[cfg(feature = "no-front-logger")]
  pub fn log_fatal_error<T>(&self, message: &str) -> Result<T, Error> {
    Self::log_raw_error::<()>(message).unwrap_err();
    Err(Error::Fatal(self.get_error_message(message)))
  }

  /// Logs fatal error message.
  #[cfg(not(feature = "no-front-logger"))]
  pub fn log_fatal_error<T>(&self, message: &str) -> Result<T, Error> {
    Self::log_raw_error::<()>(message).unwrap_err();
    Self::STATE.with(|gs| self.print_file_info(&gs.borrow().file, Color::BrightRed));
    Err(Error::Fatal)
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

  /// Checks if the current span is in the same line as the specific span.
  pub fn is_in_same_line_as(&self, span: &Span) -> bool {
    self.end.line == span.start.line
  }

  /// Gets error message.
  #[cfg(feature = "no-front-logger")]
  fn get_error_message(&self, message: &str) -> String {
    Self::STATE.with(|gs| format!("{}:{}: {}", gs.borrow().file, self.start, message))
  }

  /// Prints file information.
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

  /// Prints single line information.
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

  /// Prints multi-line information.
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
    Self { line: 1, col: 0 }
  }

  /// Updates the line number ans column number based on the specific character.
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
    assert_eq!(sp1.is_in_same_line_as(&sp2), true);
    sp2.log_error::<()>("test error").unwrap_err();
    sp2.log_warning("test warning");
    sp2.log_warning("test warning 2");
    Span::log_global();
    assert_eq!(format!("{}", sp2.start), "1:1");
    assert_eq!(format!("{}", sp2.end), "1:3");
    let mut sp = Span::new(Pos { line: 10, col: 10 });
    sp.update(Pos { line: 10, col: 15 });
    assert_eq!(sp2.is_in_same_line_as(&sp), false);
    let sp3 = sp2.into_updated_span(sp);
    assert_eq!(sp2.is_in_same_line_as(&sp3), true);
    assert_eq!(format!("{}", sp3.start), "1:1");
    assert_eq!(format!("{}", sp3.end), "10:15");
  }
}
