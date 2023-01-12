mod ext_funcs;
mod interpreter;

use interpreter::Interpreter;
use koopa::back::Generator;
use koopa::front::Driver;
use std::io::{sink, stdin, Error};
use std::{env, fmt, process, result};

fn main() {
  process::exit(try_main().unwrap_or_else(|e| {
    eprintln!("{}", e);
    -1
  }));
}

fn try_main() -> result::Result<i32, MainError> {
  // parse command line arguments
  let CommandLineArgs { input, libs } = parse_cmd_args()?;
  // parse the input file
  let program = if let Some(file) = input {
    Driver::from_path(file)
      .map_err(MainError::InvalidFile)?
      .generate_program()
  } else {
    Driver::from(stdin()).generate_program()
  }
  .map_err(|_| MainError::ParseError)?;
  // interpret the program
  let interpreter = Interpreter::new(libs);
  Generator::with_visitor(sink(), interpreter)
    .generate_on(&program)
    .map_err(MainError::OtherError)
}

enum MainError {
  InvalidArgs,
  InvalidFile(Error),
  ParseError,
  OtherError(Error),
}

impl fmt::Display for MainError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      MainError::InvalidArgs => write!(
        f,
        r#"Usage: interpreter [FILE] [-l DYN_LIB ...]
Options:
  FILE        use FILE as input instead of stdin
  -l DYN_LIB  load dynamic library DYN_LIB"#
      ),
      MainError::InvalidFile(error) => write!(f, "invalid file operation: {}", error),
      MainError::ParseError => write!(f, "error occurred when parsing the input"),
      MainError::OtherError(error) => write!(f, "{}", error),
    }
  }
}

#[derive(Default)]
struct CommandLineArgs {
  input: Option<String>,
  libs: Vec<String>,
}

fn parse_cmd_args() -> result::Result<CommandLineArgs, MainError> {
  let mut cmd_args = CommandLineArgs::default();
  let mut args = env::args();
  args.next();
  loop {
    match (args.next(), args.next()) {
      (Some(file), Some(o)) if file != "-l" && o == "-l" => {
        cmd_args.input = Some(file);
        cmd_args
          .libs
          .push(args.next().ok_or(MainError::InvalidArgs)?);
      }
      (Some(file), _) if file != "-l" => cmd_args.input = Some(file),
      (Some(o), Some(lib)) if o == "-l" => cmd_args.libs.push(lib),
      (None, None) => break,
      _ => return Err(MainError::InvalidArgs),
    }
  }
  Ok(cmd_args)
}
