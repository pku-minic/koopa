mod const_fold;
mod dce;

use koopa::back::KoopaGenerator;
use koopa::front::Driver;
use koopa::opt::{Pass, PassManager};
use std::env::args;
use std::{fmt, io, process};

fn main() {
  if let Err(error) = try_main() {
    eprintln!("{}", error);
    process::exit(1);
  }
}

enum Error {
  InvalidFile(io::Error),
  InvalidArgs,
  Parse,
  Io(io::Error),
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Error::InvalidFile(error) => write!(f, "invalid file operation: {}", error),
      Error::InvalidArgs => write!(f, "usage: opt INPUT OUTPUT"),
      Error::Parse => write!(f, "error occurred when parsing the input"),
      Error::Io(error) => write!(f, "IO error: {}", error),
    }
  }
}

fn try_main() -> Result<(), Error> {
  // parse arguments
  let mut args = args();
  args.next();
  let (driver, output) = match (args.next(), args.next(), args.next()) {
    (Some(input), Some(output), None) => (
      Driver::from_path(input).map_err(Error::InvalidFile)?,
      output,
    ),
    _ => return Err(Error::InvalidArgs),
  };
  // parse input file
  let mut program = driver.generate_program().map_err(|_| Error::Parse)?;
  // run passes
  let mut passman = PassManager::new();
  passman.register(Pass::Function(Box::new(const_fold::ConstantFolding::new())));
  passman.register(Pass::Function(Box::new(dce::DeadCodeElimination::new())));
  passman.run_passes(&mut program);
  // dump the output
  let mut generator = KoopaGenerator::from_path(output).map_err(Error::InvalidFile)?;
  generator.generate_on(&program).map_err(Error::Io)
}
