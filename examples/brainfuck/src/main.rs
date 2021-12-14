use koopa::back::{KoopaGenerator, LlvmGenerator};
use koopa::ir::{instructions as insts, values};
use koopa::ir::{BasicBlock, BasicBlockRc, Function, FunctionRc, Program, Type, ValueRc};
use std::env::args;
use std::fs::File;
use std::rc::Rc;
use std::{fmt, io, process};

fn main() {
  if let Err(error) = try_main() {
    eprintln!("{}", error);
    process::exit(1);
  }
}

fn try_main() -> Result<(), Error> {
  // parse command line arguments
  let CommandLineArgs {
    input,
    output,
    emit_llvm,
  } = parse_cmd_args()?;
  // build Koopa IR program by parsing the input
  let program = if let Some(file) = input {
    build_program(File::open(file).map_err(Error::InvalidFile)?)?
  } else {
    build_program(io::stdin())?
  };
  // emit IR to the output
  if let Some(file) = output {
    emit_ir(
      &program,
      File::create(file).map_err(Error::InvalidFile)?,
      emit_llvm,
    )
  } else {
    emit_ir(&program, io::stdout(), emit_llvm)
  }
}

enum Error {
  InvalidArgs,
  InvalidFile(io::Error),
  Parse,
  Io(io::Error),
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Error::InvalidArgs => write!(
        f,
        r#"Usage: brainfuck [-i FILE] [-o FILE] [-ll]
Options:
  -i FILE   use FILE as input instead of stdin
  -o FILE   use FILE as output instead of stdout
  -ll       emit LLVM IR instead of Koopa IR"#
      ),
      Error::InvalidFile(error) => write!(f, "invalid file operation: {}", error),
      Error::Parse => write!(f, "invalid brainfuck input"),
      Error::Io(error) => write!(f, "IO error: {}", error),
    }
  }
}

#[derive(Default)]
struct CommandLineArgs {
  input: Option<String>,
  output: Option<String>,
  emit_llvm: bool,
}

fn parse_cmd_args() -> Result<CommandLineArgs, Error> {
  let mut cmd_args = CommandLineArgs::default();
  let mut args = args();
  args.next();
  loop {
    match (args.next(), args.next()) {
      (Some(o), Some(file)) if o == "-i" => cmd_args.input = Some(file),
      (Some(o), Some(file)) if o == "-o" => cmd_args.output = Some(file),
      (Some(o), None) if o == "-ll" => cmd_args.emit_llvm = true,
      (None, None) => break,
      _ => return Err(Error::InvalidArgs),
    }
  }
  Ok(cmd_args)
}

fn build_program(input: impl io::Read) -> Result<Program, Error> {
  let mut program = Program::new();
  // create data array
  let ptr = insts::GlobalAlloc::new(values::ZeroInit::get(Type::get_array(
    Type::get_i32(),
    65536,
  )));
  ptr.inner_mut().set_name(Some("@data_arr".into()));
  program.add_var(ptr.clone());
  // create function declarations
  let putchar = Function::new_decl(
    "@putchar".into(),
    Type::get_function(vec![Type::get_i32()], Type::get_i32()),
  );
  let getchar = Function::new_decl(
    "@getchar".into(),
    Type::get_function(Vec::new(), Type::get_i32()),
  );
  program.add_func(putchar.clone());
  program.add_func(getchar.clone());
  // generate main function
  let main = Function::new("@main".into(), Vec::new(), Type::get_i32());
  program.add_func(generate_main(
    input,
    Environment {
      ptr,
      putchar,
      getchar,
      main,
    },
  )?);
  Ok(program)
}

fn emit_ir(program: &Program, output: impl io::Write, emit_llvm: bool) -> Result<(), Error> {
  if emit_llvm {
    LlvmGenerator::new(output).generate_on(program)
  } else {
    KoopaGenerator::new(output).generate_on(program)
  }
  .map_err(Error::Io)
}

// =========================================================== //
//   Stuffs that generate Koopa IR from the brainfuck input.   //
// =========================================================== //

struct Environment {
  ptr: ValueRc,
  putchar: FunctionRc,
  getchar: FunctionRc,
  main: FunctionRc,
}

fn generate_main(input: impl io::Read, mut env: Environment) -> Result<FunctionRc, Error> {
  // generate entry basic block
  let entry = BasicBlock::new(Some("%entry".into()));
  env.main.inner_mut().add_bb(entry.clone());
  let mut entry_inner = entry.inner_mut();
  let ptr = insts::Alloc::new(Type::get_pointer(Type::get_i32()));
  ptr.inner_mut().set_name(Some("%ptr".into()));
  entry_inner.add_inst(ptr.clone());
  let data_ptr = insts::GetElemPtr::new(env.ptr, values::Integer::get(0));
  entry_inner.add_inst(data_ptr.clone());
  entry_inner.add_inst(insts::Store::new(data_ptr, ptr.clone()));
  env.ptr = ptr;
  // generate other basic blocks by the specific input
  drop(entry_inner);
  let bb = generate_bbs(input, &env, entry)?;
  // generate end basic block
  let end = BasicBlock::new(Some("%end".into()));
  bb.inner_mut()
    .add_inst(insts::Jump::new(Rc::downgrade(&end)));
  end
    .inner_mut()
    .add_inst(insts::Return::new(Some(values::Integer::get(0))));
  env.main.inner_mut().add_bb(end);
  Ok(env.main)
}

fn generate_bbs(
  input: impl io::Read,
  env: &Environment,
  entry: BasicBlockRc,
) -> Result<BasicBlockRc, Error> {
  let mut bb = BasicBlock::new(None);
  env.main.inner_mut().add_bb(bb.clone());
  entry
    .inner_mut()
    .add_inst(insts::Jump::new(Rc::downgrade(&bb)));
  let mut loop_info = Vec::new();
  for result in input.bytes() {
    bb = match result.map_err(Error::Io)? {
      b'>' => generate_ptr_op(env, bb, 1),
      b'<' => generate_ptr_op(env, bb, -1),
      b'+' => generate_data_op(env, bb, 1),
      b'-' => generate_data_op(env, bb, -1),
      b'[' => generate_start(env, bb, &mut loop_info),
      b']' => generate_end(env, bb, &mut loop_info),
      b'.' => generate_put(env, bb),
      b',' => generate_get(env, bb),
      _ => continue,
    }?;
  }
  Ok(bb)
}

fn generate_ptr_op(env: &Environment, bb: BasicBlockRc, i: i32) -> Result<BasicBlockRc, Error> {
  let mut inner = bb.inner_mut();
  let load = insts::Load::new(env.ptr.clone());
  inner.add_inst(load.clone());
  let gp = insts::GetPtr::new(load, values::Integer::get(i));
  inner.add_inst(gp.clone());
  inner.add_inst(insts::Store::new(gp, env.ptr.clone()));
  drop(inner);
  Ok(bb)
}

fn generate_data_op(env: &Environment, bb: BasicBlockRc, i: i32) -> Result<BasicBlockRc, Error> {
  let mut inner = bb.inner_mut();
  let load = insts::Load::new(env.ptr.clone());
  inner.add_inst(load.clone());
  let data = insts::Load::new(load.clone());
  inner.add_inst(data.clone());
  let add = insts::Binary::new(insts::BinaryOp::Add, data, values::Integer::get(i));
  inner.add_inst(add.clone());
  inner.add_inst(insts::Store::new(add, load));
  drop(inner);
  Ok(bb)
}

fn generate_start(
  env: &Environment,
  bb: BasicBlockRc,
  loop_info: &mut Vec<(BasicBlockRc, BasicBlockRc)>,
) -> Result<BasicBlockRc, Error> {
  // create while condition
  let cond_bb = BasicBlock::new(Some("%while_cond".into()));
  env.main.inner_mut().add_bb(cond_bb.clone());
  bb.inner_mut()
    .add_inst(insts::Jump::new(Rc::downgrade(&cond_bb)));
  // add instructions
  let mut inner = cond_bb.inner_mut();
  let load = insts::Load::new(env.ptr.clone());
  inner.add_inst(load.clone());
  let data = insts::Load::new(load);
  inner.add_inst(data.clone());
  let cmp = insts::Binary::new(insts::BinaryOp::NotEq, data, values::Integer::get(0));
  inner.add_inst(cmp.clone());
  // create while body and while end
  let body_bb = BasicBlock::new(Some("%while_body".into()));
  let end_bb = BasicBlock::new(Some("%while_end".into()));
  inner.add_inst(insts::Branch::new(
    cmp,
    Rc::downgrade(&body_bb),
    Rc::downgrade(&end_bb),
  ));
  env.main.inner_mut().add_bb(body_bb.clone());
  // update loop info
  drop(inner);
  loop_info.push((cond_bb, end_bb));
  Ok(body_bb)
}

fn generate_end(
  env: &Environment,
  bb: BasicBlockRc,
  loop_info: &mut Vec<(BasicBlockRc, BasicBlockRc)>,
) -> Result<BasicBlockRc, Error> {
  let (cond_bb, end_bb) = loop_info.pop().ok_or(Error::Parse)?;
  bb.inner_mut()
    .add_inst(insts::Jump::new(Rc::downgrade(&cond_bb)));
  env.main.inner_mut().add_bb(end_bb.clone());
  Ok(end_bb)
}

fn generate_put(env: &Environment, bb: BasicBlockRc) -> Result<BasicBlockRc, Error> {
  let mut inner = bb.inner_mut();
  let load = insts::Load::new(env.ptr.clone());
  inner.add_inst(load.clone());
  let data = insts::Load::new(load);
  inner.add_inst(data.clone());
  inner.add_inst(insts::Call::new(Rc::downgrade(&env.putchar), vec![data]));
  drop(inner);
  Ok(bb)
}

fn generate_get(env: &Environment, bb: BasicBlockRc) -> Result<BasicBlockRc, Error> {
  let mut inner = bb.inner_mut();
  let call = insts::Call::new(Rc::downgrade(&env.getchar), Vec::new());
  inner.add_inst(call.clone());
  let load = insts::Load::new(env.ptr.clone());
  inner.add_inst(load.clone());
  inner.add_inst(insts::Store::new(call, load));
  drop(inner);
  Ok(bb)
}
