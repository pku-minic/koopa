use koopa::back::{KoopaGenerator, LlvmGenerator};
use koopa::ir::builder_traits::*;
use koopa::ir::{BasicBlock, BinaryOp, Function, FunctionData, Program, Type, Value};
use std::env::args;
use std::fs::File;
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
  let zero = program
    .new_value()
    .zero_init(Type::get_array(Type::get_i32(), 65536));
  let ptr = program.new_value().global_alloc(zero);
  program.set_value_name(ptr, Some("@data_arr".into()));
  // create function declarations
  let putchar = FunctionData::new_decl("@putchar".into(), vec![Type::get_i32()], Type::get_i32());
  let putchar = program.new_func(putchar);
  let getchar = FunctionData::new_decl("@getchar".into(), Vec::new(), Type::get_i32());
  let getchar = program.new_func(getchar);
  // generate main function
  let main = FunctionData::new("@main".into(), Vec::new(), Type::get_i32());
  let main = program.new_func(main);
  generate_main(
    input,
    Environment {
      ptr,
      putchar,
      getchar,
      main: program.func_mut(main),
    },
  )?;
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

struct Environment<'a> {
  ptr: Value,
  putchar: Function,
  getchar: Function,
  main: &'a mut FunctionData,
}

macro_rules! new_bb {
  ($func:expr) => {
    $func.dfg_mut().new_bb()
  };
}

macro_rules! new_value {
  ($func:expr) => {
    $func.dfg_mut().new_value()
  };
}

macro_rules! add_bb {
  ($func:expr, $bb:expr) => {
    $func.layout_mut().bbs_mut().push_key_back($bb).unwrap()
  };
}

macro_rules! add_inst {
  ($func:expr, $bb:expr, $inst:expr) => {
    $func
      .layout_mut()
      .bb_mut($bb)
      .insts_mut()
      .push_key_back($inst)
      .unwrap()
  };
}

fn generate_main(input: impl io::Read, mut env: Environment) -> Result<(), Error> {
  // generate entry basic block
  let main = &mut env.main;
  let entry = new_bb!(main).basic_block(Some("%entry".into()));
  add_bb!(main, entry);
  let ptr = new_value!(main).alloc(Type::get_pointer(Type::get_i32()));
  main.dfg_mut().set_value_name(ptr, Some("%ptr".into()));
  add_inst!(main, entry, ptr);
  let zero = new_value!(main).integer(0);
  let data_ptr = new_value!(main).get_elem_ptr(env.ptr, zero);
  add_inst!(main, entry, data_ptr);
  let store = new_value!(main).store(data_ptr, ptr);
  add_inst!(main, entry, store);
  env.ptr = ptr;
  // generate other basic blocks by the given input
  let bb = generate_bbs(input, &mut env, entry)?;
  // generate end basic block
  let main = &mut env.main;
  let end = new_bb!(main).basic_block(Some("%end".into()));
  add_bb!(main, end);
  let jump = new_value!(main).jump(end);
  add_inst!(main, bb, jump);
  let ret = new_value!(main).ret(Some(zero));
  add_inst!(main, end, ret);
  Ok(())
}

fn generate_bbs(
  input: impl io::Read,
  env: &mut Environment,
  entry: BasicBlock,
) -> Result<BasicBlock, Error> {
  let mut bb = new_bb!(env.main).basic_block(None);
  add_bb!(env.main, bb);
  let jump = new_value!(env.main).jump(bb);
  add_inst!(env.main, entry, jump);
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

fn generate_ptr_op(env: &mut Environment, bb: BasicBlock, i: i32) -> Result<BasicBlock, Error> {
  let main = &mut env.main;
  let load = new_value!(main).load(env.ptr);
  add_inst!(main, bb, load);
  let index = new_value!(main).integer(i);
  let gp = new_value!(main).get_ptr(load, index);
  add_inst!(main, bb, gp);
  let store = new_value!(main).store(gp, env.ptr);
  add_inst!(main, bb, store);
  Ok(bb)
}

fn generate_data_op(env: &mut Environment, bb: BasicBlock, i: i32) -> Result<BasicBlock, Error> {
  let main = &mut env.main;
  let load = new_value!(main).load(env.ptr);
  add_inst!(main, bb, load);
  let data = new_value!(main).load(load);
  add_inst!(main, bb, data);
  let rhs = new_value!(main).integer(i);
  let add = new_value!(main).binary(BinaryOp::Add, data, rhs);
  add_inst!(main, bb, add);
  let store = new_value!(main).store(add, load);
  add_inst!(main, bb, store);
  Ok(bb)
}

fn generate_start(
  env: &mut Environment,
  bb: BasicBlock,
  loop_info: &mut Vec<(BasicBlock, BasicBlock)>,
) -> Result<BasicBlock, Error> {
  let main = &mut env.main;
  // create while condition
  let cond_bb = new_bb!(main).basic_block(Some("%while_cond".into()));
  add_bb!(main, cond_bb);
  let jump = new_value!(main).jump(cond_bb);
  add_inst!(main, bb, jump);
  // add instructions
  let load = new_value!(main).load(env.ptr);
  add_inst!(main, cond_bb, load);
  let data = new_value!(main).load(load);
  add_inst!(main, cond_bb, data);
  let zero = new_value!(main).integer(0);
  let cmp = new_value!(main).binary(BinaryOp::NotEq, data, zero);
  add_inst!(main, cond_bb, cmp);
  // create while body and while end
  let body_bb = new_bb!(main).basic_block(Some("%while_body".into()));
  let end_bb = new_bb!(main).basic_block(Some("%while_end".into()));
  let br = new_value!(main).branch(cmp, body_bb, end_bb);
  add_inst!(main, cond_bb, br);
  add_bb!(main, body_bb);
  // update loop info
  loop_info.push((cond_bb, end_bb));
  Ok(body_bb)
}

fn generate_end(
  env: &mut Environment,
  bb: BasicBlock,
  loop_info: &mut Vec<(BasicBlock, BasicBlock)>,
) -> Result<BasicBlock, Error> {
  let (cond_bb, end_bb) = loop_info.pop().ok_or(Error::Parse)?;
  let jump = new_value!(env.main).jump(cond_bb);
  add_inst!(env.main, bb, jump);
  add_bb!(env.main, end_bb);
  Ok(end_bb)
}

fn generate_put(env: &mut Environment, bb: BasicBlock) -> Result<BasicBlock, Error> {
  let main = &mut env.main;
  let load = new_value!(main).load(env.ptr);
  add_inst!(main, bb, load);
  let data = new_value!(main).load(load);
  add_inst!(main, bb, data);
  let call = new_value!(main).call(env.putchar, vec![data]);
  add_inst!(main, bb, call);
  Ok(bb)
}

fn generate_get(env: &mut Environment, bb: BasicBlock) -> Result<BasicBlock, Error> {
  let main = &mut env.main;
  let call = new_value!(main).call(env.getchar, Vec::new());
  add_inst!(main, bb, call);
  let load = new_value!(main).load(env.ptr);
  add_inst!(main, bb, load);
  let store = new_value!(main).store(call, load);
  add_inst!(main, bb, store);
  Ok(bb)
}
