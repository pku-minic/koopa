mod ext_funcs;

use ext_funcs::ExternFuncs;
use koopa::back::{Generator, NameManager, Visitor};
use koopa::ir::instructions::*;
use koopa::ir::{BasicBlock, Function, Program, Type, TypeKind, Value, ValueKind};
use koopa::value;
use std::collections::HashMap;
use std::io::{Error, ErrorKind, Result, Write};
use std::ptr::{null, NonNull};
use std::rc::Rc;

fn main() {
  println!("Hello, world!");
}

struct Interpreter {
  global_allocs: Vec<Box<Val>>,
  vars: HashMap<*const Value, Val>,
  envs: Vec<Environment>,
  ext_funcs: ExternFuncs,
}

impl<W: Write> Visitor<W> for Interpreter {
  type Output = i32;

  fn visit(&mut self, _: &mut W, _: &mut NameManager, program: &Program) -> Result<Self::Output> {
    // evaluate all global variables
    for var in program.vars() {
      match var.kind() {
        ValueKind::GlobalAlloc(ga) => {
          let val = Self::eval_const(value!(ga.init()))?;
          self.global_allocs.push(Box::new(val));
          self
            .vars
            .insert(var, Val::new_val_pointer(self.global_allocs.last()));
        }
        _ => panic!("invalid global variable"),
      }
    }
    // evaluate on the main function
    program
      .funcs()
      .iter()
      .find(|f| f.name() == "@main")
      .ok_or_else(|| Self::new_error("function '@main' not found"))
      .and_then(|f| self.eval_func(f, Vec::new()))
      .and_then(|v| {
        if let Val::Int(i) = v {
          Ok(i)
        } else {
          Err(Self::new_error("function '@main' must return an integer"))
        }
      })
  }
}

impl Interpreter {
  fn new(ext_funcs: ExternFuncs) -> Self {
    Self {
      global_allocs: Vec::new(),
      vars: HashMap::new(),
      envs: Vec::new(),
      ext_funcs,
    }
  }

  fn new_error(message: &str) -> Error {
    Error::new(ErrorKind::Other, message)
  }

  fn eval_const(value: &Value) -> Result<Val> {
    match value.kind() {
      ValueKind::Integer(v) => Ok(Val::Int(v.value())),
      ValueKind::ZeroInit(_) => Self::new_zeroinit(value.ty()),
      ValueKind::Undef(_) => Ok(Val::Undef),
      ValueKind::Aggregate(v) => Ok(Val::Array(
        v.elems()
          .iter()
          .map(|e| Self::eval_const(value!(e)))
          .collect::<Result<_>>()?,
      )),
      _ => panic!("invalid constant"),
    }
  }

  fn new_zeroinit(ty: &Type) -> Result<Val> {
    match ty.kind() {
      TypeKind::Int32 => Ok(Val::Int(0)),
      TypeKind::Array(base, len) => Ok(Val::Array(
        (0..*len)
          .map(|_| Self::new_zeroinit(base))
          .collect::<Result<_>>()?,
      )),
      TypeKind::Pointer(_) => Ok(Val::new_val_pointer(None)),
      _ => panic!("invalid type of zero initializer"),
    }
  }

  fn eval_func(&mut self, func: &Function, args: Vec<Val>) -> Result<Val> {
    // check parameter count
    assert_eq!(func.params().len(), args.len(), "parameter count mismatch");
    // check if is a function declaration
    if let Some(bb) = func.inner().bbs().front().get() {
      // setup the environment
      self.envs.push(Environment::new(
        func
          .params()
          .iter()
          .map(|p| Rc::as_ptr(p))
          .zip(args.into_iter())
          .collect(),
      ));
      // evaluate the entry basic block
      let ret = self.eval_bb(bb);
      self.envs.pop();
      ret
    } else {
      // call the external function
      unsafe { self.ext_funcs.call(func, args) }
    }
  }

  fn eval_bb(&mut self, bb: &BasicBlock) -> Result<Val> {
    // evaluate on all instructions
    for inst in bb.inner().insts() {
      match inst.kind() {
        ValueKind::Alloc(_) => self.eval_alloc(inst)?,
        ValueKind::Load(v) => self.eval_load(inst, v)?,
        ValueKind::Store(v) => self.eval_store(inst, v)?,
        ValueKind::GetPtr(v) => self.eval_getptr(inst, v)?,
        ValueKind::GetElemPtr(v) => self.eval_getelemptr(inst, v)?,
        ValueKind::Binary(v) => self.eval_binary(inst, v)?,
        ValueKind::Call(v) => self.eval_call(inst, v)?,
        ValueKind::Phi(v) => self.eval_phi(inst, v)?,
        ValueKind::Branch(v) => return self.eval_branch(bb, v),
        ValueKind::Jump(v) => return self.eval_jump(bb, v),
        ValueKind::Return(v) => return self.eval_return(v),
        _ => panic!("invalid instruction"),
      }
    }
    unreachable!()
  }

  fn eval_alloc(&mut self, inst: &Value) -> Result<()> {
    let base = match inst.ty().kind() {
      TypeKind::Pointer(base) => base,
      _ => panic!("invalid pointer type"),
    };
    let env = self.envs.first_mut().unwrap();
    env.allocs.push(Box::new(Self::new_zeroinit(base)?));
    env
      .vals
      .insert(inst, Val::new_val_pointer(env.allocs.last()));
    Ok(())
  }

  fn eval_load(&mut self, inst: &Value, load: &Load) -> Result<()> {
    todo!()
  }

  fn eval_store(&mut self, inst: &Value, store: &Store) -> Result<()> {
    todo!()
  }

  fn eval_getptr(&mut self, inst: &Value, gp: &GetPtr) -> Result<()> {
    todo!()
  }

  fn eval_getelemptr(&mut self, inst: &Value, gep: &GetElemPtr) -> Result<()> {
    todo!()
  }

  fn eval_binary(&mut self, inst: &Value, bin: &Binary) -> Result<()> {
    todo!()
  }

  fn eval_call(&mut self, inst: &Value, call: &Call) -> Result<()> {
    todo!()
  }

  fn eval_phi(&mut self, inst: &Value, phi: &Phi) -> Result<()> {
    todo!()
  }

  fn eval_branch(&mut self, cur_bb: &BasicBlock, br: &Branch) -> Result<Val> {
    // update last basic block
    self.envs.first_mut().unwrap().last_bb = cur_bb;
    // evaluate on condition
    let cond = self.eval_value(value!(br.cond()))?;
    // perform branching
    if cond.as_bool() {
      self.eval_bb(br.true_bb().upgrade().unwrap().as_ref())
    } else {
      self.eval_bb(br.false_bb().upgrade().unwrap().as_ref())
    }
  }

  fn eval_jump(&mut self, cur_bb: &BasicBlock, jump: &Jump) -> Result<Val> {
    // update last basic block
    self.envs.first_mut().unwrap().last_bb = cur_bb;
    // just jump
    self.eval_bb(jump.target().upgrade().unwrap().as_ref())
  }

  fn eval_return(&mut self, ret: &Return) -> Result<Val> {
    ret
      .value()
      .value()
      .map_or(Ok(Val::Undef), |v| self.eval_value(v.as_ref()))
  }

  fn eval_value(&mut self, val: &Value) -> Result<Val> {
    // TODO: &mut self -> &self
    // TODO: do not use `Result` as return type
    todo!()
  }
}

struct Environment {
  allocs: Vec<Box<Val>>,
  vals: HashMap<*const Value, Val>,
  last_bb: *const BasicBlock,
}

impl Environment {
  fn new(vals: HashMap<*const Value, Val>) -> Self {
    Self {
      allocs: Vec::new(),
      vals,
      last_bb: null(),
    }
  }
}

enum Val {
  Undef,
  Int(i32),
  Array(Box<[Val]>),
  Pointer {
    ptr: Option<NonNull<Val>>,
    // if the pointer points to an array element,
    // the index and the total length of the parent array are recorded
    // in case of an out-of-bounds access
    index: usize,
    len: usize,
  },
  UnsafePointer(Option<NonNull<()>>),
}

impl Val {
  fn new_val_pointer(parent: Option<&Box<Val>>) -> Self {
    Self::Pointer {
      ptr: parent.map(|p| unsafe { NonNull::new_unchecked(p.as_ref() as *const Val as *mut Val) }),
      index: 0,
      len: 0,
    }
  }

  fn new_array_pointer(parent: Option<&Box<[Val]>>) -> Self {
    if let Some(arr) = parent {
      Self::Pointer {
        ptr: Some(unsafe { NonNull::new_unchecked(arr.as_ptr() as *mut Val) }),
        index: 0,
        len: arr.len(),
      }
    } else {
      Self::Pointer {
        ptr: None,
        index: 0,
        len: 0,
      }
    }
  }

  fn as_bool(&self) -> bool {
    matches!(self, Val::Int(i) if *i != 0)
  }
}
