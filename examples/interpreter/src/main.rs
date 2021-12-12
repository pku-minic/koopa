mod ext_funcs;

use ext_funcs::ExternFuncs;
use koopa::back::{Generator, NameManager, Visitor};
use koopa::ir::structs::BasicBlockRef;
use koopa::ir::{Function, Program, Type, TypeKind, Value, ValueKind};
use koopa::value;
use std::collections::HashMap;
use std::io::{Error, ErrorKind, Result, Write};
use std::ptr::NonNull;
use std::rc::Rc;

fn main() {
  println!("Hello, world!");
}

struct Interpreter<'lib> {
  vars: HashMap<*const Value, Box<Val>>,
  env: Option<Environment>,
  ext_funcs: ExternFuncs<'lib>,
}

impl<'lib, W: Write> Visitor<W> for Interpreter<'lib> {
  type Output = i32;

  fn visit(&mut self, _: &mut W, _: &mut NameManager, program: &Program) -> Result<Self::Output> {
    // evaluate all global variables
    for var in program.vars() {
      match var.kind() {
        ValueKind::GlobalAlloc(ga) => {
          let val = Self::eval_const(value!(ga.init()))?;
          self.vars.insert(var, Box::new(val));
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

impl<'lib> Interpreter<'lib> {
  fn new(ext_funcs: ExternFuncs<'lib>) -> Self {
    Self {
      vars: HashMap::default(),
      env: Option::default(),
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
    // check if is a function declaration
    // TODO
    // setup the environment
    assert_eq!(
      func.params().len(),
      args.len(),
      "{} parameters required but got {} in function '{}'",
      func.params().len(),
      args.len(),
      func.name(),
    );
    self.env = Some(Environment::new(
      func
        .params()
        .iter()
        .map(|p| Rc::as_ptr(p))
        .zip(args.into_iter().map(Box::new))
        .collect(),
    ));
    func.inner().bbs();
    todo!()
  }
}

struct Environment {
  allocs: HashMap<*const Value, Box<Val>>,
  last_bb: BasicBlockRef,
}

impl Environment {
  fn new(allocs: HashMap<*const Value, Box<Val>>) -> Self {
    Self {
      allocs,
      last_bb: BasicBlockRef::default(),
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
}
