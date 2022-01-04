// Use `Vec<Box<T>>` to prevent reallocation.
#![allow(clippy::vec_box)]
// For convenience.
#![allow(clippy::borrowed_box)]

use super::ext_funcs::ExternFuncs;
use koopa::back::{NameManager, Visitor};
use koopa::ir::entities::ValueData;
use koopa::ir::layout::BasicBlockNode;
use koopa::ir::values::*;
use koopa::ir::{BasicBlock, BinaryOp, FunctionData, Program, Type, TypeKind, Value, ValueKind};
use std::collections::HashMap;
use std::io::{Error, ErrorKind, Result, Write};
use std::ptr::{null, NonNull};

pub fn new_error(message: &str) -> Error {
  Error::new(ErrorKind::Other, message)
}

pub struct Interpreter {
  libs: Vec<String>,
}

impl Interpreter {
  pub fn new(libs: Vec<String>) -> Self {
    Self { libs }
  }
}

impl<W: Write> Visitor<W> for Interpreter {
  type Output = i32;

  fn visit(&mut self, _: &mut W, _: &mut NameManager, program: &Program) -> Result<Self::Output> {
    let ext_funcs = unsafe { ExternFuncs::new(&self.libs) }
      .map_err(|e| new_error(&format!("invalid library: {}", e)))?;
    let mut interpreter = InterpreterImpl::new(program, ext_funcs);
    interpreter.interpret()
  }
}

struct InterpreterImpl<'a> {
  program: &'a Program,
  global_allocs: Vec<Box<Val>>,
  vars: HashMap<*const ValueData, Val>,
  envs: Vec<Environment<'a>>,
  ext_funcs: ExternFuncs,
}

macro_rules! func {
  ($self:ident) => {
    $self.envs.last().unwrap().func
  };
}

macro_rules! value {
  ($self:ident, $value:expr) => {
    func!($self).dfg().value($value)
  };
}

macro_rules! bb_node {
  ($self:ident, $bb:expr) => {
    func!($self).layout().bbs().node(&$bb).unwrap()
  };
}

impl<'a> InterpreterImpl<'a> {
  fn new(program: &'a Program, ext_funcs: ExternFuncs) -> Self {
    Self {
      program,
      global_allocs: Vec::new(),
      vars: HashMap::new(),
      envs: Vec::new(),
      ext_funcs,
    }
  }

  fn interpret(&mut self) -> Result<i32> {
    // evaluate all global variables
    for var in self.program.inst_layout() {
      let value = self.program.borrow_value(*var);
      match value.kind() {
        ValueKind::GlobalAlloc(ga) => {
          let val = self.eval_global_const(&self.program.borrow_value(ga.init()));
          self.global_allocs.push(Box::new(val));
          self.vars.insert(
            &value as &ValueData,
            Val::new_val_pointer(self.global_allocs.last()),
          );
        }
        _ => panic!("invalid global variable"),
      }
    }
    // evaluate on the main function
    self
      .program
      .funcs()
      .values()
      .find(|f| f.name() == "@main")
      .ok_or_else(|| new_error("function '@main' not found"))
      .and_then(|f| self.eval_func(f, Vec::new()))
      .and_then(|v| {
        if let Val::Int(i) = v {
          Ok(i)
        } else {
          Err(new_error("function '@main' must return an integer"))
        }
      })
  }

  fn eval_global_const(&self, value: &ValueData) -> Val {
    match value.kind() {
      ValueKind::Integer(v) => Val::Int(v.value()),
      ValueKind::ZeroInit(_) => Self::new_zeroinit(value.ty()),
      ValueKind::Undef(_) => Val::Undef,
      ValueKind::Aggregate(v) => Val::Array(
        v.elems()
          .iter()
          .map(|e| self.eval_global_const(&self.program.borrow_value(*e)))
          .collect(),
      ),
      _ => panic!("invalid constant"),
    }
  }

  fn eval_local_const(&self, value: &ValueData) -> Val {
    match value.kind() {
      ValueKind::Integer(v) => Val::Int(v.value()),
      ValueKind::ZeroInit(_) => Self::new_zeroinit(value.ty()),
      ValueKind::Undef(_) => Val::Undef,
      ValueKind::Aggregate(v) => Val::Array(
        v.elems()
          .iter()
          .map(|e| self.eval_local_const(func!(self).dfg().value(*e)))
          .collect(),
      ),
      _ => panic!("invalid constant"),
    }
  }

  fn new_zeroinit(ty: &Type) -> Val {
    match ty.kind() {
      TypeKind::Int32 => Val::Int(0),
      TypeKind::Array(base, len) => {
        Val::Array((0..*len).map(|_| Self::new_zeroinit(base)).collect())
      }
      TypeKind::Pointer(_) => Val::new_val_pointer(None),
      _ => panic!("invalid type of zero initializer"),
    }
  }

  fn get_pointer(src: Val, offset: isize, base_size: usize) -> Result<Val> {
    match src {
      Val::Pointer { ptr, index, len } => {
        let new_index = (index as isize + offset) as usize;
        (new_index < len)
          .then(|| Val::Pointer {
            ptr: ptr.map(|p| unsafe { NonNull::new_unchecked(p.as_ptr().offset(offset)) }),
            index: new_index,
            len,
          })
          .ok_or_else(|| {
            new_error(&format!(
              "pointer calculation out of bounds with index {} and length {}",
              index, len
            ))
          })
      }
      Val::UnsafePointer(ptr) => Ok(Val::UnsafePointer(ptr.map(|p| unsafe {
        NonNull::new_unchecked((p.as_ptr() as isize + base_size as isize * offset) as *mut ())
      }))),
      _ => panic!("invalid pointer"),
    }
  }

  fn eval_func(&mut self, func: &'a FunctionData, args: Vec<Val>) -> Result<Val> {
    // check parameter count
    let param_len = match func.ty().kind() {
      TypeKind::Function(params, _) => params.len(),
      _ => panic!("invalid function"),
    };
    assert_eq!(param_len, args.len(), "parameter count mismatch");
    // check if is a function declaration
    if let Some(bb) = func.layout().bbs().front_node() {
      // setup the environment
      self.envs.push(Environment::new(
        func,
        func
          .params()
          .iter()
          .map(|p| func.dfg().value(*p) as *const ValueData)
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

  fn eval_bb(&mut self, bb: &BasicBlockNode) -> Result<Val> {
    // evaluate on all instructions
    for inst in bb.insts().keys() {
      let inst = func!(self).dfg().value(*inst);
      match inst.kind() {
        ValueKind::Alloc(_) => self.eval_alloc(inst),
        ValueKind::Load(v) => self.eval_load(inst, v)?,
        ValueKind::Store(v) => self.eval_store(v)?,
        ValueKind::GetPtr(v) => self.eval_getptr(inst, v)?,
        ValueKind::GetElemPtr(v) => self.eval_getelemptr(inst, v)?,
        ValueKind::Binary(v) => self.eval_binary(inst, v),
        ValueKind::Call(v) => self.eval_call(inst, v)?,
        ValueKind::Branch(v) => return self.eval_branch(v),
        ValueKind::Jump(v) => return self.eval_jump(v),
        ValueKind::Return(v) => return Ok(self.eval_return(v)),
        _ => panic!("invalid instruction"),
      }
    }
    unreachable!()
  }

  fn eval_alloc(&mut self, inst: &ValueData) {
    let base = match inst.ty().kind() {
      TypeKind::Pointer(base) => base,
      _ => panic!("invalid pointer type"),
    };
    let env = self.envs.last_mut().unwrap();
    env.allocs.push(Box::new(Self::new_zeroinit(base)));
    env
      .vals
      .insert(inst, Val::new_val_pointer(env.allocs.last()));
  }

  fn eval_load(&mut self, inst: &ValueData, load: &Load) -> Result<()> {
    let val = match self.eval_value(load.src()) {
      Val::Pointer { ptr, .. } => ptr.map(|p| unsafe { p.as_ref().clone() }),
      Val::UnsafePointer(ptr) => Val::load_from_unsafe_ptr(ptr, inst.ty()),
      _ => panic!("invalid pointer"),
    }
    .ok_or_else(|| new_error("accessing to null pointer"))?;
    self.insert_val(inst, val);
    Ok(())
  }

  fn eval_store(&self, store: &Store) -> Result<()> {
    let val = self.eval_value(store.value());
    match self.eval_value(store.dest()) {
      Val::Pointer { ptr, .. } => ptr
        .map(|p| unsafe { *p.as_ptr() = val })
        .ok_or_else(|| new_error("accessing to null pointer")),
      Val::UnsafePointer(ptr) => val.store_to_unsafe_ptr(ptr, value!(self, store.value()).ty()),
      _ => panic!("invalid pointer"),
    }
  }

  fn eval_getptr(&mut self, inst: &ValueData, gp: &GetPtr) -> Result<()> {
    // evaluate on index (offset)
    let offset = match self.eval_value(gp.index()) {
      Val::Int(i) => i as isize,
      _ => panic!("invalid index"),
    };
    // perform pointer calculation
    let base_size = match inst.ty().kind() {
      TypeKind::Pointer(base) => base.size(),
      _ => panic!("invalid pointer"),
    };
    let ptr = Self::get_pointer(self.eval_value(gp.src()), offset, base_size)?;
    self.insert_val(inst, ptr);
    Ok(())
  }

  fn eval_getelemptr(&mut self, inst: &ValueData, gep: &GetElemPtr) -> Result<()> {
    // evaluate on index (offset)
    let offset = match self.eval_value(gep.index()) {
      Val::Int(i) => i as isize,
      _ => panic!("invalid index"),
    };
    // perform pointer calculation
    let base_size = match inst.ty().kind() {
      TypeKind::Pointer(base) => base.size(),
      _ => panic!("invalid pointer"),
    };
    let ptr = match self.eval_value(gep.src()) {
      Val::Pointer { ptr, .. } => ptr
        .map(|p| match unsafe { p.as_ref() } {
          Val::Array(arr) => Self::get_pointer(Val::new_array_pointer(arr), offset, base_size),
          _ => panic!("invalid array"),
        })
        .ok_or_else(|| new_error("accessing to null pointer"))??,
      Val::UnsafePointer(ptr) => Val::UnsafePointer(ptr.map(|p| unsafe {
        NonNull::new_unchecked((p.as_ptr() as isize + base_size as isize * offset) as *mut ())
      })),
      _ => panic!("invalid pointer"),
    };
    self.insert_val(inst, ptr);
    Ok(())
  }

  fn eval_binary(&mut self, inst: &ValueData, bin: &Binary) {
    // evaluate lhs & rhs
    let lhs = self.eval_value(bin.lhs());
    let rhs = self.eval_value(bin.rhs());
    let (lv, rv) = match (lhs, rhs) {
      (Val::Int(lv), Val::Int(rv)) => (lv, rv),
      _ => panic!("invalid lhs or rhs"),
    };
    // perform binary operation
    let ans = match bin.op() {
      BinaryOp::NotEq => (lv != rv) as i32,
      BinaryOp::Eq => (lv == rv) as i32,
      BinaryOp::Gt => (lv > rv) as i32,
      BinaryOp::Lt => (lv < rv) as i32,
      BinaryOp::Ge => (lv >= rv) as i32,
      BinaryOp::Le => (lv <= rv) as i32,
      BinaryOp::Add => lv + rv,
      BinaryOp::Sub => lv - rv,
      BinaryOp::Mul => lv * rv,
      BinaryOp::Div => lv / rv,
      BinaryOp::Mod => lv % rv,
      BinaryOp::And => lv & rv,
      BinaryOp::Or => lv | rv,
      BinaryOp::Xor => lv ^ rv,
      BinaryOp::Shl => lv << rv,
      BinaryOp::Shr => ((lv as u32) >> rv) as i32,
      BinaryOp::Sar => lv >> rv,
    };
    self.insert_val(inst, Val::Int(ans));
  }

  fn eval_call(&mut self, inst: &ValueData, call: &Call) -> Result<()> {
    // evaluate arguments
    let args = call.args().iter().map(|u| self.eval_value(*u)).collect();
    // perform function call
    let ret = self.eval_func(self.program.func(call.callee()), args)?;
    self.insert_val(inst, ret);
    Ok(())
  }

  fn eval_branch(&mut self, br: &Branch) -> Result<Val> {
    // evaluate on condition
    let cond = self.eval_value(br.cond());
    // perform branching
    if cond.as_bool() {
      self.update_bb_params(br.true_bb(), br.true_args());
      self.eval_bb(bb_node!(self, br.true_bb()))
    } else {
      self.update_bb_params(br.false_bb(), br.false_args());
      self.eval_bb(bb_node!(self, br.false_bb()))
    }
  }

  fn eval_jump(&mut self, jump: &Jump) -> Result<Val> {
    self.update_bb_params(jump.target(), jump.args());
    self.eval_bb(bb_node!(self, jump.target()))
  }

  fn eval_return(&self, ret: &Return) -> Val {
    ret.value().map_or(Val::Undef, |v| self.eval_value(v))
  }

  fn eval_value(&self, value: Value) -> Val {
    if value.is_global() {
      let value = self.program.borrow_value(value);
      assert!(!value.kind().is_const());
      let v: *const ValueData = &value as &ValueData;
      self.vars.get(&v).unwrap().clone()
    } else {
      let value = value!(self, value);
      if value.kind().is_const() {
        self.eval_local_const(value)
      } else {
        let v: *const ValueData = value;
        self
          .vars
          .get(&v)
          .or_else(|| self.envs.last().unwrap().vals.get(&v))
          .unwrap()
          .clone()
      }
    }
  }

  fn insert_val(&mut self, inst: &ValueData, val: Val) {
    self.envs.last_mut().unwrap().vals.insert(inst, val);
  }

  fn update_bb_params(&mut self, bb: BasicBlock, args: &[Value]) {
    let bb = func!(self).dfg().bb(bb);
    for (param, arg) in bb.params().iter().zip(args.iter()) {
      self.insert_val(func!(self).dfg().value(*param), self.eval_value(*arg));
    }
  }
}

struct Environment<'a> {
  func: &'a FunctionData,
  allocs: Vec<Box<Val>>,
  vals: HashMap<*const ValueData, Val>,
}

impl<'a> Environment<'a> {
  fn new(func: &'a FunctionData, vals: HashMap<*const ValueData, Val>) -> Self {
    Self {
      func,
      allocs: Vec::new(),
      vals,
    }
  }
}

#[derive(Clone)]
pub enum Val {
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

  fn new_array_pointer(arr: &Box<[Val]>) -> Self {
    Self::Pointer {
      ptr: Some(unsafe { NonNull::new_unchecked(arr.as_ptr() as *mut Val) }),
      index: 0,
      len: arr.len(),
    }
  }

  fn load_from_unsafe_ptr(ptr: Option<NonNull<()>>, ty: &Type) -> Option<Self> {
    ptr.map(|p| match ty.kind() {
      TypeKind::Int32 => Val::Int(unsafe { *(p.as_ptr() as *const i32) }),
      TypeKind::Array(ty, len) => Val::Array(
        (0..*len)
          .map(|i| {
            Val::load_from_unsafe_ptr(
              Some(unsafe {
                NonNull::new_unchecked((p.as_ptr() as usize + ty.size() * i) as *mut ())
              }),
              ty,
            )
            .unwrap()
          })
          .collect::<Vec<_>>()
          .into_boxed_slice(),
      ),
      TypeKind::Pointer(_) => Val::UnsafePointer(NonNull::new(unsafe {
        *(p.as_ptr() as *const usize) as *mut ()
      })),
      _ => panic!("invalid type"),
    })
  }

  fn as_bool(&self) -> bool {
    matches!(self, Val::Int(i) if *i != 0)
  }

  fn store_to_unsafe_ptr(&self, ptr: Option<NonNull<()>>, ty: &Type) -> Result<()> {
    ptr
      .map(|p| match self {
        Val::Int(i) => {
          unsafe { *(p.as_ptr() as *mut i32) = *i };
          Ok(())
        }
        Val::Array(arr) => {
          let base = match ty.kind() {
            TypeKind::Array(base, _) => base,
            _ => panic!("invalid array type"),
          };
          arr.iter().enumerate().try_for_each(|(i, v)| {
            v.store_to_unsafe_ptr(
              Some(unsafe {
                NonNull::new_unchecked((p.as_ptr() as usize + base.size() * i) as *mut ())
              }),
              base,
            )
          })
        }
        Val::UnsafePointer(ptr) => {
          unsafe { *(p.as_ptr() as *mut *const ()) = ptr.map_or(null(), |p| p.as_ptr()) };
          Ok(())
        }
        _ => Err(new_error("incompatible type of value")),
      })
      .ok_or_else(|| new_error("accessing to null pointer"))?
  }
}
