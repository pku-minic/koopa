use super::ext_funcs::ExternFuncs;
use koopa::back::{NameManager, Visitor};
use koopa::ir::instructions::*;
use koopa::ir::{BasicBlock, Function, Program, Type, TypeKind, Value, ValueKind};
use koopa::value;
use std::collections::HashMap;
use std::io::{Error, ErrorKind, Result, Write};
use std::ptr::{null, NonNull};
use std::rc::Rc;

pub fn new_error(message: &str) -> Error {
  Error::new(ErrorKind::Other, message)
}

pub struct Interpreter {
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
          let val = Self::eval_const(value!(ga.init()));
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
}

impl Interpreter {
  pub fn new(ext_funcs: ExternFuncs) -> Self {
    Self {
      global_allocs: Vec::new(),
      vars: HashMap::new(),
      envs: Vec::new(),
      ext_funcs,
    }
  }

  fn eval_const(value: &Value) -> Val {
    match value.kind() {
      ValueKind::Integer(v) => Val::Int(v.value()),
      ValueKind::ZeroInit(_) => Self::new_zeroinit(value.ty()),
      ValueKind::Undef(_) => Val::Undef,
      ValueKind::Aggregate(v) => Val::Array(
        v.elems()
          .iter()
          .map(|e| Self::eval_const(value!(e)))
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

  fn eval_func(&mut self, func: &Function, args: Vec<Val>) -> Result<Val> {
    // check parameter count
    let param_len = match func.ty().kind() {
      TypeKind::Function(params, _) => params.len(),
      _ => panic!("invalid function"),
    };
    assert_eq!(param_len, args.len(), "parameter count mismatch");
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
        ValueKind::Alloc(_) => self.eval_alloc(inst),
        ValueKind::Load(v) => self.eval_load(inst, v)?,
        ValueKind::Store(v) => self.eval_store(v)?,
        ValueKind::GetPtr(v) => self.eval_getptr(inst, v)?,
        ValueKind::GetElemPtr(v) => self.eval_getelemptr(inst, v)?,
        ValueKind::Binary(v) => self.eval_binary(inst, v),
        ValueKind::Call(v) => self.eval_call(inst, v)?,
        ValueKind::Phi(v) => self.eval_phi(inst, v),
        ValueKind::Branch(v) => return self.eval_branch(bb, v),
        ValueKind::Jump(v) => return self.eval_jump(bb, v),
        ValueKind::Return(v) => return Ok(self.eval_return(v)),
        _ => panic!("invalid instruction"),
      }
    }
    unreachable!()
  }

  fn eval_alloc(&mut self, inst: &Value) {
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

  fn eval_load(&mut self, inst: &Value, load: &Load) -> Result<()> {
    let val = match self.eval_value(value!(load.src())) {
      Val::Pointer { ptr, .. } => ptr.map(|p| unsafe { p.as_ref().clone() }),
      Val::UnsafePointer(ptr) => Val::load_from_unsafe_ptr(ptr, inst.ty()),
      _ => panic!("invalid pointer"),
    }
    .ok_or_else(|| new_error("accessing to null pointer"))?;
    self.insert_val(inst, val);
    Ok(())
  }

  fn eval_store(&self, store: &Store) -> Result<()> {
    let val = self.eval_value(value!(store.value()));
    match self.eval_value(value!(store.dest())) {
      Val::Pointer { ptr, .. } => ptr
        .map(|p| unsafe { *p.as_ptr() = val })
        .ok_or_else(|| new_error("accessing to null pointer")),
      Val::UnsafePointer(ptr) => val.store_to_unsafe_ptr(ptr, value!(store.value()).ty()),
      _ => panic!("invalid pointer"),
    }
  }

  fn eval_getptr(&mut self, inst: &Value, gp: &GetPtr) -> Result<()> {
    // evaluate on index (offset)
    let offset = match self.eval_value(value!(gp.index())) {
      Val::Int(i) => i as isize,
      _ => panic!("invalid index"),
    };
    // perform pointer calculation
    let base_size = match inst.ty().kind() {
      TypeKind::Pointer(base) => base.size(),
      _ => panic!("invalid pointer"),
    };
    let ptr = Self::get_pointer(self.eval_value(value!(gp.src())), offset, base_size)?;
    self.insert_val(inst, ptr);
    Ok(())
  }

  fn eval_getelemptr(&mut self, inst: &Value, gep: &GetElemPtr) -> Result<()> {
    // evaluate on index (offset)
    let offset = match self.eval_value(value!(gep.index())) {
      Val::Int(i) => i as isize,
      _ => panic!("invalid index"),
    };
    // perform pointer calculation
    let base_size = match inst.ty().kind() {
      TypeKind::Pointer(base) => match base.kind() {
        TypeKind::Array(ty, _) => ty.size(),
        _ => panic!("invalid array pointer"),
      },
      _ => panic!("invalid pointer"),
    };
    let ptr = match self.eval_value(value!(gep.src())) {
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

  fn eval_binary(&mut self, inst: &Value, bin: &Binary) {
    // evaluate lhs & rhs
    let lhs = self.eval_value(value!(bin.lhs()));
    let rhs = self.eval_value(value!(bin.rhs()));
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

  fn eval_call(&mut self, inst: &Value, call: &Call) -> Result<()> {
    // evaluate arguments
    let args = call
      .args()
      .iter()
      .map(|u| self.eval_value(value!(u)))
      .collect();
    // perform function call
    let ret = self.eval_func(call.callee().upgrade().unwrap().as_ref(), args)?;
    self.insert_val(inst, ret);
    Ok(())
  }

  fn eval_phi(&mut self, inst: &Value, phi: &Phi) {
    let val = phi
      .oprs()
      .iter()
      .find_map(|(o, b)| {
        (self.envs.last().unwrap().last_bb == b.as_ptr()).then(|| self.eval_value(value!(o)))
      })
      .unwrap();
    self.insert_val(inst, val);
  }

  fn eval_branch(&mut self, cur_bb: &BasicBlock, br: &Branch) -> Result<Val> {
    // update last basic block
    self.envs.last_mut().unwrap().last_bb = cur_bb;
    // evaluate on condition
    let cond = self.eval_value(value!(br.cond()));
    // perform branching
    if cond.as_bool() {
      self.eval_bb(br.true_bb().upgrade().unwrap().as_ref())
    } else {
      self.eval_bb(br.false_bb().upgrade().unwrap().as_ref())
    }
  }

  fn eval_jump(&mut self, cur_bb: &BasicBlock, jump: &Jump) -> Result<Val> {
    // update last basic block
    self.envs.last_mut().unwrap().last_bb = cur_bb;
    // just jump
    self.eval_bb(jump.target().upgrade().unwrap().as_ref())
  }

  fn eval_return(&self, ret: &Return) -> Val {
    ret
      .value()
      .value()
      .map_or(Val::Undef, |v| self.eval_value(v.as_ref()))
  }

  fn eval_value(&self, value: &Value) -> Val {
    if value.is_const() {
      Self::eval_const(value)
    } else {
      let v = value as *const Value;
      self
        .vars
        .get(&v)
        .or_else(|| self.envs.last().unwrap().vals.get(&v))
        .unwrap()
        .clone()
    }
  }

  fn insert_val(&mut self, inst: &Value, val: Val) {
    self.envs.last_mut().unwrap().vals.insert(inst, val);
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
        Val::Int(i) => Ok(unsafe { *(p.as_ptr() as *mut i32) = *i }),
        Val::Array(arr) => {
          let base = match ty.kind() {
            TypeKind::Array(base, _) => base,
            _ => panic!("invalid array type"),
          };
          arr
            .iter()
            .enumerate()
            .map(|(i, v)| {
              v.store_to_unsafe_ptr(
                Some(unsafe {
                  NonNull::new_unchecked((p.as_ptr() as usize + base.size() * i) as *mut ())
                }),
                base,
              )
            })
            .collect()
        }
        Val::UnsafePointer(ptr) => {
          Ok(unsafe { *(p.as_ptr() as *mut *const ()) = ptr.map_or(null(), |p| p.as_ptr()) })
        }
        _ => Err(new_error("incompatible type of value")),
      })
      .ok_or_else(|| new_error("accessing to null pointer"))?
  }
}
