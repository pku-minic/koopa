use super::ext_funcs::ExternFuncs;
use koopa::back::{NameManager, Visitor};
use koopa::ir::entities::ValueData;
use koopa::ir::layout::BasicBlockNode;
use koopa::ir::values::*;
use koopa::ir::{BasicBlock, BinaryOp, FunctionData, Program, Type, TypeKind, Value, ValueKind};
use std::alloc::{Layout, alloc_zeroed, dealloc, handle_alloc_error};
use std::collections::HashMap;
use std::io::{Error, Result, Write};
use std::ptr::{NonNull, null};

pub fn new_error(message: &str) -> Error {
  Error::other(message)
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
  global_allocs: Vec<Allocation>,
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
    if Type::get_pointer(Type::get_i32()).size() != size_of::<*mut ()>() {
      return Err(new_error("interpreter requires the host pointer size"));
    }
    // evaluate all global variables
    for var in self.program.inst_layout() {
      let value = self.program.borrow_value(*var);
      let ValueKind::GlobalAlloc(ga) = value.kind() else {
        panic!("invalid global variable");
      };
      let val = self.eval_global_const(&self.program.borrow_value(ga.init()));
      let ty = self.program.borrow_value(ga.init()).ty().clone();
      let allocation = Allocation::new(&ty)?;
      val.store_to_unsafe_ptr(Some(allocation.ptr), &ty)?;
      self.vars.insert(&value as &ValueData, allocation.value());
      self.global_allocs.push(allocation);
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
    let byte_offset = isize::try_from(base_size)
      .ok()
      .and_then(|size| size.checked_mul(offset))
      .ok_or_else(|| new_error("pointer offset overflow"))?;
    let offset_pointer = |ptr: Option<NonNull<()>>| {
      ptr.and_then(|p| NonNull::new(p.as_ptr().cast::<u8>().wrapping_offset(byte_offset).cast()))
    };
    match src {
      Val::Pointer { ptr, index, len } => {
        let new_index = index.checked_add_signed(offset);
        match new_index {
          Some(new_index) if new_index < len => Ok(Val::Pointer {
            ptr: offset_pointer(ptr),
            index: new_index,
            len,
          }),
          _ => Err(new_error(&format!(
            "pointer calculation out of bounds with index {index}, offset {offset} and length {len}"
          ))),
        }
      }
      Val::UnsafePointer(ptr) => Ok(Val::UnsafePointer(offset_pointer(ptr))),
      _ => panic!("invalid pointer"),
    }
  }

  fn eval_func(&mut self, func: &'a FunctionData, args: Vec<Val>) -> Result<Val> {
    // check parameter count
    let TypeKind::Function(params, _) = func.ty().kind() else {
      panic!("invalid function");
    };
    assert_eq!(params.len(), args.len(), "parameter count mismatch");
    // check if is a function declaration
    if let Some(bb) = func.layout().bbs().front_node() {
      // setup the environment
      self.envs.push(Environment::new(
        func,
        func
          .params()
          .iter()
          .map(|p| func.dfg().value(*p) as *const ValueData)
          .zip(args)
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

  fn eval_bb(&mut self, mut bb: &'a BasicBlockNode) -> Result<Val> {
    // A control-flow edge stays in the same activation. Do not consume a
    // Rust stack frame per iteration of an interpreted loop.
    'blocks: loop {
      for inst in bb.insts().keys() {
        let inst = func!(self).dfg().value(*inst);
        match inst.kind() {
          ValueKind::Alloc(_) => self.eval_alloc(inst)?,
          ValueKind::Load(v) => self.eval_load(inst, v)?,
          ValueKind::Store(v) => self.eval_store(v)?,
          ValueKind::GetPtr(v) => self.eval_getptr(inst, v)?,
          ValueKind::GetElemPtr(v) => self.eval_getelemptr(inst, v)?,
          ValueKind::Binary(v) => self.eval_binary(inst, v),
          ValueKind::Call(v) => self.eval_call(inst, v)?,
          ValueKind::Branch(v) => {
            let target = self.eval_branch(v);
            bb = bb_node!(self, target);
            continue 'blocks;
          }
          ValueKind::Jump(v) => {
            self.update_bb_params(v.target(), v.args());
            bb = bb_node!(self, v.target());
            continue 'blocks;
          }
          ValueKind::Return(v) => return Ok(self.eval_return(v)),
          _ => panic!("invalid instruction"),
        }
      }
      unreachable!()
    }
  }

  fn eval_alloc(&mut self, inst: &ValueData) -> Result<()> {
    let TypeKind::Pointer(base) = inst.ty().kind() else {
      panic!("invalid pointer type");
    };
    let allocation = Allocation::new(base)?;
    let env = self.envs.last_mut().unwrap();
    env.vals.insert(inst, allocation.value());
    env.allocs.push(allocation);
    Ok(())
  }

  fn eval_load(&mut self, inst: &ValueData, load: &Load) -> Result<()> {
    let (Val::Pointer { ptr, .. } | Val::UnsafePointer(ptr)) = self.eval_value(load.src()) else {
      panic!("invalid pointer");
    };
    let val = Val::load_from_unsafe_ptr(ptr, inst.ty())
      .ok_or_else(|| new_error("accessing to null pointer"))?;
    self.insert_val(inst, val);
    Ok(())
  }

  fn eval_store(&self, store: &Store) -> Result<()> {
    let val = self.eval_value(store.value());
    let (Val::Pointer { ptr, .. } | Val::UnsafePointer(ptr)) = self.eval_value(store.dest()) else {
      panic!("invalid pointer");
    };
    val.store_to_unsafe_ptr(ptr, &self.value_type(store.value()))
  }

  fn value_type(&self, value: Value) -> Type {
    if value.is_global() {
      self.program.borrow_value(value).ty().clone()
    } else {
      value!(self, value).ty().clone()
    }
  }

  fn eval_getptr(&mut self, inst: &ValueData, gp: &GetPtr) -> Result<()> {
    // evaluate on index (offset)
    let Val::Int(offset) = self.eval_value(gp.index()) else {
      panic!("invalid index");
    };
    // perform pointer calculation
    let TypeKind::Pointer(base) = inst.ty().kind() else {
      panic!("invalid pointer");
    };
    let base_size = base.size();
    let ptr = Self::get_pointer(self.eval_value(gp.src()), offset as isize, base_size)?;
    self.insert_val(inst, ptr);
    Ok(())
  }

  fn eval_getelemptr(&mut self, inst: &ValueData, gep: &GetElemPtr) -> Result<()> {
    // evaluate on index (offset)
    let Val::Int(offset) = self.eval_value(gep.index()) else {
      panic!("invalid index");
    };
    let offset = offset as isize;
    // perform pointer calculation
    let TypeKind::Pointer(base) = inst.ty().kind() else {
      panic!("invalid pointer");
    };
    let base_size = base.size();
    let ptr = match self.eval_value(gep.src()) {
      Val::Pointer { ptr, .. } => {
        if ptr.is_none() {
          return Err(new_error("accessing to null pointer"));
        }
        let src_ty = self.value_type(gep.src());
        let TypeKind::Pointer(array_ty) = src_ty.kind() else {
          panic!("invalid pointer type");
        };
        let &TypeKind::Array(_, len) = array_ty.kind() else {
          panic!("invalid array type");
        };
        Self::get_pointer(Val::Pointer { ptr, index: 0, len }, offset, base_size)?
      }
      pointer @ Val::UnsafePointer(_) => Self::get_pointer(pointer, offset, base_size)?,
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
      (Val::Undef, _) | (_, Val::Undef) => {
        self.insert_val(inst, Val::Undef);
        return;
      }
      _ => panic!("invalid lhs or rhs"),
    };
    // perform binary operation
    let ans = match bin.op() {
      BinaryOp::NotEq => Some((lv != rv) as i32),
      BinaryOp::Eq => Some((lv == rv) as i32),
      BinaryOp::Gt => Some((lv > rv) as i32),
      BinaryOp::Lt => Some((lv < rv) as i32),
      BinaryOp::Ge => Some((lv >= rv) as i32),
      BinaryOp::Le => Some((lv <= rv) as i32),
      BinaryOp::Add => Some(lv.wrapping_add(rv)),
      BinaryOp::Sub => Some(lv.wrapping_sub(rv)),
      BinaryOp::Mul => Some(lv.wrapping_mul(rv)),
      BinaryOp::Div => lv.checked_div(rv),
      BinaryOp::Mod => lv.checked_rem(rv),
      BinaryOp::And => Some(lv & rv),
      BinaryOp::Or => Some(lv | rv),
      BinaryOp::Xor => Some(lv ^ rv),
      BinaryOp::Shl => lv.checked_shl(rv as u32),
      BinaryOp::Shr => (lv as u32).checked_shr(rv as u32).map(|v| v as i32),
      BinaryOp::Sar => lv.checked_shr(rv as u32),
    };
    self.insert_val(inst, ans.map_or(Val::Undef, Val::Int));
  }

  fn eval_call(&mut self, inst: &ValueData, call: &Call) -> Result<()> {
    // evaluate arguments
    let args = call.args().iter().map(|u| self.eval_value(*u)).collect();
    // perform function call
    let ret = self.eval_func(self.program.func(call.callee()), args)?;
    self.insert_val(inst, ret);
    Ok(())
  }

  fn eval_branch(&mut self, br: &Branch) -> BasicBlock {
    let (target, args) = if self.eval_value(br.cond()).as_bool() {
      (br.true_bb(), br.true_args())
    } else {
      (br.false_bb(), br.false_args())
    };
    self.update_bb_params(target, args);
    target
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
    // All incoming arguments refer to the environment before the transfer.
    // In particular, a loop back edge may permute its own block parameters.
    let args: Vec<_> = args.iter().map(|arg| self.eval_value(*arg)).collect();
    let bb = func!(self).dfg().bb(bb);
    for (param, arg) in bb.params().iter().zip(args) {
      self.insert_val(func!(self).dfg().value(*param), arg);
    }
  }
}

// Memory visible to native functions must have the target's actual scalar and
// contiguous array layout, never the layout of the interpreter's Val enum.
struct Allocation {
  ptr: NonNull<()>,
  layout: Layout,
}

impl Allocation {
  fn new(ty: &Type) -> Result<Self> {
    let layout = Layout::from_size_align(ty.size().max(1), align_of::<usize>())
      .map_err(|_| new_error("invalid allocation size"))?;
    let ptr = NonNull::new(unsafe { alloc_zeroed(layout) })
      .unwrap_or_else(|| handle_alloc_error(layout))
      .cast();
    Ok(Self { ptr, layout })
  }

  fn value(&self) -> Val {
    Val::new_val_pointer(Some(self.ptr))
  }
}

impl Drop for Allocation {
  fn drop(&mut self) {
    unsafe { dealloc(self.ptr.as_ptr().cast(), self.layout) };
  }
}

struct Environment<'a> {
  func: &'a FunctionData,
  allocs: Vec<Allocation>,
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
    ptr: Option<NonNull<()>>,
    // if the pointer points to an array element,
    // the index and the total length of the parent array are recorded
    // in case of an out-of-bounds access
    index: usize,
    len: usize,
  },
  UnsafePointer(Option<NonNull<()>>),
}

impl Val {
  fn new_val_pointer(ptr: Option<NonNull<()>>) -> Self {
    Self::Pointer {
      ptr,
      index: 0,
      len: usize::from(ptr.is_some()),
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
                NonNull::new_unchecked(p.as_ptr().cast::<u8>().add(ty.size() * i).cast())
              }),
              ty,
            )
            .unwrap()
          })
          .collect::<Vec<_>>()
          .into_boxed_slice(),
      ),
      TypeKind::Pointer(_) => {
        Val::UnsafePointer(NonNull::new(unsafe { *p.as_ptr().cast::<*mut ()>() }))
      }
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
          let TypeKind::Array(base, _) = ty.kind() else {
            panic!("invalid array type");
          };
          arr.iter().enumerate().try_for_each(|(i, v)| {
            v.store_to_unsafe_ptr(
              Some(unsafe {
                NonNull::new_unchecked(p.as_ptr().cast::<u8>().add(base.size() * i).cast())
              }),
              base,
            )
          })
        }
        Val::Pointer { ptr, .. } | Val::UnsafePointer(ptr) => {
          unsafe { *p.as_ptr().cast::<*const ()>() = ptr.map_or(null(), |p| p.as_ptr()) };
          Ok(())
        }
        Val::Undef => {
          // Choose zero for an unspecified initial value, just like local alloc.
          unsafe { p.as_ptr().cast::<u8>().write_bytes(0, ty.size()) };
          Ok(())
        }
      })
      .ok_or_else(|| new_error("accessing to null pointer"))?
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use koopa::back::Generator;
  use koopa::front::Driver;
  use std::io::sink;

  fn run(source: &str) -> Result<i32> {
    let program = Driver::from(source).generate_program().unwrap();
    Generator::with_visitor(sink(), Interpreter::new(Vec::new())).generate_on(&program)
  }

  #[test]
  fn block_arguments_are_assigned_in_parallel() {
    for transfer in [
      "jump %loop(%b, %a, %next)",
      "br 1, %loop(%b, %a, %next), %exit",
      "br 0, %exit, %loop(%b, %a, %next)",
    ] {
      let source = format!(
        "fun @main(): i32 {{
        %entry:
          jump %loop(1, 2, 0)
        %loop(%a: i32, %b: i32, %n: i32):
          %cond = lt %n, 1
          br %cond, %body, %exit
        %body:
          %next = add %n, 1
          {transfer}
        %exit:
          ret %b
        }}"
      );
      assert_eq!(run(&source).unwrap(), 1);
    }
  }

  #[test]
  fn long_loops_do_not_consume_the_host_stack() {
    let iterations = if cfg!(miri) { 32 } else { 100_000 };
    let source = format!(
      "fun @main(): i32 {{
      %entry:
        jump %loop(0)
      %loop(%i: i32):
        %next = add %i, 1
        %cond = lt %next, {iterations}
        br %cond, %body, %exit
      %body:
        jump %loop(%next)
      %exit:
        ret %next
      }}"
    );
    assert_eq!(run(&source).unwrap(), iterations);
  }

  #[test]
  fn integer_operations_match_i32_and_undefined_ir_semantics() {
    for (expression, expected) in [
      ("add 2147483647, 1", Some(i32::MIN)),
      ("sub -2147483648, 1", Some(i32::MAX)),
      ("mul 1073741824, 4", Some(0)),
      ("div 1, 0", None),
      ("div -2147483648, -1", None),
      ("mod -2147483648, -1", None),
      ("shl 1, 32", None),
      ("shr 1, -1", None),
      ("sar 1, 32", None),
      ("add undef, 1", None),
      ("add 1, undef", None),
    ] {
      let source = format!("fun @main(): i32 {{ %entry: %result = {expression} ret %result }}");
      let result = run(&source);
      if let Some(expected) = expected {
        assert_eq!(result.unwrap(), expected);
      } else {
        // An undefined result cannot be returned as the interpreter exit code.
        assert!(result.is_err(), "{expression}");
      }
    }
    assert_eq!(
      run("fun @main(): i32 { %entry: %unused = add undef, 1 ret 42 }").unwrap(),
      42
    );
  }

  #[test]
  fn zero_offset_preserves_scalar_and_array_allocation_pointers() {
    assert_eq!(
      run(
        "global @g = alloc i32, 40
        fun @main(): i32 {
        %entry:
          %local = alloc [i32, 1]
          %array = getptr %local, 0
          %element = getelemptr %array, 0
          store 2, %element
          %global = getptr @g, 0
          %a = load %global
          %b = load %element
          %sum = add %a, %b
          ret %sum
        }"
      )
      .unwrap(),
      42
    );
  }

  #[test]
  fn native_storage_preserves_pointer_and_aggregate_loads() {
    assert_eq!(
      run(
        "global @g = alloc [[i32, 2], 2], {{1, 2}, {3, 4}}
      global @pointer = alloc *i32, zeroinit
      fun @main(): i32 {
      %entry:
        %copy = alloc [[i32, 2], 2]
        %array = load @g
        store %array, %copy
        %row = getelemptr %copy, 1
        %element = getelemptr %row, 0
        store %element, @pointer
        %loaded = load @pointer
        store 42, %loaded
        %answer = load %element
        ret %answer
      }"
      )
      .unwrap(),
      42
    );
  }

  #[cfg(not(miri))]
  #[test]
  fn native_calls_share_multidimensional_storage_and_pointer_aliases() {
    unsafe extern "C" fn mutate(
      matrix: *mut [i32; 3],
      alias: *mut i32,
      out: *mut *mut i32,
    ) -> *mut i32 {
      unsafe {
        let first = matrix.cast::<i32>();
        if first.add(4) != alias || *first.add(5) != 6 {
          return std::ptr::null_mut();
        }
        *first = 9;
        *alias = 30;
        *out = alias;
        alias
      }
    }
    let program = Driver::from(
      "global @g = alloc [[i32, 3], 2], {{1, 2, 3}, {4, 5, 6}}
      decl @mutate(*[i32, 3], *i32, **i32): *i32
      fun @main(): i32 {
      %entry:
        %out = alloc *i32
        %first_row = getelemptr @g, 0
        %second_row = getelemptr @g, 1
        %alias = getelemptr %second_row, 1
        %returned = call @mutate(%first_row, %alias, %out)
        %before = load %alias
        %changed = add %before, 3
        store %changed, %returned
        %out_pointer = load %out
        %a = load %out_pointer
        %first = getelemptr %first_row, 0
        %b = load %first
        %sum = add %a, %b
        ret %sum
      }",
    )
    .generate_program()
    .unwrap();
    let externs = ExternFuncs::with_test_symbols(vec![("mutate", mutate as *const ())]);
    assert_eq!(
      InterpreterImpl::new(&program, externs).interpret().unwrap(),
      42
    );
  }
}
