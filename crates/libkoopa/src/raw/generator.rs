use super::builder::Pointer;
use super::entities::*;
use crate::errors::ErrorCode;
use koopa::ir::builder_traits::*;
use koopa::ir::{BasicBlock, BinaryOp, Function, FunctionData, Program, Type, TypeKind, Value};
use std::collections::HashMap;
use std::ffi::CStr;
use std::marker::PhantomData;
use std::mem::replace;
use std::os::raw::c_char;
use std::ptr::null;

/// Result returned by raw program generator functions.
pub(crate) type Result<T> = std::result::Result<T, ErrorCode>;

/// Generates the given raw program to Koopa IR program.
pub(crate) fn generate_program(raw: &RawProgram) -> Result<Program> {
  let mut program = Program::new();
  raw.generate(&mut program, &mut ProgramInfo::new())?;
  Ok(program)
}

/// Information about the Koopa IR program.
struct ProgramInfo {
  values: HashMap<RawValue, Value>,
  funcs: HashMap<RawFunction, FunctionInfo>,
  cur_func: RawFunction,
}

impl ProgramInfo {
  /// Creates a new `ProgramInfo` structure.
  fn new() -> Self {
    ProgramInfo {
      values: HashMap::new(),
      funcs: HashMap::new(),
      cur_func: null(),
    }
  }

  /// Returns a reference to the information of the current function.
  fn cur_func_info(&self) -> &FunctionInfo {
    self.funcs.get(&self.cur_func).unwrap()
  }

  /// Returns a mutable reference to the information of the current function.
  fn cur_func_info_mut(&mut self) -> &mut FunctionInfo {
    self.funcs.get_mut(&self.cur_func).unwrap()
  }
}

/// Information about the Koopa IR function.
struct FunctionInfo {
  func: Function,
  bbs: HashMap<RawBasicBlock, BasicBlock>,
  values: HashMap<RawValue, Value>,
}

impl FunctionInfo {
  /// Creates a new `FunctionInfo` structure.
  fn new(func: Function, values: HashMap<RawValue, Value>) -> Self {
    Self {
      func,
      bbs: HashMap::new(),
      values,
    }
  }
}

/// Returns a local value builder of the current function.
macro_rules! builder {
  ($program:expr, $info:expr) => {
    $program
      .func_mut($info.cur_func_info().func)
      .dfg_mut()
      .new_value()
  };
}

/// Auto-select global/local value builder and build value.
macro_rules! build_value {
  ($program:expr, $info:expr, $builder:ident, $b:block) => {
    if $info.cur_func.is_null() {
      let $builder = $program.new_value();
      $b
    } else {
      let $builder = builder!($program, $info);
      $b
    }
  };
}

/// Iterator of raw slices.
struct RawSliceIter<'a, T: Pointer> {
  slice: &'a RawSlice,
  index: u32,
  phantom: PhantomData<T>,
}

impl<'a, T, E> RawSliceIter<'a, T>
where
  T: Pointer + GenerateOnRaw<Entity = E>,
{
  /// Generates a new collection of entities by this iterator.
  fn generate<C>(self, program: &mut Program, info: &mut ProgramInfo) -> Result<C>
  where
    C: FromIterator<E>,
  {
    self.map(|t| t.generate(program, info)).collect()
  }
}

impl<'a, T: Pointer> Iterator for RawSliceIter<'a, T> {
  type Item = T;

  fn next(&mut self) -> Option<Self::Item> {
    (self.index < self.slice.len).then(|| {
      let buffer = self.slice.buffer as *const *const ();
      let ptr = unsafe { *buffer.add(self.index as usize) };
      self.index += 1;
      T::from_ptr(ptr)
    })
  }
}

impl RawSlice {
  /// Returns an type iterator of this slice.
  fn types(&self) -> Result<RawSliceIter<RawType>> {
    match self.kind {
      RawSliceItemKind::Type => Ok(RawSliceIter::<RawType> {
        slice: self,
        index: 0,
        phantom: PhantomData,
      }),
      _ => Err(ErrorCode::RawSliceItemKindMismatch),
    }
  }

  /// Returns an function iterator of this slice.
  fn funcs(&self) -> Result<RawSliceIter<RawFunction>> {
    match self.kind {
      RawSliceItemKind::Function => Ok(RawSliceIter::<RawFunction> {
        slice: self,
        index: 0,
        phantom: PhantomData,
      }),
      _ => Err(ErrorCode::RawSliceItemKindMismatch),
    }
  }

  /// Returns an basic block iterator of this slice.
  fn bbs(&self) -> Result<RawSliceIter<RawBasicBlock>> {
    match self.kind {
      RawSliceItemKind::BasicBlock => Ok(RawSliceIter::<RawBasicBlock> {
        slice: self,
        index: 0,
        phantom: PhantomData,
      }),
      _ => Err(ErrorCode::RawSliceItemKindMismatch),
    }
  }

  /// Returns an value iterator of this slice.
  fn values(&self) -> Result<RawSliceIter<RawValue>> {
    match self.kind {
      RawSliceItemKind::Value => Ok(RawSliceIter::<RawValue> {
        slice: self,
        index: 0,
        phantom: PhantomData,
      }),
      _ => Err(ErrorCode::RawSliceItemKindMismatch),
    }
  }
}

/// Trait for generating on raw structures.
trait GenerateOnRaw {
  /// The type of generated entity.
  type Entity;

  /// Generates a new entity.
  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity>;
}

impl GenerateOnRaw for *const c_char {
  type Entity = Option<String>;

  fn generate(&self, _: &mut Program, _: &mut ProgramInfo) -> Result<Self::Entity> {
    (!self.is_null())
      .then(|| {
        unsafe { CStr::from_ptr(*self) }
          .to_str()
          .map(|s| s.into())
          .map_err(|_| ErrorCode::InvalidUtf8String)
      })
      .transpose()
  }
}

impl<'rpb> GenerateOnRaw for RawProgram<'rpb> {
  type Entity = ();

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    for value in self.values.values()? {
      value.generate(program, info)?;
    }
    for func in self.funcs.funcs()? {
      func.generate(program, info)?;
    }
    Ok(())
  }
}

impl GenerateOnRaw for RawType {
  type Entity = Type;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    Ok(match unsafe { &**self } {
      RawTypeKind::Int32 => Type::get_i32(),
      RawTypeKind::Unit => Type::get_unit(),
      RawTypeKind::Array(base, len) => Type::get_array(base.generate(program, info)?, *len),
      RawTypeKind::Pointer(base) => Type::get_pointer(base.generate(program, info)?),
      RawTypeKind::Function(params, ret) => Type::get_function(
        params.types()?.generate(program, info)?,
        ret.generate(program, info)?,
      ),
    })
  }
}

impl GenerateOnRaw for RawFunction {
  type Entity = Function;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    if let Some(f) = info.funcs.get(self) {
      Ok(f.func)
    } else {
      let raw = unsafe { &**self };
      // generate function name & type
      let name = raw.name.generate(program, info)?.unwrap_string()?;
      let (params, ret) = match raw.ty.generate(program, info)?.kind() {
        TypeKind::Function(params, ret) => (params.clone(), ret.clone()),
        _ => return Err(ErrorCode::TypeMismatch),
      };
      // generate function data
      let data = if raw.bbs.len == 0 {
        FunctionData::new_decl(name, params, ret)
      } else {
        if raw.params.len as usize != params.len() {
          return Err(ErrorCode::FuncParamNumMismatch);
        }
        let params = params
          .into_iter()
          .zip(raw.params.values()?)
          .map(|(ty, p)| Ok((unsafe { &*p }.name.generate(program, info)?, ty)))
          .collect::<Result<_>>()?;
        FunctionData::with_param_names(name, params, ret)
      };
      // generate function arguments
      let values = raw
        .params
        .values()?
        .zip(data.params().iter().copied())
        .collect();
      // insert to function map
      let func = program.new_func(data);
      info.funcs.insert(*self, FunctionInfo::new(func, values));
      // generate basic blocks
      if raw.bbs.len != 0 {
        let last_func = replace(&mut info.cur_func, *self);
        for bb in raw.bbs.bbs()? {
          bb.generate(program, info)?;
        }
        info.cur_func = last_func;
      }
      Ok(func)
    }
  }
}

impl GenerateOnRaw for RawBasicBlock {
  type Entity = BasicBlock;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    if let Some(b) = info.cur_func_info().bbs.get(self) {
      Ok(*b)
    } else {
      let raw = unsafe { &**self };
      // generate basic block name & parameters
      let name = raw.name.generate(program, info)?;
      let params = raw
        .params
        .values()?
        .map(|p| {
          let raw = unsafe { &*p };
          let name = raw.name.generate(program, info)?;
          Ok((name, raw.ty.generate(program, info)?))
        })
        .collect::<Result<_>>()?;
      // generate basic block
      let func_info = info.cur_func_info_mut();
      let func = program.func_mut(func_info.func);
      let bb = func
        .dfg_mut()
        .new_bb()
        .basic_block_with_param_names(name, params);
      func.layout_mut().bbs_mut().push_key_back(bb).unwrap();
      func_info.bbs.insert(*self, bb);
      // insert basic block parameters to value map
      let params = func.dfg().bb(bb).params();
      raw.params.values()?.zip(params).for_each(|(rp, p)| {
        func_info.values.insert(rp, *p);
      });
      // generate instructions
      for inst in raw.insts.values()? {
        let inst = inst.generate(program, info)?;
        // insert to the current basic block
        let layout = program.func_mut(info.cur_func_info().func).layout_mut();
        layout.bb_mut(bb).insts_mut().push_key_back(inst).unwrap();
      }
      Ok(bb)
    }
  }
}

impl GenerateOnRaw for RawValue {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    // try to find value in cache
    let value = info.values.get(self).or_else(|| {
      if info.cur_func.is_null() {
        None
      } else {
        info.cur_func_info().values.get(self)
      }
    });
    if let Some(v) = value {
      Ok(*v)
    } else {
      // generate value
      let raw = unsafe { &**self };
      let value = match &raw.kind {
        RawValueKind::Integer(v) => v.generate(program, info)?,
        RawValueKind::Aggregate(v) => v.generate(program, info)?,
        RawValueKind::FuncArgRef(_) => unreachable!("handled in `RawFunction`"),
        RawValueKind::BlockArgRef(_) => unreachable!("handled in `RawBasicBlock`"),
        RawValueKind::GlobalAlloc(v) => v.generate(program, info)?,
        RawValueKind::Load(v) => v.generate(program, info)?,
        RawValueKind::Store(v) => v.generate(program, info)?,
        RawValueKind::GetPtr(v) => v.generate(program, info)?,
        RawValueKind::GetElemPtr(v) => v.generate(program, info)?,
        RawValueKind::Binary(v) => v.generate(program, info)?,
        RawValueKind::Branch(v) => v.generate(program, info)?,
        RawValueKind::Jump(v) => v.generate(program, info)?,
        RawValueKind::Call(v) => v.generate(program, info)?,
        RawValueKind::Return(v) => v.generate(program, info)?,
        _ => {
          let ty = raw.ty.generate(program, info)?;
          match &raw.kind {
            RawValueKind::ZeroInit => build_value!(program, info, b, { b.zero_init(ty) }),
            RawValueKind::Undef => build_value!(program, info, b, { b.undef(ty) }),
            RawValueKind::Alloc => builder!(program, info).alloc(ty),
            _ => unreachable!(),
          }
        }
      };
      // set value name & insert value
      let name = raw.name.generate(program, info)?;
      if info.cur_func.is_null() {
        program.set_value_name(value, name);
        info.values.insert(*self, value);
      } else {
        let func_info = info.cur_func_info_mut();
        let func = program.func_mut(func_info.func);
        func.dfg_mut().set_value_name(value, name);
        func_info.values.insert(*self, value);
      }
      Ok(value)
    }
  }
}

impl GenerateOnRaw for RawInteger {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    Ok(build_value!(program, info, b, { b.integer(self.value) }))
  }
}

impl GenerateOnRaw for RawAggregate {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let elems = self.elems.values()?.generate(program, info)?;
    Ok(build_value!(program, info, b, { b.aggregate(elems) }))
  }
}

impl GenerateOnRaw for RawGlobalAlloc {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let init = self.init.generate(program, info)?;
    Ok(program.new_value().global_alloc(init))
  }
}

impl GenerateOnRaw for RawLoad {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let src = self.src.generate(program, info)?;
    Ok(builder!(program, info).load(src))
  }
}

impl GenerateOnRaw for RawStore {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let value = self.value.generate(program, info)?;
    let dest = self.dest.generate(program, info)?;
    Ok(builder!(program, info).store(value, dest))
  }
}

impl GenerateOnRaw for RawGetPtr {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let src = self.src.generate(program, info)?;
    let index = self.index.generate(program, info)?;
    Ok(builder!(program, info).get_ptr(src, index))
  }
}

impl GenerateOnRaw for RawGetElemPtr {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let src = self.src.generate(program, info)?;
    let index = self.index.generate(program, info)?;
    Ok(builder!(program, info).get_elem_ptr(src, index))
  }
}

impl GenerateOnRaw for RawBinary {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let op = match self.op {
      RawBinaryOp::NotEq => BinaryOp::NotEq,
      RawBinaryOp::Eq => BinaryOp::Eq,
      RawBinaryOp::Gt => BinaryOp::Gt,
      RawBinaryOp::Lt => BinaryOp::Lt,
      RawBinaryOp::Ge => BinaryOp::Ge,
      RawBinaryOp::Le => BinaryOp::Le,
      RawBinaryOp::Add => BinaryOp::Add,
      RawBinaryOp::Sub => BinaryOp::Sub,
      RawBinaryOp::Mul => BinaryOp::Mul,
      RawBinaryOp::Div => BinaryOp::Div,
      RawBinaryOp::Mod => BinaryOp::Mod,
      RawBinaryOp::And => BinaryOp::And,
      RawBinaryOp::Or => BinaryOp::Or,
      RawBinaryOp::Xor => BinaryOp::Xor,
      RawBinaryOp::Shl => BinaryOp::Shl,
      RawBinaryOp::Shr => BinaryOp::Shr,
      RawBinaryOp::Sar => BinaryOp::Sar,
    };
    let lhs = self.lhs.generate(program, info)?;
    let rhs = self.rhs.generate(program, info)?;
    Ok(builder!(program, info).binary(op, lhs, rhs))
  }
}

impl GenerateOnRaw for RawBranch {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let cond = self.cond.generate(program, info)?;
    let true_bb = self.true_bb.generate(program, info)?;
    let false_bb = self.false_bb.generate(program, info)?;
    let true_args = self.true_args.values()?.generate(program, info)?;
    let false_args = self.false_args.values()?.generate(program, info)?;
    Ok(builder!(program, info).branch_with_args(cond, true_bb, false_bb, true_args, false_args))
  }
}

impl GenerateOnRaw for RawJump {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let target = self.target.generate(program, info)?;
    let args = self.args.values()?.generate(program, info)?;
    Ok(builder!(program, info).jump_with_args(target, args))
  }
}

impl GenerateOnRaw for RawCall {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let callee = self.callee.generate(program, info)?;
    let args = self.args.values()?.generate(program, info)?;
    Ok(builder!(program, info).call(callee, args))
  }
}

impl GenerateOnRaw for RawReturn {
  type Entity = Value;

  fn generate(&self, program: &mut Program, info: &mut ProgramInfo) -> Result<Self::Entity> {
    let value = (!self.value.is_null())
      .then(|| self.value.generate(program, info))
      .transpose()?;
    Ok(builder!(program, info).ret(value))
  }
}

/// Trait for unwrapping [`Option<String>`]s.
trait UnwrapString {
  /// Unwraps an [`Option<String>`].
  /// Returns `NullPointerError` if this option is `None`.
  fn unwrap_string(self) -> Result<String>;
}

impl UnwrapString for Option<String> {
  fn unwrap_string(self) -> Result<String> {
    self.ok_or(ErrorCode::NullPointerError)
  }
}
