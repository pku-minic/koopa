use super::entities::*;
use crate::utils::new_uninit_box;
use koopa::ir::entities::{BasicBlockData, ValueData};
use koopa::ir::values::*;
use koopa::ir::{BasicBlock, Function, FunctionData, Program, Type, TypeKind};
use koopa::ir::{BinaryOp, Value, ValueKind};
use std::collections::HashMap;
use std::ffi::CString;
use std::os::raw::{c_char, c_void};
use std::ptr::null;

/// Raw builder that builds raw programs from Koopa IR programs.
#[derive(Default)]
pub struct RawProgramBuilder {
  slices: Vec<Vec<*const ()>>,
  strs: HashMap<String, CString>,
  tys: HashMap<Type, Box<RawTypeKind>>,
  funcs: HashMap<Function, Box<RawFunctionData>>,
  bbs: HashMap<BasicBlock, Box<RawBasicBlockData>>,
  values: HashMap<Value, Box<RawValueData>>,
}

impl RawProgramBuilder {
  /// Creates a new raw builder.
  pub fn new() -> Self {
    Self::default()
  }

  /// Builds on the given Koopa IR program.
  pub fn build_on(&mut self, program: &Program) -> RawProgram {
    let mut info = ProgramInfo::new(program);
    let raw = program.build(self, &mut info);
    // fill `used_by` fields of all values
    let slices: Vec<_> = self
      .values
      .keys()
      .map(|value| {
        let v: Vec<_> = info.value_used_by[value]
          .iter()
          .map(|v| self.values[v].as_ref() as RawValue as *const ())
          .collect();
        let slice = RawSlice {
          buffer: v.as_ptr() as *const c_void,
          len: v.len() as u32,
          kind: RawSliceItemKind::Value,
        };
        self.slices.push(v);
        slice
      })
      .collect();
    for (data, slice) in self.values.values_mut().zip(slices.into_iter()) {
      data.used_by = slice;
    }
    raw
  }
}

/// Some necessary information required by the [`BuildRaw`] trait.
struct ProgramInfo<'a> {
  program: &'a Program,
  cur_func: Option<&'a FunctionData>,
  cur_bb: Option<BasicBlock>,
  value_used_by: HashMap<Value, Vec<Value>>,
}

impl<'a> ProgramInfo<'a> {
  fn new(program: &'a Program) -> Self {
    Self {
      program,
      cur_func: None,
      cur_bb: None,
      value_used_by: HashMap::new(),
    }
  }
}

impl Default for RawSlice {
  fn default() -> Self {
    Self {
      buffer: null(),
      len: 0,
      kind: RawSliceItemKind::Unknown,
    }
  }
}

/// Converts an iterator to [`RawSlice`].
fn iter_into_raw<'a, I, T, R>(
  iter: I,
  builder: &mut RawProgramBuilder,
  info: &mut ProgramInfo,
) -> RawSlice
where
  I: Iterator<Item = &'a T>,
  T: 'a + BuildRaw<Raw = R>,
  R: Pointer,
{
  let v: Vec<_> = iter.map(|i| i.build(builder, info).into_any()).collect();
  let raw = RawSlice {
    buffer: v.as_ptr() as *const c_void,
    len: v.len() as u32,
    kind: T::KIND,
  };
  builder.slices.push(v);
  raw
}

/// Trait for building raw structures from Koopa IR entities.
trait BuildRaw {
  /// The type of builded raw structure.
  type Raw;

  /// Kind of the builded raw item.
  const KIND: RawSliceItemKind = RawSliceItemKind::Unknown;

  /// Builds a new raw structure.
  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw;
}

impl BuildRaw for str {
  type Raw = *const c_char;

  fn build(&self, builder: &mut RawProgramBuilder, _: &mut ProgramInfo) -> Self::Raw {
    if let Some(s) = builder.strs.get(self) {
      s.as_ptr()
    } else {
      let s = CString::new(self).expect("invalid string");
      let raw = s.as_ptr();
      builder.strs.insert(self.into(), s);
      raw
    }
  }
}

impl BuildRaw for String {
  type Raw = *const c_char;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    self.as_str().build(builder, info)
  }
}

impl<T, R> BuildRaw for Option<T>
where
  T: BuildRaw<Raw = R>,
  R: Pointer,
{
  type Raw = R;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    self.as_ref().map_or(R::NULL, |s| s.build(builder, info))
  }
}

impl<'a> BuildRaw for &'a Program {
  type Raw = RawProgram;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawProgram {
      values: iter_into_raw(self.inst_layout().iter(), builder, info),
      funcs: iter_into_raw(self.func_layout().iter(), builder, info),
    }
  }
}

impl BuildRaw for Type {
  type Raw = RawType;

  const KIND: RawSliceItemKind = RawSliceItemKind::Type;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    if let Some(t) = builder.tys.get(self) {
      t.as_ref()
    } else {
      let kind = Box::new(self.kind().build(builder, info));
      let raw = kind.as_ref() as RawType;
      builder.tys.insert(self.clone(), kind);
      raw
    }
  }
}

impl BuildRaw for TypeKind {
  type Raw = RawTypeKind;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    match self {
      TypeKind::Int32 => RawTypeKind::Int32,
      TypeKind::Unit => RawTypeKind::Unit,
      TypeKind::Array(base, len) => RawTypeKind::Array(base.build(builder, info), *len),
      TypeKind::Pointer(base) => RawTypeKind::Pointer(base.build(builder, info)),
      TypeKind::Function(params, ret) => RawTypeKind::Function(
        iter_into_raw(params.iter(), builder, info),
        ret.build(builder, info),
      ),
    }
  }
}

impl BuildRaw for Function {
  type Raw = RawFunction;

  const KIND: RawSliceItemKind = RawSliceItemKind::Function;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    if let Some(f) = builder.funcs.get(self) {
      f.as_ref()
    } else {
      builder.funcs.insert(*self, unsafe { new_uninit_box() });
      let func = info.program.func(*self);
      let last_func = info.cur_func.replace(func);
      let f = func.build(builder, info);
      info.cur_func = last_func;
      let fb = builder.funcs.get_mut(self).unwrap();
      **fb = f;
      fb.as_ref()
    }
  }
}

impl BuildRaw for FunctionData {
  type Raw = RawFunctionData;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawFunctionData {
      ty: self.ty().build(builder, info),
      name: self.name().build(builder, info),
      params: iter_into_raw(self.params().iter(), builder, info),
      bbs: iter_into_raw(self.layout().bbs().keys(), builder, info),
    }
  }
}

impl BuildRaw for BasicBlock {
  type Raw = RawBasicBlock;

  const KIND: RawSliceItemKind = RawSliceItemKind::BasicBlock;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    if let Some(b) = builder.bbs.get(self) {
      b.as_ref()
    } else {
      builder.bbs.insert(*self, unsafe { new_uninit_box() });
      let last_bb = info.cur_bb.replace(*self);
      let b = info.cur_func.unwrap().dfg().bb(*self).build(builder, info);
      info.cur_bb = last_bb;
      let bb = builder.bbs.get_mut(self).unwrap();
      **bb = b;
      bb.as_ref()
    }
  }
}

impl BuildRaw for BasicBlockData {
  type Raw = RawBasicBlockData;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawBasicBlockData {
      name: self.name().build(builder, info),
      params: iter_into_raw(self.params().iter(), builder, info),
      used_by: iter_into_raw(self.used_by().iter(), builder, info),
      insts: {
        let node = &info.cur_func.unwrap().layout().bbs()[&info.cur_bb.unwrap()];
        iter_into_raw(node.insts().keys(), builder, info)
      },
    }
  }
}

impl BuildRaw for Value {
  type Raw = RawValue;

  const KIND: RawSliceItemKind = RawSliceItemKind::Value;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    if let Some(v) = builder.values.get(self) {
      v.as_ref()
    } else {
      builder.values.insert(*self, unsafe { new_uninit_box() });
      let (v, used_by) = if self.is_global() {
        // get global value
        let value = info.program.borrow_value(*self);
        // get `used_by` list
        let used_by = value.used_by().iter().copied().collect();
        // build value
        (value.build(builder, info), used_by)
      } else {
        // get local value
        let func = info.cur_func.unwrap();
        let value = func.dfg().value(*self);
        // get `used_by` list
        let used_by = value.used_by().iter().copied().collect();
        // build value
        (value.build(builder, info), used_by)
      };
      // insert `used_by` list to info
      info.value_used_by.insert(*self, used_by);
      // store raw value data
      let vb = builder.values.get_mut(self).unwrap();
      **vb = v;
      vb.as_ref()
    }
  }
}

impl BuildRaw for ValueData {
  type Raw = RawValueData;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawValueData {
      ty: self.ty().build(builder, info),
      name: self.name().build(builder, info),
      used_by: RawSlice::default(),
      kind: self.kind().build(builder, info),
    }
  }
}

impl BuildRaw for ValueKind {
  type Raw = RawValueKind;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    match self {
      ValueKind::Integer(v) => RawValueKind::Integer(v.build(builder, info)),
      ValueKind::ZeroInit(_) => RawValueKind::ZeroInit,
      ValueKind::Undef(_) => RawValueKind::Undef,
      ValueKind::Aggregate(v) => RawValueKind::Aggregate(v.build(builder, info)),
      ValueKind::FuncArgRef(v) => RawValueKind::FuncArgRef(v.build(builder, info)),
      ValueKind::BlockArgRef(v) => RawValueKind::BlockArgRef(v.build(builder, info)),
      ValueKind::Alloc(_) => RawValueKind::Alloc,
      ValueKind::GlobalAlloc(v) => RawValueKind::GlobalAlloc(v.build(builder, info)),
      ValueKind::Load(v) => RawValueKind::Load(v.build(builder, info)),
      ValueKind::Store(v) => RawValueKind::Store(v.build(builder, info)),
      ValueKind::GetPtr(v) => RawValueKind::GetPtr(v.build(builder, info)),
      ValueKind::GetElemPtr(v) => RawValueKind::GetElemPtr(v.build(builder, info)),
      ValueKind::Binary(v) => RawValueKind::Binary(v.build(builder, info)),
      ValueKind::Branch(v) => RawValueKind::Branch(v.build(builder, info)),
      ValueKind::Jump(v) => RawValueKind::Jump(v.build(builder, info)),
      ValueKind::Call(v) => RawValueKind::Call(v.build(builder, info)),
      ValueKind::Return(v) => RawValueKind::Return(v.build(builder, info)),
    }
  }
}

impl BuildRaw for Integer {
  type Raw = RawInteger;

  fn build(&self, _: &mut RawProgramBuilder, _: &mut ProgramInfo) -> Self::Raw {
    RawInteger {
      value: self.value(),
    }
  }
}

impl BuildRaw for Aggregate {
  type Raw = RawAggregate;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawAggregate {
      elems: iter_into_raw(self.elems().iter(), builder, info),
    }
  }
}

impl BuildRaw for FuncArgRef {
  type Raw = RawFuncArgRef;

  fn build(&self, _: &mut RawProgramBuilder, _: &mut ProgramInfo) -> Self::Raw {
    RawFuncArgRef {
      index: self.index(),
    }
  }
}

impl BuildRaw for BlockArgRef {
  type Raw = RawBlockArgRef;

  fn build(&self, _: &mut RawProgramBuilder, _: &mut ProgramInfo) -> Self::Raw {
    RawBlockArgRef {
      index: self.index(),
    }
  }
}

impl BuildRaw for GlobalAlloc {
  type Raw = RawGlobalAlloc;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawGlobalAlloc {
      init: self.init().build(builder, info),
    }
  }
}

impl BuildRaw for Load {
  type Raw = RawLoad;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawLoad {
      src: self.src().build(builder, info),
    }
  }
}

impl BuildRaw for Store {
  type Raw = RawStore;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawStore {
      value: self.value().build(builder, info),
      dest: self.dest().build(builder, info),
    }
  }
}

impl BuildRaw for GetPtr {
  type Raw = RawGetPtr;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawGetPtr {
      src: self.src().build(builder, info),
      index: self.index().build(builder, info),
    }
  }
}

impl BuildRaw for GetElemPtr {
  type Raw = RawGetElemPtr;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawGetElemPtr {
      src: self.src().build(builder, info),
      index: self.index().build(builder, info),
    }
  }
}

impl BuildRaw for Binary {
  type Raw = RawBinary;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawBinary {
      op: match self.op() {
        BinaryOp::NotEq => RawBinaryOp::NotEq,
        BinaryOp::Eq => RawBinaryOp::Eq,
        BinaryOp::Gt => RawBinaryOp::Gt,
        BinaryOp::Lt => RawBinaryOp::Lt,
        BinaryOp::Ge => RawBinaryOp::Ge,
        BinaryOp::Le => RawBinaryOp::Le,
        BinaryOp::Add => RawBinaryOp::Add,
        BinaryOp::Sub => RawBinaryOp::Sub,
        BinaryOp::Mul => RawBinaryOp::Mul,
        BinaryOp::Div => RawBinaryOp::Div,
        BinaryOp::Mod => RawBinaryOp::Mod,
        BinaryOp::And => RawBinaryOp::And,
        BinaryOp::Or => RawBinaryOp::Or,
        BinaryOp::Xor => RawBinaryOp::Xor,
        BinaryOp::Shl => RawBinaryOp::Shl,
        BinaryOp::Shr => RawBinaryOp::Shr,
        BinaryOp::Sar => RawBinaryOp::Sar,
      },
      lhs: self.lhs().build(builder, info),
      rhs: self.rhs().build(builder, info),
    }
  }
}

impl BuildRaw for Branch {
  type Raw = RawBranch;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawBranch {
      cond: self.cond().build(builder, info),
      true_bb: self.true_bb().build(builder, info),
      false_bb: self.false_bb().build(builder, info),
      true_args: iter_into_raw(self.true_args().iter(), builder, info),
      false_args: iter_into_raw(self.false_args().iter(), builder, info),
    }
  }
}

impl BuildRaw for Jump {
  type Raw = RawJump;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawJump {
      target: self.target().build(builder, info),
      args: iter_into_raw(self.args().iter(), builder, info),
    }
  }
}

impl BuildRaw for Call {
  type Raw = RawCall;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawCall {
      callee: self.callee().build(builder, info),
      args: iter_into_raw(self.args().iter(), builder, info),
    }
  }
}

impl BuildRaw for Return {
  type Raw = RawReturn;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    RawReturn {
      value: self.value().build(builder, info),
    }
  }
}

/// Trait for pointer types.
pub(crate) trait Pointer {
  /// Null pointer of the current pointer.
  const NULL: Self;

  /// Converts the current pointer to `*const ()`.
  fn into_any(self) -> *const ();

  /// Converts the given pointer to the current pointer.
  fn from_ptr<T>(ptr: *const T) -> Self;
}

/// Implements [`Pointer`] trait for the given pointer type.
macro_rules! impl_pointer {
  ($ty:ty) => {
    impl Pointer for $ty {
      const NULL: Self = null();

      fn into_any(self) -> *const () {
        self as *const ()
      }

      fn from_ptr<T>(ptr: *const T) -> Self {
        ptr as Self
      }
    }
  };
}

impl_pointer!(*const c_char);
impl_pointer!(RawType);
impl_pointer!(RawFunction);
impl_pointer!(RawBasicBlock);
impl_pointer!(RawValue);
