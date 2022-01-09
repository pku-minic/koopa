use super::entities::*;
use crate::utils::new_uninit_box;
use koopa::ir::entities::{BasicBlockData, ValueData};
use koopa::ir::{BasicBlock, Function, FunctionData, Program, Type, TypeKind, Value, ValueKind};
use std::collections::HashMap;
use std::ffi::CString;
use std::os::raw::{c_char, c_void};
use std::ptr::null;

/// Raw builder can build raw programs from Koopa IR programs.
#[derive(Default)]
pub(crate) struct RawProgramBuilder {
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
    program.build(self, &mut ProgramInfo::new(program))
  }
}

/// Some necessary information required by the [`BuildRaw`] trait.
struct ProgramInfo<'a> {
  program: &'a Program,
  cur_func: Option<&'a FunctionData>,
  cur_bb: Option<BasicBlock>,
}

impl<'a> ProgramInfo<'a> {
  fn new(program: &'a Program) -> Self {
    Self {
      program,
      cur_func: None,
      cur_bb: None,
    }
  }
}

/// A general iterator for building [`RawSlice`]s.
struct Iter<'a, I: Iterator<Item = &'a T>, T: 'a>(I);

impl<'a, I, T> Iter<'a, I, T>
where
  I: Iterator<Item = &'a T>,
{
  fn new(iter: I) -> Self {
    Self(iter)
  }
}

impl<'a, I, T, R> Iter<'a, I, T>
where
  I: Iterator<Item = &'a T>,
  T: BuildRaw<Raw = R>,
  R: Pointer,
{
  fn into_raw(self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> RawSlice {
    let v: Vec<_> = self
      .0
      .map(|i| i.build(builder, info).as_any_ptr())
      .collect();
    let raw = RawSlice {
      buffer: v.as_ptr() as *const c_void,
      len: v.len() as u32,
      kind: T::KIND,
    };
    builder.slices.push(v);
    raw
  }
}

/// Trait for building raw structures from Koopa IR entities.
trait BuildRaw {
  /// The type of builded raw structure.
  type Raw;

  /// Kind of the builded raw item.
  const KIND: ItemKind = ItemKind::Unknown;

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
      values: Iter::new(self.inst_layout().iter()).into_raw(builder, info),
      funcs: Iter::new(self.func_layout().iter()).into_raw(builder, info),
    }
  }
}

impl BuildRaw for Type {
  type Raw = RawType;

  const KIND: ItemKind = ItemKind::Type;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    if let Some(t) = builder.tys.get(&self) {
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
        Iter::new(params.iter()).into_raw(builder, info),
        ret.build(builder, info),
      ),
    }
  }
}

impl BuildRaw for Function {
  type Raw = RawFunction;

  const KIND: ItemKind = ItemKind::Function;

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
      params: Iter::new(self.params().iter()).into_raw(builder, info),
      bbs: Iter::new(self.layout().bbs().keys()).into_raw(builder, info),
    }
  }
}

impl BuildRaw for BasicBlock {
  type Raw = RawBasicBlock;

  const KIND: ItemKind = ItemKind::BasicBlock;

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
      params: Iter::new(self.params().iter()).into_raw(builder, info),
      used_by: Iter::new(self.used_by().iter()).into_raw(builder, info),
      insts: {
        let node = &info.cur_func.unwrap().layout().bbs()[&info.cur_bb.unwrap()];
        Iter::new(node.insts().keys()).into_raw(builder, info)
      },
    }
  }
}

impl BuildRaw for Value {
  type Raw = RawValue;

  const KIND: ItemKind = ItemKind::Value;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    if let Some(v) = builder.values.get(self) {
      v.as_ref()
    } else {
      builder.values.insert(*self, unsafe { new_uninit_box() });
      let func = info.cur_func.unwrap();
      let v = func.dfg().value(*self).build(builder, info);
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
      used_by: Iter::new(self.used_by().iter()).into_raw(builder, info),
      kind: self.kind().build(builder, info),
    }
  }
}

impl BuildRaw for ValueKind {
  type Raw = RawValueKind;

  fn build(&self, builder: &mut RawProgramBuilder, info: &mut ProgramInfo) -> Self::Raw {
    todo!()
  }
}

/// Trait for pointer types.
trait Pointer {
  /// Null pointer of the current pointer.
  const NULL: Self;

  /// Converts the current pointer to `*const ()`.
  fn as_any_ptr(self) -> *const ();
}

/// Implements [`Pointer`] trait for the given pointer type.
macro_rules! impl_pointer {
  ($ty:ty) => {
    impl Pointer for $ty {
      const NULL: Self = null();

      fn as_any_ptr(self) -> *const () {
        self as *const ()
      }
    }
  };
}

impl_pointer!(*const c_char);
impl_pointer!(RawType);
impl_pointer!(RawFunction);
impl_pointer!(RawBasicBlock);
impl_pointer!(RawValue);
