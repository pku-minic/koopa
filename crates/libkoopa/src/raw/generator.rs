use super::builder::Pointer;
use super::entities::*;
use crate::errors::ErrorCode;
use koopa::ir::{BasicBlock, Function, Program, Type, Value};
use std::marker::PhantomData;

/// Result returned by raw program generator functions.
pub(crate) type Result<T> = std::result::Result<T, ErrorCode>;

/// Generates the given raw program to Koopa IR program.
pub(crate) fn generate_program(raw: &RawProgram) -> Result<Program> {
  let mut program = Program::new();
  raw.generate(&mut program)?;
  Ok(program)
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
  fn generate<C>(self, program: &mut Program) -> Result<C>
  where
    C: FromIterator<E>,
  {
    self.map(|t| t.generate(program)).collect()
  }
}

impl<'a, T: Pointer> Iterator for RawSliceIter<'a, T> {
  type Item = T;

  fn next(&mut self) -> Option<Self::Item> {
    (self.index < self.slice.len).then(|| {
      let buffer = self.slice.buffer as *const *const ();
      let ptr = unsafe { buffer.add(self.index as usize) };
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
  fn generate(&self, program: &mut Program) -> Result<Self::Entity>;
}

impl GenerateOnRaw for RawProgram {
  type Entity = ();

  fn generate(&self, program: &mut Program) -> Result<Self::Entity> {
    for value in self.values.values()? {
      value.generate(program)?;
    }
    for func in self.funcs.funcs()? {
      func.generate(program)?;
    }
    Ok(())
  }
}

impl GenerateOnRaw for RawType {
  type Entity = Type;

  fn generate(&self, program: &mut Program) -> Result<Self::Entity> {
    Ok(match unsafe { &**self } {
      RawTypeKind::Int32 => Type::get_i32(),
      RawTypeKind::Unit => Type::get_unit(),
      RawTypeKind::Array(base, len) => Type::get_array(base.generate(program)?, *len),
      RawTypeKind::Pointer(base) => Type::get_pointer(base.generate(program)?),
      RawTypeKind::Function(params, ret) => {
        Type::get_function(params.types()?.generate(program)?, ret.generate(program)?)
      }
    })
  }
}

impl GenerateOnRaw for RawFunction {
  type Entity = Function;

  fn generate(&self, program: &mut Program) -> Result<Self::Entity> {
    todo!()
  }
}

impl GenerateOnRaw for RawBasicBlock {
  type Entity = BasicBlock;

  fn generate(&self, program: &mut Program) -> Result<Self::Entity> {
    todo!()
  }
}

impl GenerateOnRaw for RawValue {
  type Entity = Value;

  fn generate(&self, program: &mut Program) -> Result<Self::Entity> {
    todo!()
  }
}
