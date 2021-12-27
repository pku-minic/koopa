// TODO: cursor on function (layout)

use crate::ir::dfg::DataFlowGraph;
use crate::ir::entities::{BasicBlock, Function, Value, ValueData};
use crate::ir::types::{Type, TypeKind};
use crate::ir::values::*;

pub trait EntityBuilder: Sized {
  /// Returns the type information of the given value.
  ///
  /// # Panics
  ///
  /// Panics if the given value does not exist.
  fn value_type(&self, value: Value) -> Type;

  /// Returns the type information of the given basic block.
  ///
  /// # Panics
  ///
  /// Panics if the given basic block does not exist.
  fn bb_type(&self, bb: BasicBlock) -> Type;

  /// Returns the type information of the given function.
  ///
  /// # Panics
  ///
  /// Panics if the given function does not exist.
  fn func_type(&self, func: Function) -> Type;

  /// Checks if the given value is a constant.
  ///
  /// # Panics
  ///
  /// Panics if the given value does not exist.
  fn is_const(&self, value: Value) -> bool;

  /// Inserts the specific data to the data flow graph,
  /// returns the handle of the inserted value.
  fn insert(self, data: ValueData) -> Value;

  /// Create a new integer constant.
  ///
  /// The type of the created `Integer` will be integer type.
  fn integer(self, value: i32) -> Value {
    self.insert(Integer::new_data(value))
  }

  /// Create a new zero initializer.
  ///
  /// # Panics
  ///
  /// Panics if the given type is an unit type.
  fn zero_init(self, ty: Type) -> Value {
    assert!(!ty.is_unit(), "`ty` can not be unit");
    self.insert(ZeroInit::new_data(ty))
  }

  /// Create a new undefined value.
  ///
  /// # Panics
  ///
  /// Panics if the given type is an unit type.
  fn undef(self, ty: Type) -> Value {
    assert!(!ty.is_unit(), "`ty` can not be unit");
    self.insert(Undef::new_data(ty))
  }

  /// Creates an aggregate constant with elements `elems`.
  ///
  /// # Panics
  ///
  /// Panics if:
  ///
  /// * No elements are provided.
  /// * Presence of non-constant elements or unit type elements.
  /// * Elements have different types.
  fn aggregate(self, elems: Vec<Value>) -> Value {
    // element list should not be empty
    assert!(!elems.is_empty(), "`elems` must not be empty");
    // check if all elements are constant
    assert!(
      elems.iter().all(|e| self.is_const(*e)),
      "`elems` must all be constants"
    );
    // check if all elements have the same type
    assert!(
      elems
        .windows(2)
        .all(|e| self.value_type(e[0]) == self.value_type(e[1])),
      "type mismatch in `elems`"
    );
    // check base type
    let base = self.value_type(elems[0]);
    assert!(!base.is_unit(), "base type must not be `unit`");
    // create array type
    let ty = Type::get_array(base, elems.len());
    self.insert(Aggregate::new_data(elems, ty))
  }

  /// Creates a function argument reference with the given index.
  ///
  /// # Panics
  ///
  /// Panics if the given type is an unit type.
  fn func_arg_ref(self, index: usize, ty: Type) -> Value {
    assert!(!ty.is_unit(), "`ty` can not be unit");
    self.insert(FuncArgRef::new_data(index, ty))
  }

  /// Creates a basic block argument reference with the given index.
  ///
  /// # Panics
  ///
  /// Panics if the given type is an unit type.
  fn block_arg_ref(self, index: usize, ty: Type) -> Value {
    assert!(!ty.is_unit(), "`ty` can not be unit");
    self.insert(BlockArgRef::new_data(index, ty))
  }

  /// Creates a local memory allocation.
  ///
  /// # Panics
  ///
  /// Panics if the given type is an unit type.
  fn alloc(self, ty: Type) -> Value {
    assert!(!ty.is_unit(), "`ty` can not be unit");
    self.insert(Alloc::new_data(ty))
  }

  /// Creates a global memory allocation.
  ///
  /// # Panics
  ///
  /// Panics if the type of the initialize is an unit type.
  fn global_alloc(self, init: Value) -> Value {
    let init_ty = self.value_type(init);
    assert!(!init_ty.is_unit(), "the type of `init` must not be unit");
    let ty = Type::get_pointer(init_ty);
    self.insert(GlobalAlloc::new_data(init, ty))
  }

  /// Creates a memory load with the given source.
  ///
  /// # Panics
  ///
  /// Panics if the type of the source value is not a pointer type.
  fn load(self, src: Value) -> Value {
    let src_ty = self.value_type(src);
    let ty = match src_ty.kind() {
      TypeKind::Pointer(ty) => ty.clone(),
      _ => panic!("expected a pointer type"),
    };
    self.insert(Load::new_data(src, ty))
  }

  /// Creates a memory store with the given value and destination.
  ///
  /// # Panics
  ///
  /// Panics if the dest type is not a pointer of the value type.
  fn store(self, value: Value, dest: Value) -> Value {
    assert!(
      Type::get_pointer(self.value_type(value)) == self.value_type(dest),
      "the type of `dest` must be the pointer of `value`'s type"
    );
    self.insert(Store::new_data(value, dest))
  }

  /// Creates a pointer calculation with the given source pointer and index.
  ///
  /// # Panics
  ///
  /// Panics if the source type is not a pointer type, or the index type is
  /// not an integer type.
  fn get_ptr(self, src: Value, index: Value) -> Value {
    let src_ty = self.value_type(src);
    assert!(
      matches!(src_ty.kind(), TypeKind::Pointer(..)),
      "`src` must be a pointer"
    );
    assert!(
      self.value_type(index).is_i32(),
      "`index` must be an integer"
    );
    self.insert(GetPtr::new_data(src, index, src_ty))
  }

  /// Creates a element pointer calculation with the given source pointer
  /// and index.
  ///
  /// # Panics
  ///
  /// Panics if the source type is not a pointer type of an array, or the
  /// index type is not an integer type.
  fn get_elem_ptr(self, src: Value, index: Value) -> Value {
    assert!(
      self.value_type(index).is_i32(),
      "`index` must be an integer"
    );
    let ty = match self.value_type(src).kind() {
      TypeKind::Pointer(ty) => match ty.kind() {
        TypeKind::Array(base, _) => Type::get_pointer(base.clone()),
        _ => panic!("`src` must be a pointer of array"),
      },
      _ => panic!("`src` must be a pointer of array"),
    };
    self.insert(GetElemPtr::new_data(src, index, ty))
  }

  /// Creates a binary operation.
  ///
  /// # Panics
  ///
  /// Panics if the lhs/rhs type is not an integer type.
  fn binary(self, op: BinaryOp, lhs: Value, rhs: Value) -> Value {
    let lhs_ty = self.value_type(lhs);
    let rhs_ty = self.value_type(rhs);
    assert!(
      lhs_ty.is_i32() && lhs_ty == rhs_ty,
      "both `lhs` and `rhs` must be integer"
    );
    self.insert(Binary::new_data(op, lhs, rhs, lhs_ty))
  }

  /// Creates a conditional branch with the given condition and targets.
  ///
  /// # Panics
  ///
  /// Panics if the condition type is not an integer type, or the true/false
  /// basic block has parameters.
  fn branch(self, cond: Value, true_bb: BasicBlock, false_bb: BasicBlock) -> Value {
    assert!(self.value_type(cond).is_i32(), "`cond` must be integer");
    check_bb_no_params(self.bb_type(true_bb));
    check_bb_no_params(self.bb_type(false_bb));
    self.insert(Branch::new_data(cond, true_bb, false_bb))
  }

  /// Creates a conditional branch with the given condition, targets
  /// and arguments.
  ///
  /// # Panics
  ///
  /// Panics if the condition type is not an integer type, or the argument
  /// types of the true/false basic block do not match.
  fn branch_with_args(
    self,
    cond: Value,
    true_bb: BasicBlock,
    false_bb: BasicBlock,
    true_args: Vec<Value>,
    false_args: Vec<Value>,
  ) -> Value {
    assert!(self.value_type(cond).is_i32(), "`cond` must be integer");
    check_bb_arg_types(&self, self.bb_type(true_bb), &true_args);
    check_bb_arg_types(&self, self.bb_type(false_bb), &false_args);
    self.insert(Branch::with_args(
      cond, true_bb, false_bb, true_args, false_args,
    ))
  }

  /// Creates a unconditional jump with the given target.
  ///
  /// # Panics
  ///
  /// Panics if the target basic block has parameters.
  fn jump(self, target: BasicBlock) -> Value {
    check_bb_no_params(self.bb_type(target));
    self.insert(Jump::new_data(target))
  }

  /// Creates a unconditional jump with the given target and arguments.
  ///
  /// # Panics
  ///
  /// Panics if the argument types of the target basic block do not match.
  fn jump_with_args(self, target: BasicBlock, args: Vec<Value>) -> Value {
    check_bb_arg_types(&self, self.bb_type(target), &args);
    self.insert(Jump::with_args(target, args))
  }

  /// Creates a function call.
  ///
  /// # Panics
  ///
  /// Panics if the argument types of the callee do not match.
  fn call(self, callee: Function, args: Vec<Value>) -> Value {
    let ty = match self.func_type(callee).kind() {
      TypeKind::Function(params, ret) => {
        assert!(
          params
            .iter()
            .zip(args.iter())
            .all(|(ty, a)| ty == &self.value_type(*a)),
          "argument type mismatch"
        );
        ret.clone()
      }
      _ => panic!("expected a function type"),
    };
    self.insert(Call::new_data(callee, args, ty))
  }

  /// Creates a new return instruction.
  ///
  /// # Panics
  ///
  /// Panics if the value type (if value is not `None`) is an unit type.
  fn ret(self, value: Option<Value>) -> Value {
    assert!(
      value.map_or(true, |v| !self.value_type(v).is_unit()),
      "the type of `value` must not be `unit`"
    );
    self.insert(Return::new_data(value))
  }

  fn basic_block(self, name: Option<String>) -> BasicBlock {
    todo!()
  }

  fn basic_block_with_params(self, name: Option<String>, params: Vec<Value>) -> BasicBlock {
    todo!()
  }
}

fn check_bb_no_params(bb_ty: Type) {
  assert!(
    matches!(bb_ty.kind(), TypeKind::BasicBlock(p) if p.is_empty()),
    "basic block must not have parameters"
  );
}

fn check_bb_arg_types(builder: &impl EntityBuilder, bb_ty: Type, args: &[Value]) {
  match bb_ty.kind() {
    TypeKind::BasicBlock(params) => assert!(
      params.len() == args.len()
        && params
          .iter()
          .zip(args.iter())
          .all(|(ty, a)| ty == &builder.value_type(*a)),
      "arguments type of basic block mismatch"
    ),
    _ => panic!("expected a basic block type"),
  }
}

/// An entity builder that replaces an existing value.
/// 
/// The inserted new value will have the same value handle as the old one.
pub struct ReplaceBuilder<'a> {
  pub(crate) dfg: &'a mut DataFlowGraph,
  pub(crate) value: Value,
}

impl<'a> EntityBuilder for ReplaceBuilder<'a> {
  fn value_type(&self, value: Value) -> Type {
    self
      .dfg
      .globals
      .upgrade()
      .unwrap()
      .borrow()
      .get(&value)
      .or_else(|| self.dfg.values().get(&value))
      .expect("value does not exist")
      .ty()
      .clone()
  }

  fn bb_type(&self, bb: BasicBlock) -> Type {
    self
      .dfg
      .bbs()
      .get(&bb)
      .expect("basic block does not exist")
      .ty()
      .clone()
  }

  fn func_type(&self, func: Function) -> Type {
    self
      .dfg
      .func_tys
      .upgrade()
      .unwrap()
      .borrow()
      .get(&func)
      .expect("function does not exist")
      .clone()
  }

  fn is_const(&self, value: Value) -> bool {
    self
      .dfg
      .globals
      .upgrade()
      .unwrap()
      .borrow()
      .get(&value)
      .or_else(|| self.dfg.values().get(&value))
      .expect("value does not exist")
      .kind()
      .is_const()
  }

  fn insert(self, data: ValueData) -> Value {
    self.dfg.replace_value_with_data(self.value, data);
    self.value
  }
}
