use crate::ir::dfg::DataFlowGraph;
use crate::ir::entities::{BasicBlock, BasicBlockData, Function, Program, Value, ValueData};
use crate::ir::types::{Type, TypeKind};
use crate::ir::values::*;

/// A trait that provides methods for querying entity information.
pub trait EntityInfoQuerier {
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
}

/// A builder trait that provides method for inserting value data
/// to the value storage.
pub trait ValueInserter {
  /// Inserts the given value data to the value storage,
  /// returns the handle of the inserted value.
  fn insert_value(&mut self, data: ValueData) -> Value;
}

/// A builder trait that provides method for building value data.
pub trait ValueBuilder: Sized + EntityInfoQuerier + ValueInserter {
  /// Create a new integer constant.
  fn integer(mut self, value: i32) -> Value {
    self.insert_value(Integer::new_data(value))
  }

  /// Create a new zero initializer.
  ///
  /// # Panics
  ///
  /// Panics if the given type is an unit type.
  fn zero_init(mut self, ty: Type) -> Value {
    assert!(!ty.is_unit(), "`ty` can not be unit");
    self.insert_value(ZeroInit::new_data(ty))
  }

  /// Create a new undefined value.
  ///
  /// # Panics
  ///
  /// Panics if the given type is an unit type.
  fn undef(mut self, ty: Type) -> Value {
    assert!(!ty.is_unit(), "`ty` can not be unit");
    self.insert_value(Undef::new_data(ty))
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
  fn aggregate(mut self, elems: Vec<Value>) -> Value {
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
    self.insert_value(Aggregate::new_data(elems, ty))
  }
}

/// A builder for building and inserting global instructions.
pub trait GlobalInstBuilder: ValueBuilder {
  /// Creates a global memory allocation.
  ///
  /// # Panics
  ///
  /// Panics if the type of the initialize is an unit type.
  fn global_alloc(mut self, init: Value) -> Value {
    let init_ty = self.value_type(init);
    assert!(!init_ty.is_unit(), "the type of `init` must not be unit");
    let ty = Type::get_pointer(init_ty);
    self.insert_value(GlobalAlloc::new_data(init, ty))
  }
}

/// A builder for building and inserting local instructions.
pub trait LocalInstBuilder: ValueBuilder {
  /// Creates a local memory allocation.
  ///
  /// # Panics
  ///
  /// Panics if the given type is an unit type.
  fn alloc(mut self, ty: Type) -> Value {
    assert!(!ty.is_unit(), "`ty` can not be unit");
    self.insert_value(Alloc::new_data(ty))
  }

  /// Creates a memory load with the given source.
  ///
  /// # Panics
  ///
  /// Panics if the type of the source value is not a pointer type.
  fn load(mut self, src: Value) -> Value {
    let src_ty = self.value_type(src);
    let ty = match src_ty.kind() {
      TypeKind::Pointer(ty) => ty.clone(),
      _ => panic!("expected a pointer type"),
    };
    self.insert_value(Load::new_data(src, ty))
  }

  /// Creates a memory store with the given value and destination.
  ///
  /// # Panics
  ///
  /// Panics if the dest type is not a pointer of the value type.
  fn store(mut self, value: Value, dest: Value) -> Value {
    assert!(
      Type::get_pointer(self.value_type(value)) == self.value_type(dest),
      "the type of `dest` must be the pointer of `value`'s type"
    );
    self.insert_value(Store::new_data(value, dest))
  }

  /// Creates a pointer calculation with the given source pointer and index.
  ///
  /// # Panics
  ///
  /// Panics if the source type is not a pointer type, or the index type is
  /// not an integer type.
  fn get_ptr(mut self, src: Value, index: Value) -> Value {
    let src_ty = self.value_type(src);
    assert!(
      matches!(src_ty.kind(), TypeKind::Pointer(..)),
      "`src` must be a pointer"
    );
    assert!(
      self.value_type(index).is_i32(),
      "`index` must be an integer"
    );
    self.insert_value(GetPtr::new_data(src, index, src_ty))
  }

  /// Creates a element pointer calculation with the given source pointer
  /// and index.
  ///
  /// # Panics
  ///
  /// Panics if the source type is not a pointer type of an array, or the
  /// index type is not an integer type.
  fn get_elem_ptr(mut self, src: Value, index: Value) -> Value {
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
    self.insert_value(GetElemPtr::new_data(src, index, ty))
  }

  /// Creates a binary operation.
  ///
  /// # Panics
  ///
  /// Panics if the lhs/rhs type is not an integer type.
  fn binary(mut self, op: BinaryOp, lhs: Value, rhs: Value) -> Value {
    let lhs_ty = self.value_type(lhs);
    let rhs_ty = self.value_type(rhs);
    assert!(
      lhs_ty.is_i32() && lhs_ty == rhs_ty,
      "both `lhs` and `rhs` must be integer"
    );
    self.insert_value(Binary::new_data(op, lhs, rhs, lhs_ty))
  }

  /// Creates a conditional branch with the given condition and targets.
  ///
  /// # Panics
  ///
  /// Panics if the condition type is not an integer type, or the true/false
  /// basic block has parameters.
  fn branch(mut self, cond: Value, true_bb: BasicBlock, false_bb: BasicBlock) -> Value {
    assert!(self.value_type(cond).is_i32(), "`cond` must be integer");
    check_bb_no_params(self.bb_type(true_bb));
    check_bb_no_params(self.bb_type(false_bb));
    self.insert_value(Branch::new_data(cond, true_bb, false_bb))
  }

  /// Creates a conditional branch with the given condition, targets
  /// and arguments.
  ///
  /// # Panics
  ///
  /// Panics if the condition type is not an integer type, or the argument
  /// types of the true/false basic block do not match.
  fn branch_with_args(
    mut self,
    cond: Value,
    true_bb: BasicBlock,
    false_bb: BasicBlock,
    true_args: Vec<Value>,
    false_args: Vec<Value>,
  ) -> Value {
    assert!(self.value_type(cond).is_i32(), "`cond` must be integer");
    check_bb_arg_types(&self, self.bb_type(true_bb), &true_args);
    check_bb_arg_types(&self, self.bb_type(false_bb), &false_args);
    self.insert_value(Branch::with_args(
      cond, true_bb, false_bb, true_args, false_args,
    ))
  }

  /// Creates a unconditional jump with the given target.
  ///
  /// # Panics
  ///
  /// Panics if the target basic block has parameters.
  fn jump(mut self, target: BasicBlock) -> Value {
    check_bb_no_params(self.bb_type(target));
    self.insert_value(Jump::new_data(target))
  }

  /// Creates a unconditional jump with the given target and arguments.
  ///
  /// # Panics
  ///
  /// Panics if the argument types of the target basic block do not match.
  fn jump_with_args(mut self, target: BasicBlock, args: Vec<Value>) -> Value {
    check_bb_arg_types(&self, self.bb_type(target), &args);
    self.insert_value(Jump::with_args(target, args))
  }

  /// Creates a function call.
  ///
  /// # Panics
  ///
  /// Panics if the argument types of the callee do not match.
  fn call(mut self, callee: Function, args: Vec<Value>) -> Value {
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
    self.insert_value(Call::new_data(callee, args, ty))
  }

  /// Creates a new return instruction.
  ///
  /// # Panics
  ///
  /// Panics if the value type (if value is not `None`) is an unit type.
  fn ret(mut self, value: Option<Value>) -> Value {
    assert!(
      value.map_or(true, |v| !self.value_type(v).is_unit()),
      "the type of `value` must not be `unit`"
    );
    self.insert_value(Return::new_data(value))
  }
}

/// A builder trait that provides method for building value data and
/// inserting value data to the value storage.
pub trait BasicBlockBuilder: Sized + ValueInserter {
  /// Inserts the given basic block data to the basic block storage,
  /// returns the handle of the inserted basic block.
  fn insert_bb(&mut self, data: BasicBlockData) -> BasicBlock;

  /// Creates a new basic block with the given name.
  ///
  /// # Panics
  ///
  /// Panics if the given name (if exists) not starts with `%` or `@`.
  fn basic_block(mut self, name: Option<String>) -> BasicBlock {
    check_bb_name(&name);
    self.insert_bb(BasicBlockData::new(name))
  }

  /// Creates a new basic block with the given name and parameter types.
  ///
  /// # Panics
  ///
  /// Panics if there are unit types in the given parameter types.
  fn basic_block_with_params(mut self, name: Option<String>, params_ty: Vec<Type>) -> BasicBlock {
    check_bb_name(&name);
    assert!(
      params_ty.iter().all(|p| !p.is_unit()),
      "parameter type must not be `unit`!"
    );
    let params = params_ty
      .iter()
      .enumerate()
      .map(|(i, ty)| self.insert_value(BlockArgRef::new_data(i, ty.clone())))
      .collect();
    let ty = Type::get_basic_block(params_ty);
    self.insert_bb(BasicBlockData::with_params(name, params, ty))
  }

  /// Creates a new basic block with the given name, parameter names
  /// and parameter types.
  ///
  /// # Panics
  ///
  /// Panics if there are unit types in the given parameter types.
  fn basic_block_with_param_names(
    mut self,
    name: Option<String>,
    params: Vec<(Option<String>, Type)>,
  ) -> BasicBlock {
    check_bb_name(&name);
    assert!(
      params.iter().all(|(_, p)| !p.is_unit()),
      "parameter type must not be `unit`!"
    );
    let (params, params_ty) = params
      .into_iter()
      .enumerate()
      .map(|(i, (n, ty))| {
        let mut arg = BlockArgRef::new_data(i, ty.clone());
        arg.set_name(n);
        (self.insert_value(arg), ty)
      })
      .unzip();
    let ty = Type::get_basic_block(params_ty);
    self.insert_bb(BasicBlockData::with_params(name, params, ty))
  }
}

/// Checks if the given basic block type has no parameters.
///
/// # Panics
///
/// Panics if the given basic block type has parameters.
fn check_bb_no_params(bb_ty: Type) {
  assert!(
    matches!(bb_ty.kind(), TypeKind::BasicBlock(p) if p.is_empty()),
    "basic block must not have parameters"
  );
}

/// Checks if the parameter types of the given basic block type matches
/// the given argument types.
///
/// # Panics
///
/// Panics if the parameter types of the given basic block type does not
/// match the given argument types.
fn check_bb_arg_types(querier: &impl EntityInfoQuerier, bb_ty: Type, args: &[Value]) {
  match bb_ty.kind() {
    TypeKind::BasicBlock(params) => assert!(
      params.len() == args.len()
        && params
          .iter()
          .zip(args.iter())
          .all(|(ty, a)| ty == &querier.value_type(*a)),
      "arguments type of basic block mismatch"
    ),
    _ => panic!("expected a basic block type"),
  }
}

/// Checks if the given name is a valid basic block name.
///
/// # Panics
///
/// Panics if the given name (if exists) not starts with `%` or `@`.
fn check_bb_name(name: &Option<String>) {
  assert!(
    name.as_ref().map_or(true, |n| n.len() > 1
      && (n.starts_with('%') || n.starts_with('@'))),
    "invalid basic block name"
  );
}

/// An entity information querier based on data flow graph.
pub trait DfgBasedInfoQuerier {
  fn dfg(&self) -> &DataFlowGraph;
}

impl<T: DfgBasedInfoQuerier> EntityInfoQuerier for T {
  fn value_type(&self, value: Value) -> Type {
    self
      .dfg()
      .globals
      .upgrade()
      .unwrap()
      .borrow()
      .get(&value)
      .or_else(|| self.dfg().values().get(&value))
      .expect("value does not exist")
      .ty()
      .clone()
  }

  fn bb_type(&self, bb: BasicBlock) -> Type {
    self
      .dfg()
      .bbs()
      .get(&bb)
      .expect("basic block does not exist")
      .ty()
      .clone()
  }

  fn func_type(&self, func: Function) -> Type {
    self
      .dfg()
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
      .dfg()
      .globals
      .upgrade()
      .unwrap()
      .borrow()
      .get(&value)
      .or_else(|| self.dfg().values().get(&value))
      .expect("value does not exist")
      .kind()
      .is_const()
  }
}

/// An value builder that builds a new local value and inserts it
/// to the data flow graph.
pub struct LocalBuilder<'a> {
  pub(crate) dfg: &'a mut DataFlowGraph,
}

impl<'a> DfgBasedInfoQuerier for LocalBuilder<'a> {
  fn dfg(&self) -> &DataFlowGraph {
    self.dfg
  }
}

impl<'a> ValueInserter for LocalBuilder<'a> {
  fn insert_value(&mut self, data: ValueData) -> Value {
    self.dfg.new_value_data(data)
  }
}

impl<'a> ValueBuilder for LocalBuilder<'a> {}
impl<'a> LocalInstBuilder for LocalBuilder<'a> {}

/// An basic block builder that builds a new basic block and inserts it
/// to the data flow graph.
pub struct BlockBuilder<'a> {
  pub(crate) dfg: &'a mut DataFlowGraph,
}

impl<'a> ValueInserter for BlockBuilder<'a> {
  fn insert_value(&mut self, data: ValueData) -> Value {
    self.dfg.new_value_data(data)
  }
}

impl<'a> BasicBlockBuilder for BlockBuilder<'a> {
  fn insert_bb(&mut self, data: BasicBlockData) -> BasicBlock {
    self.dfg.new_bb_data(data)
  }
}

/// An value builder that replaces an existing local value.
///
/// The inserted new value will have the same value handle as the old one.
pub struct ReplaceBuilder<'a> {
  pub(crate) dfg: &'a mut DataFlowGraph,
  pub(crate) value: Value,
}

impl<'a> DfgBasedInfoQuerier for ReplaceBuilder<'a> {
  fn dfg(&self) -> &DataFlowGraph {
    self.dfg
  }
}

impl<'a> ValueInserter for ReplaceBuilder<'a> {
  fn insert_value(&mut self, data: ValueData) -> Value {
    self.dfg.replace_value_with_data(self.value, data);
    self.value
  }
}

impl<'a> ValueBuilder for ReplaceBuilder<'a> {}
impl<'a> LocalInstBuilder for ReplaceBuilder<'a> {}

/// An value builder that builds a new global value and inserts it
/// to the program.
pub struct GlobalBuilder<'a> {
  pub(crate) program: &'a mut Program,
}

impl<'a> EntityInfoQuerier for GlobalBuilder<'a> {
  fn value_type(&self, value: Value) -> Type {
    self
      .program
      .values
      .borrow()
      .get(&value)
      .expect("value does not exist")
      .ty()
      .clone()
  }

  fn bb_type(&self, _: BasicBlock) -> Type {
    unimplemented!()
  }

  fn func_type(&self, _: Function) -> Type {
    unimplemented!()
  }

  fn is_const(&self, value: Value) -> bool {
    self
      .program
      .values
      .borrow()
      .get(&value)
      .expect("value does not exist")
      .kind()
      .is_const()
  }
}

impl<'a> ValueInserter for GlobalBuilder<'a> {
  fn insert_value(&mut self, data: ValueData) -> Value {
    let is_inst = data.kind().is_global_alloc();
    let value = self.program.new_value_data(data);
    if is_inst {
      self.program.inst_layout.push(value);
    }
    value
  }
}

impl<'a> ValueBuilder for GlobalBuilder<'a> {}
impl<'a> GlobalInstBuilder for GlobalBuilder<'a> {}
