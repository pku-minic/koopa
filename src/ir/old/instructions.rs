#![allow(clippy::new_ret_no_self)]

use crate::ir::core::{Use, UseBox};
use crate::ir::structs::{BasicBlockRef, FunctionRef, PredList};
use crate::ir::{Type, TypeKind, Value, ValueKind, ValueRc};
use std::fmt;

/// Local memory allocation.
pub struct Alloc;

impl Alloc {
  /// Creates a local memory allocation.
  ///
  /// The type of the created allocation will be `*ty`.
  pub fn new(ty: Type) -> ValueRc {
    assert!(!ty.is_unit(), "`ty` can not be unit!");
    Value::new(Type::get_pointer(ty), ValueKind::Alloc(Self))
  }
}

/// Global memory allocation.
pub struct GlobalAlloc {
  init: UseBox,
}

impl GlobalAlloc {
  /// Creates a global memory allocation with initializer `init`.
  ///
  /// The type of the created allocation will be `(init.ty)*`.
  pub fn new(init: ValueRc) -> ValueRc {
    let ty = Type::get_pointer(init.ty().clone());
    Value::new_with_init(ty, |user| {
      ValueKind::GlobalAlloc(Self {
        init: Use::new(Some(init), user),
      })
    })
  }

  /// Gets the initializer.
  pub fn init(&self) -> &UseBox {
    &self.init
  }
}

/// Memory load.
pub struct Load {
  src: UseBox,
}

impl Load {
  /// Creates a memory load with source `src`.
  ///
  /// The type of `src` must be some kind of pointer (`*ty`),
  /// and the type of the created load will be `ty`.
  pub fn new(src: ValueRc) -> ValueRc {
    let ty = match src.ty().kind() {
      TypeKind::Pointer(ty) => ty.clone(),
      _ => panic!("expected a pointer type!"),
    };
    Value::new_with_init(ty, |user| {
      ValueKind::Load(Self {
        src: Use::new(Some(src), user),
      })
    })
  }

  /// Gets the source memory location.
  pub fn src(&self) -> &UseBox {
    &self.src
  }
}

/// Memory store.
pub struct Store {
  value: UseBox,
  dest: UseBox,
}

impl Store {
  /// Creates a memory store with value `value` and destination `dest`.
  pub fn new(value: ValueRc, dest: ValueRc) -> ValueRc {
    assert!(
      &Type::get_pointer(value.ty().clone()) == dest.ty(),
      "the type of `dest` must be the pointer of `value`'s type!"
    );
    Value::new_with_init(Type::get_unit(), |user| {
      ValueKind::Store(Self {
        value: Use::new(Some(value), user.clone()),
        dest: Use::new(Some(dest), user),
      })
    })
  }

  /// Gets the value of the memory store.
  pub fn value(&self) -> &UseBox {
    &self.value
  }

  /// Gets the destination of the memory store.
  pub fn dest(&self) -> &UseBox {
    &self.dest
  }
}

/// Pointer calculation.
pub struct GetPtr {
  src: UseBox,
  index: UseBox,
}

impl GetPtr {
  /// Creates a pointer calculation.
  ///
  /// The type of `src` must be some kind of pointer (`*ty`),
  /// and the type of the created `GetPtr` will also be `*ty`.
  pub fn new(src: ValueRc, index: ValueRc) -> ValueRc {
    assert!(
      matches!(src.ty().kind(), TypeKind::Pointer(..)),
      "`src` must be a pointer!"
    );
    assert!(index.ty().is_i32(), "``index` must be an integer!");
    Value::new_with_init(src.ty().clone(), |user| {
      ValueKind::GetPtr(Self {
        src: Use::new(Some(src), user.clone()),
        index: Use::new(Some(index), user),
      })
    })
  }

  /// Gets the source memory location.
  pub fn src(&self) -> &UseBox {
    &self.src
  }

  /// Gets the index of pointer calculation.
  pub fn index(&self) -> &UseBox {
    &self.index
  }
}

/// Element pointer calculation.
pub struct GetElemPtr {
  src: UseBox,
  index: UseBox,
}

impl GetElemPtr {
  /// Creates a element pointer calculation.
  ///
  /// The type of `src` must be some kind of pointer of array (`*[ty, len]`),
  /// and the type of the created `GetElemPtr` will be `*ty`.
  pub fn new(src: ValueRc, index: ValueRc) -> ValueRc {
    assert!(index.ty().is_i32(), "``index` must be an integer!");
    let ty = match src.ty().kind() {
      TypeKind::Pointer(ty) => match ty.kind() {
        TypeKind::Array(base, _) => Type::get_pointer(base.clone()),
        _ => panic!("`src` must be a pointer of array!"),
      },
      _ => panic!("`src` must be a pointer of array!"),
    };
    Value::new_with_init(ty, |user| {
      ValueKind::GetElemPtr(Self {
        src: Use::new(Some(src), user.clone()),
        index: Use::new(Some(index), user),
      })
    })
  }

  /// Gets the source memory location.
  pub fn src(&self) -> &UseBox {
    &self.src
  }

  /// Gets the index of element pointer calculation.
  pub fn index(&self) -> &UseBox {
    &self.index
  }
}

/// Binary operation.
pub struct Binary {
  op: BinaryOp,
  lhs: UseBox,
  rhs: UseBox,
}

impl Binary {
  /// Creates a binary operation.
  ///
  /// The type of the created `Binary` will be `(lhs.ty)`.
  pub fn new(op: BinaryOp, lhs: ValueRc, rhs: ValueRc) -> ValueRc {
    let ty = lhs.ty().clone();
    assert!(
      ty.is_i32() && &ty == rhs.ty(),
      "both `lhs` and `rhs` must be integer!"
    );
    Value::new_with_init(ty, |user| {
      ValueKind::Binary(Self {
        op,
        lhs: Use::new(Some(lhs), user.clone()),
        rhs: Use::new(Some(rhs), user),
      })
    })
  }

  /// Gets the binary operator.
  pub fn op(&self) -> &BinaryOp {
    &self.op
  }

  /// Gets the left-hand side use.
  pub fn lhs(&self) -> &UseBox {
    &self.lhs
  }

  /// Gets the right-hand side use.
  pub fn rhs(&self) -> &UseBox {
    &self.rhs
  }
}

/// Supported binary operators.
#[rustfmt::skip]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BinaryOp {
  // comparison
  NotEq, Eq, Gt, Lt, Ge, Le,
  // arithmetic
  Add, Sub, Mul, Div, Mod,
  // bitwise operations
  And, Or, Xor,
  // shifting
  Shl, Shr, Sar,
}

impl fmt::Display for BinaryOp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      BinaryOp::NotEq => f.write_str("ne"),
      BinaryOp::Eq => f.write_str("eq"),
      BinaryOp::Gt => f.write_str("gt"),
      BinaryOp::Lt => f.write_str("lt"),
      BinaryOp::Ge => f.write_str("ge"),
      BinaryOp::Le => f.write_str("le"),
      BinaryOp::Add => f.write_str("add"),
      BinaryOp::Sub => f.write_str("sub"),
      BinaryOp::Mul => f.write_str("mul"),
      BinaryOp::Div => f.write_str("div"),
      BinaryOp::Mod => f.write_str("mod"),
      BinaryOp::And => f.write_str("and"),
      BinaryOp::Or => f.write_str("or"),
      BinaryOp::Xor => f.write_str("xor"),
      BinaryOp::Shl => f.write_str("shl"),
      BinaryOp::Shr => f.write_str("shr"),
      BinaryOp::Sar => f.write_str("sar"),
    }
  }
}

/// Branching.
pub struct Branch {
  cond: UseBox,
  targets: [BasicBlockRef; 2],
}

impl Branch {
  /// Creates a conditional branch.
  ///
  /// The type of `cond` must be integer.
  pub fn new(cond: ValueRc, true_bb: BasicBlockRef, false_bb: BasicBlockRef) -> ValueRc {
    assert!(cond.ty().is_i32(), "`cond` must be integer!");
    Value::new_with_init(Type::get_unit(), |user| {
      ValueKind::Branch(Self {
        cond: Use::new(Some(cond), user),
        targets: [true_bb, false_bb],
      })
    })
  }

  /// Gets the branch condition.
  pub fn cond(&self) -> &UseBox {
    &self.cond
  }

  /// Gets the true target basic block.
  pub fn true_bb(&self) -> &BasicBlockRef {
    &self.targets[0]
  }

  /// Gets the false target basic block.
  pub fn false_bb(&self) -> &BasicBlockRef {
    &self.targets[1]
  }
  /// Gets the target basic blocks.
  pub fn targets(&self) -> &[BasicBlockRef] {
    &self.targets
  }

  /// Adds the specific basic block to the predecessor lists of all targets.
  pub(crate) fn add_pred(&self, bb: BasicBlockRef, preds: &mut PredList) {
    for target in &self.targets {
      if target.ptr_eq(&bb) {
        preds.add_pred(bb.clone());
      } else {
        let ptr = target.upgrade().unwrap();
        ptr.inner_mut().preds_mut().add_pred(bb.clone());
      }
    }
  }

  /// Removes the specific basic block from the predecessor lists of all targets.
  pub(crate) fn remove_pred(&self, bb: &BasicBlockRef, preds: &mut PredList) {
    for target in &self.targets {
      if target.ptr_eq(bb) {
        preds.remove_pred(bb);
      } else {
        let ptr = target.upgrade().unwrap();
        ptr.inner_mut().preds_mut().remove_pred(bb);
      }
    }
  }
}

/// Jumping.
pub struct Jump {
  target: BasicBlockRef,
}

impl Jump {
  /// Creates a unconditional jump.
  pub fn new(target: BasicBlockRef) -> ValueRc {
    Value::new(Type::get_unit(), ValueKind::Jump(Self { target }))
  }

  /// Gets the target basic block.
  pub fn target(&self) -> &BasicBlockRef {
    &self.target
  }

  /// Adds the specific basic block to the predecessor list of target.
  pub(crate) fn add_pred(&self, bb: BasicBlockRef, preds: &mut PredList) {
    if self.target.ptr_eq(&bb) {
      preds.add_pred(bb);
    } else {
      let ptr = self.target.upgrade().unwrap();
      ptr.inner_mut().preds_mut().add_pred(bb);
    }
  }

  /// Removes the specific basic block from the predecessor list of target.
  pub(crate) fn remove_pred(&self, bb: &BasicBlockRef, preds: &mut PredList) {
    if self.target.ptr_eq(bb) {
      preds.remove_pred(bb);
    } else {
      let ptr = self.target.upgrade().unwrap();
      ptr.inner_mut().preds_mut().remove_pred(bb);
    }
  }
}

/// Function call.
pub struct Call {
  callee: FunctionRef,
  args: Vec<UseBox>,
}

impl Call {
  /// Creates a function call.
  ///
  /// The type of created call will be the return type of function `callee`.
  pub fn new(callee: FunctionRef, args: Vec<ValueRc>) -> ValueRc {
    let ty = match callee.upgrade().unwrap().ty().kind() {
      TypeKind::Function(params, ret) => {
        assert!(
          params.iter().zip(args.iter()).all(|v| v.0 == v.1.ty()),
          "argument type mismatch"
        );
        ret.clone()
      }
      _ => panic!("expected a function type"),
    };
    Value::new_with_init(ty, |user| {
      ValueKind::Call(Self {
        callee,
        args: args
          .into_iter()
          .map(|a| Use::new(Some(a), user.clone()))
          .collect(),
      })
    })
  }

  /// Gets the callee.
  pub fn callee(&self) -> &FunctionRef {
    &self.callee
  }

  /// Gets the argument list.
  pub fn args(&self) -> &[UseBox] {
    &self.args
  }
}

/// Function return.
pub struct Return {
  value: UseBox,
}

impl Return {
  /// Creates a new return instruction.
  pub fn new(value: Option<ValueRc>) -> ValueRc {
    assert!(
      value.as_ref().map_or(true, |v| !v.ty().is_unit()),
      "the type of `value` must not be `unit`!"
    );
    Value::new_with_init(Type::get_unit(), |user| {
      ValueKind::Return(Self {
        value: Use::new(value, user),
      })
    })
  }

  /// Gets the return value.
  pub fn value(&self) -> &UseBox {
    &self.value
  }
}

/// Phi function.
pub struct Phi {
  oprs: Vec<(UseBox, BasicBlockRef)>,
}

impl Phi {
  /// Creates a new phi function.
  pub fn new(oprs: Vec<(ValueRc, BasicBlockRef)>) -> ValueRc {
    // operand list should not be empty
    assert!(!oprs.is_empty(), "`oprs` must not be empty!");
    // check if all operands have the same type
    assert!(
      oprs.windows(2).all(|v| v[0].0.ty() == v[1].0.ty()),
      "type mismatch in `oprs`!"
    );
    // check value type
    let ty = oprs[0].0.ty().clone();
    assert!(!ty.is_unit(), "value type must not be `unit`!");
    Value::new_with_init(ty, |user| {
      ValueKind::Phi(Self {
        oprs: oprs
          .into_iter()
          .map(|v| (Use::new(Some(v.0), user.clone()), v.1))
          .collect(),
      })
    })
  }

  /// Creates a new uninitialized phi function.
  ///
  /// This phi function must be replaced with a normal phi function afterwards.
  pub fn new_uninit(ty: Type) -> ValueRc {
    // check value type
    assert!(!ty.is_unit(), "value type must not be `unit`!");
    Value::new(ty, ValueKind::Phi(Self { oprs: Vec::new() }))
  }

  /// Gets the operands (incoming values and incoming basic blocks).
  pub fn oprs(&self) -> &[(UseBox, BasicBlockRef)] {
    &self.oprs
  }
}
