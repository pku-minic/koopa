use crate::ir::core::{Use, UseBox, Value, ValueKind, ValueRc};
use crate::ir::structs::{BasicBlockRef, FunctionRef};
use crate::ir::types::{Type, TypeKind};
use std::fmt;

/// Local memory allocation.
pub struct Alloc;

impl Alloc {
  /// Creates a local memory allocation.
  ///
  /// The type of the created allocation will be `ty*`.
  pub fn new(ty: Type) -> ValueRc {
    debug_assert!(
      !matches!(ty.kind(), TypeKind::Unit),
      "`ty` can not be unit!"
    );
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
  /// The type of `src` must be some kind of pointer (`ty*`),
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
    debug_assert!(
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
  step: Option<i32>,
}

impl GetPtr {
  /// Creates a pointer calculation.
  ///
  /// The type of the created `GetPtr` will be the dereference of `src`'s type.
  pub fn new(src: ValueRc, index: ValueRc, step: Option<i32>) -> ValueRc {
    debug_assert!(
      matches!(index.ty().kind(), TypeKind::Int32),
      "``index` must be an integer!"
    );
    debug_assert!(step != Some(0), "`step` can not be zero");
    let ty = match src.ty().kind() {
      TypeKind::Array(ty, _) => ty.clone(),
      TypeKind::Pointer(ty) => ty.clone(),
      _ => panic!("`src` must be an array or a pointer!"),
    };
    Value::new_with_init(Type::get_pointer(ty), |user| {
      ValueKind::GetPtr(Self {
        src: Use::new(Some(src), user.clone()),
        index: Use::new(Some(index), user),
        step,
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

  /// Gets the step of pointer calculation.
  pub fn step(&self) -> &Option<i32> {
    &self.step
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
    debug_assert!(
      matches!(ty.kind(), TypeKind::Int32) && &ty == rhs.ty(),
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

/// Unary operation
pub struct Unary {
  op: UnaryOp,
  opr: UseBox,
}

impl Unary {
  /// Creates a unary operation.
  ///
  /// The type of the created `Unary` will be `(opr.ty)`.
  pub fn new(op: UnaryOp, opr: ValueRc) -> ValueRc {
    let ty = opr.ty().clone();
    debug_assert!(
      matches!(ty.kind(), TypeKind::Int32),
      "`opr` must be integer!"
    );
    Value::new_with_init(ty, |user| {
      ValueKind::Unary(Self {
        op,
        opr: Use::new(Some(opr), user),
      })
    })
  }

  /// Gets the unary operator.
  pub fn op(&self) -> &UnaryOp {
    &self.op
  }

  /// Gets the operand.
  pub fn opr(&self) -> &UseBox {
    &self.opr
  }
}

/// Supported unary operators.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum UnaryOp {
  Neg, // negation
  Not, // bitwise not
}

impl fmt::Display for UnaryOp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      UnaryOp::Neg => f.write_str("neg"),
      UnaryOp::Not => f.write_str("not"),
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
    debug_assert!(
      matches!(cond.ty().kind(), TypeKind::Int32),
      "`cond` must be integer!"
    );
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
        debug_assert!(
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
    debug_assert!(
      value
        .as_ref()
        .map_or(true, |v| matches!(v.ty().kind(), TypeKind::Unit)),
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
    debug_assert!(!oprs.is_empty(), "`oprs` must not be empty!");
    // check if all operands have the same type
    debug_assert!(
      oprs.windows(2).all(|v| v[0].0.ty() == v[1].0.ty()),
      "type mismatch in `oprs`!"
    );
    // check value type
    let ty = oprs[0].0.ty().clone();
    debug_assert!(
      !matches!(ty.kind(), TypeKind::Unit),
      "value type must not be `unit`!"
    );
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
    debug_assert!(
      !matches!(ty.kind(), TypeKind::Unit),
      "value type must not be `unit`!"
    );
    Value::new(ty, ValueKind::Phi(Self { oprs: Vec::new() }))
  }

  /// Gets the operands (incoming values and incoming basic blocks).
  pub fn oprs(&self) -> &[(UseBox, BasicBlockRef)] {
    &self.oprs
  }
}
