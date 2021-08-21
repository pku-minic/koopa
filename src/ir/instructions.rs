use crate::ir::core::{Use, UseBox, Value, ValueKind, ValueRc};
use crate::ir::types::{Type, TypeKind};

/// Local memory allocation.
pub struct Alloc;

impl Alloc {
  /// Creates a local memory allocation.
  ///
  /// The type of the created allocation will be `ty*`.
  pub fn new(ty: Type) -> ValueRc {
    Value::new(Type::get_pointer(ty), ValueKind::Alloc(Alloc))
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
    let ty = Type::get_pointer(init.borrow().ty().clone());
    Value::new_with_init(ty, |user| {
      ValueKind::GlobalAlloc(GlobalAlloc {
        init: Use::new(init, user),
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
    let ty = match src.borrow().ty().kind() {
      TypeKind::Pointer(ty) => ty.clone(),
      _ => panic!("expected a pointer type!"),
    };
    Value::new_with_init(ty, |user| {
      ValueKind::Load(Load {
        src: Use::new(src, user),
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
      &Type::get_pointer(value.borrow().ty().clone()) == dest.borrow().ty(),
      "the type of `dest` must be the pointer of `value`'s type!"
    );
    Value::new_with_init(Type::get_unit(), |user| {
      ValueKind::Store(Store {
        value: Use::new(value, user.clone()),
        dest: Use::new(dest, user),
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
  step: Option<usize>,
}

impl GetPtr {
  /// Creates a pointer calculation.
  ///
  /// The type of the created `GetPtr` will be the dereference of `src`'s type.
  pub fn new(src: ValueRc, index: ValueRc, step: Option<usize>) -> ValueRc {
    debug_assert!(
      matches!(index.borrow().ty().kind(), TypeKind::Int32),
      "``index` must be an integer!"
    );
    debug_assert!(step != Some(0), "`step` can not be zero");
    let ty = match src.borrow().ty().kind() {
      TypeKind::Array(ty, _) => ty.clone(),
      TypeKind::Pointer(ty) => ty.clone(),
      _ => panic!("`src` must be an array or a pointer!"),
    };
    Value::new_with_init(ty, |user| {
      ValueKind::GetPtr(GetPtr {
        src: Use::new(src, user.clone()),
        index: Use::new(index, user),
        step: step,
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
  pub fn step(&self) -> &Option<usize> {
    &self.step
  }
}

/// Binary operation.
pub struct Binary {
  op: BinaryOp,
  lhs: UseBox,
  rhs: UseBox,
}

/// Supported binary operators.
pub enum BinaryOp {
  // comparison
  NotEq,
  Eq,
  Gt,
  Lt,
  Ge,
  Le,
  // arithmetic
  Add,
  Sub,
  Mul,
  Div,
  Mod,
  // bitwise operations
  And,
  Or,
  Xor,
  // shifting
  Shl,
  Shr,
  Sar,
}

impl Binary {
  /// Creates a binary operation.
  ///
  /// The type of the created `Binary` will be `(lhs.ty)`.
  pub fn new(op: BinaryOp, lhs: ValueRc, rhs: ValueRc) -> ValueRc {
    let ty = lhs.borrow().ty().clone();
    debug_assert!(
      matches!(ty.kind(), TypeKind::Int32) && &ty == rhs.borrow().ty(),
      "both `lhs` and `rhs` must be integer!"
    );
    Value::new_with_init(ty, |user| {
      ValueKind::Binary(Binary {
        op: op,
        lhs: Use::new(lhs, user.clone()),
        rhs: Use::new(rhs, user),
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

/// Unary operation
pub struct Unary {
  op: UnaryOp,
  opr: UseBox,
}

/// Supported unary operators.
pub enum UnaryOp {
  Neg, // negation
  Not, // bitwise not
}

impl Unary {
  /// Creates a unary operation.
  ///
  /// The type of the created `Unary` will be `(opr.ty)`.
  pub fn new(op: UnaryOp, opr: ValueRc) -> ValueRc {
    let ty = opr.borrow().ty().clone();
    debug_assert!(
      matches!(ty.kind(), TypeKind::Int32),
      "`opr` must be integer!"
    );
    Value::new_with_init(ty, |user| {
      ValueKind::Unary(Unary {
        op: op,
        opr: Use::new(opr, user),
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

/// Branching.
pub struct Branch {
  //
}

impl Branch {
  //
}

/// Jumping.
pub struct Jump {
  //
}

impl Jump {
  //
}

/// Function call.
pub struct Call {
  //
}

impl Call {
  //
}

/// Function return.
pub struct Return {
  //
}

impl Return {
  //
}

/// Function argument reference.
pub struct ArgRef {
  //
}

impl ArgRef {
  //
}

/// Phi function.
pub struct Phi {
  //
}

impl Phi {
  //
}
