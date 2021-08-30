use crate::front::span::Span;
use crate::ir::instructions::{BinaryOp, UnaryOp};
use std::cmp::PartialEq;

/// AST of Koopa IR.
#[derive(Debug)]
pub struct Ast {
  pub span: Span,
  pub kind: AstKind,
}

/// Box of AST.
pub type AstBox = Box<Ast>;

impl Ast {
  /// Creates a new AST box.
  pub fn new(span: Span, kind: AstKind) -> AstBox {
    Box::new(Self { span, kind })
  }
}

impl PartialEq for Ast {
  fn eq(&self, other: &Self) -> bool {
    // ignore field `span`
    self.kind == other.kind
  }
}

/// Kind of AST.
#[derive(Debug, PartialEq)]
pub enum AstKind {
  /// 32-bit integer type.
  IntType,
  /// Array type.
  ArrayType { base: AstBox, len: usize },
  /// Pointer type.
  PointerType { base: AstBox },
  /// Function type.
  FunType {
    params: Vec<AstBox>,
    ret: Option<AstBox>,
  },

  /// Symbol refernce.
  SymbolRef { symbol: String },
  /// Integer literal.
  IntVal { value: i32 },
  /// Undefined value.
  UndefVal,
  /// Aggregate value.
  Aggregate { elems: Vec<AstBox> },
  /// Zero initializer.
  ZeroInit,

  /// Symbol definition.
  SymbolDef { name: String, value: AstBox },
  /// Global symbol definition.
  GlobalDef { name: String, value: AstBox },

  /// Memory declaration.
  MemDecl { ty: AstBox },
  /// Global memory declaration.
  GlobalDecl { ty: AstBox, init: AstBox },
  /// Load.
  Load { symbol: String },
  /// Store.
  Store { value: AstBox, symbol: String },
  /// Pointer calculation.
  GetPointer {
    symbol: String,
    value: AstBox,
    step: Option<i32>,
  },

  /// Binary expression.
  BinaryExpr {
    op: BinaryOp,
    lhs: AstBox,
    rhs: AstBox,
  },
  /// Unary expression.
  UnaryExpr { op: UnaryOp, opr: AstBox },

  /// Branch.
  Branch {
    cond: AstBox,
    tbb: String,
    fbb: String,
  },
  /// Jump.
  Jump { target: String },

  /// Function call.
  FunCall { fun: String, args: Vec<AstBox> },
  /// Return.
  Return { value: Option<AstBox> },

  /// Function definition.
  FunDef {
    name: String,
    params: Vec<(String, AstBox)>,
    ret: Option<AstBox>,
    bbs: Vec<AstBox>,
  },
  /// Basic block.
  Block { name: String, stmts: Vec<AstBox> },
  /// Function declaration.
  FunDecl {
    name: String,
    params: Vec<AstBox>,
    ret: Option<AstBox>,
  },

  /// Phi function.
  Phi { oprs: Vec<(AstBox, String)> },

  /// End of file.
  End,
}
