use crate::front::span::Span;
use crate::ir::BinaryOp;
use std::cmp::PartialEq;

/// An AST of Koopa IR.
#[derive(Debug)]
pub struct Ast {
  pub span: Span,
  pub kind: AstKind,
}

/// A [`Box`] of Koopa IR AST.
pub type AstBox = Box<Ast>;

impl Ast {
  /// Creates a new AST box.
  pub(in crate::front) fn new_boxed(span: Span, kind: AstKind) -> AstBox {
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
  IntType(IntType),
  ArrayType(ArrayType),
  PointerType(PointerType),
  FunType(FunType),
  SymbolRef(SymbolRef),
  IntVal(IntVal),
  UndefVal(UndefVal),
  Aggregate(Aggregate),
  ZeroInit(ZeroInit),
  SymbolDef(SymbolDef),
  GlobalDef(GlobalDef),
  MemDecl(MemDecl),
  GlobalDecl(GlobalDecl),
  Load(Load),
  Store(Store),
  GetPointer(GetPointer),
  GetElementPointer(GetElementPointer),
  BinaryExpr(BinaryExpr),
  Branch(Branch),
  Jump(Jump),
  FunCall(FunCall),
  Return(Return),
  FunDef(FunDef),
  Block(Block),
  FunDecl(FunDecl),
  End(End),
  Error(Error),
}

/// 32-bit integer type.
#[derive(Debug, PartialEq)]
pub struct IntType;

impl IntType {
  /// Creates a new box of `IntType` AST.
  pub fn new_boxed(span: Span) -> AstBox {
    Ast::new_boxed(span, AstKind::IntType(Self))
  }
}

/// Array type.
#[derive(Debug, PartialEq)]
pub struct ArrayType {
  pub base: AstBox,
  pub len: usize,
}

impl ArrayType {
  /// Creates a new box of `ArrayType` AST.
  pub fn new_boxed(span: Span, base: AstBox, len: usize) -> AstBox {
    Ast::new_boxed(span, AstKind::ArrayType(Self { base, len }))
  }
}

/// Pointer type.
#[derive(Debug, PartialEq)]
pub struct PointerType {
  pub base: AstBox,
}

impl PointerType {
  /// Creates a new box of `PointerType` AST.
  pub fn new_boxed(span: Span, base: AstBox) -> AstBox {
    Ast::new_boxed(span, AstKind::PointerType(Self { base }))
  }
}

/// Function type.
#[derive(Debug, PartialEq)]
pub struct FunType {
  pub params: Vec<AstBox>,
  pub ret: Option<AstBox>,
}

impl FunType {
  /// Creates a new box of `FunType` AST.
  pub fn new_boxed(span: Span, params: Vec<AstBox>, ret: Option<AstBox>) -> AstBox {
    Ast::new_boxed(span, AstKind::FunType(Self { params, ret }))
  }
}

/// Symbol refernce.
#[derive(Debug, PartialEq)]
pub struct SymbolRef {
  pub symbol: String,
}

impl SymbolRef {
  /// Creates a new box of `SymbolRef` AST.
  pub fn new_boxed(span: Span, symbol: String) -> AstBox {
    Ast::new_boxed(span, AstKind::SymbolRef(Self { symbol }))
  }
}

/// Integer literal.
#[derive(Debug, PartialEq)]
pub struct IntVal {
  pub value: i32,
}

impl IntVal {
  /// Creates a new box of `IntVal` AST.
  pub fn new_boxed(span: Span, value: i32) -> AstBox {
    Ast::new_boxed(span, AstKind::IntVal(Self { value }))
  }
}

/// Undefined value.
#[derive(Debug, PartialEq)]
pub struct UndefVal;

impl UndefVal {
  /// Creates a new box of `UndefVal` AST.
  pub fn new_boxed(span: Span) -> AstBox {
    Ast::new_boxed(span, AstKind::UndefVal(Self))
  }
}

/// Aggregate value.
#[derive(Debug, PartialEq)]
pub struct Aggregate {
  pub elems: Vec<AstBox>,
}

impl Aggregate {
  /// Creates a new box of `Aggregate` AST.
  pub fn new_boxed(span: Span, elems: Vec<AstBox>) -> AstBox {
    Ast::new_boxed(span, AstKind::Aggregate(Self { elems }))
  }
}

/// Zero initializer.
#[derive(Debug, PartialEq)]
pub struct ZeroInit;

impl ZeroInit {
  /// Creates a new box of `ZeroInit` AST.
  pub fn new_boxed(span: Span) -> AstBox {
    Ast::new_boxed(span, AstKind::ZeroInit(Self))
  }
}

/// Symbol definition.
#[derive(Debug, PartialEq)]
pub struct SymbolDef {
  pub name: String,
  pub value: AstBox,
}

impl SymbolDef {
  /// Creates a new box of `SymbolDef` AST.
  pub fn new_boxed(span: Span, name: String, value: AstBox) -> AstBox {
    Ast::new_boxed(span, AstKind::SymbolDef(Self { name, value }))
  }
}

/// Global symbol definition.
#[derive(Debug, PartialEq)]
pub struct GlobalDef {
  pub name: String,
  pub value: AstBox,
}

impl GlobalDef {
  /// Creates a new box of `GlobalDef` AST.
  pub fn new_boxed(span: Span, name: String, value: AstBox) -> AstBox {
    Ast::new_boxed(span, AstKind::GlobalDef(Self { name, value }))
  }
}

/// Memory declaration.
#[derive(Debug, PartialEq)]
pub struct MemDecl {
  pub ty: AstBox,
}

impl MemDecl {
  /// Creates a new box of `MemDecl` AST.
  pub fn new_boxed(span: Span, ty: AstBox) -> AstBox {
    Ast::new_boxed(span, AstKind::MemDecl(Self { ty }))
  }
}

/// Global memory declaration.
#[derive(Debug, PartialEq)]
pub struct GlobalDecl {
  pub ty: AstBox,
  pub init: AstBox,
}

impl GlobalDecl {
  /// Creates a new box of `GlobalDecl` AST.
  pub fn new_boxed(span: Span, ty: AstBox, init: AstBox) -> AstBox {
    Ast::new_boxed(span, AstKind::GlobalDecl(Self { ty, init }))
  }
}

/// Load.
#[derive(Debug, PartialEq)]
pub struct Load {
  pub symbol: String,
}

impl Load {
  /// Creates a new box of `Load` AST.
  pub fn new_boxed(span: Span, symbol: String) -> AstBox {
    Ast::new_boxed(span, AstKind::Load(Self { symbol }))
  }
}

/// Store.
#[derive(Debug, PartialEq)]
pub struct Store {
  pub value: AstBox,
  pub symbol: String,
}

impl Store {
  /// Creates a new box of `Store` AST.
  pub fn new_boxed(span: Span, value: AstBox, symbol: String) -> AstBox {
    Ast::new_boxed(span, AstKind::Store(Self { value, symbol }))
  }
}

/// Pointer calculation.
#[derive(Debug, PartialEq)]
pub struct GetPointer {
  pub symbol: String,
  pub value: AstBox,
}

impl GetPointer {
  /// Creates a new box of `GetPointer` AST.
  pub fn new_boxed(span: Span, symbol: String, value: AstBox) -> AstBox {
    Ast::new_boxed(span, AstKind::GetPointer(Self { symbol, value }))
  }
}

/// Element pointer calculation.
#[derive(Debug, PartialEq)]
pub struct GetElementPointer {
  pub symbol: String,
  pub value: AstBox,
}

impl GetElementPointer {
  /// Creates a new box of `GetElementPointer` AST.
  pub fn new_boxed(span: Span, symbol: String, value: AstBox) -> AstBox {
    Ast::new_boxed(span, AstKind::GetElementPointer(Self { symbol, value }))
  }
}

/// Binary expression.
#[derive(Debug, PartialEq)]
pub struct BinaryExpr {
  pub op: BinaryOp,
  pub lhs: AstBox,
  pub rhs: AstBox,
}

impl BinaryExpr {
  /// Creates a new box of `BinaryExpr` AST.
  pub fn new_boxed(span: Span, op: BinaryOp, lhs: AstBox, rhs: AstBox) -> AstBox {
    Ast::new_boxed(span, AstKind::BinaryExpr(Self { op, lhs, rhs }))
  }
}

/// Branch.
#[derive(Debug, PartialEq)]
pub struct Branch {
  pub cond: AstBox,
  pub tbb: String,
  pub targs: Vec<AstBox>,
  pub fbb: String,
  pub fargs: Vec<AstBox>,
}

impl Branch {
  /// Creates a new box of `Branch` AST.
  pub fn new_boxed(
    span: Span,
    cond: AstBox,
    tbb: String,
    targs: Vec<AstBox>,
    fbb: String,
    fargs: Vec<AstBox>,
  ) -> AstBox {
    Ast::new_boxed(
      span,
      AstKind::Branch(Self {
        cond,
        tbb,
        targs,
        fbb,
        fargs,
      }),
    )
  }
}

/// Jump.
#[derive(Debug, PartialEq)]
pub struct Jump {
  pub target: String,
  pub args: Vec<AstBox>,
}

impl Jump {
  /// Creates a new box of `Jump` AST.
  pub fn new_boxed(span: Span, target: String, args: Vec<AstBox>) -> AstBox {
    Ast::new_boxed(span, AstKind::Jump(Self { target, args }))
  }
}

/// Function call.
#[derive(Debug, PartialEq)]
pub struct FunCall {
  pub fun: String,
  pub args: Vec<AstBox>,
}

impl FunCall {
  /// Creates a new box of `FunCall` AST.
  pub fn new_boxed(span: Span, fun: String, args: Vec<AstBox>) -> AstBox {
    Ast::new_boxed(span, AstKind::FunCall(Self { fun, args }))
  }
}

/// Return.
#[derive(Debug, PartialEq)]
pub struct Return {
  pub value: Option<AstBox>,
}

impl Return {
  /// Creates a new box of `Return` AST.
  pub fn new_boxed(span: Span, value: Option<AstBox>) -> AstBox {
    Ast::new_boxed(span, AstKind::Return(Self { value }))
  }
}

/// Function definition.
#[derive(Debug, PartialEq)]
pub struct FunDef {
  pub name: String,
  pub params: Vec<(String, AstBox)>,
  pub ret: Option<AstBox>,
  pub bbs: Vec<AstBox>,
}

impl FunDef {
  /// Creates a new box of `FunDef` AST.
  pub fn new_boxed(
    span: Span,
    name: String,
    params: Vec<(String, AstBox)>,
    ret: Option<AstBox>,
    bbs: Vec<AstBox>,
  ) -> AstBox {
    Ast::new_boxed(
      span,
      AstKind::FunDef(Self {
        name,
        params,
        ret,
        bbs,
      }),
    )
  }
}

/// Basic block.
#[derive(Debug, PartialEq)]
pub struct Block {
  pub name: String,
  pub params: Vec<(String, AstBox)>,
  pub stmts: Vec<AstBox>,
}

impl Block {
  /// Creates a new box of `Block` AST.
  pub fn new_boxed(
    span: Span,
    name: String,
    params: Vec<(String, AstBox)>,
    stmts: Vec<AstBox>,
  ) -> AstBox {
    Ast::new_boxed(
      span,
      AstKind::Block(Self {
        name,
        params,
        stmts,
      }),
    )
  }
}

/// Function declaration.
#[derive(Debug, PartialEq)]
pub struct FunDecl {
  pub name: String,
  pub params: Vec<AstBox>,
  pub ret: Option<AstBox>,
}

impl FunDecl {
  /// Creates a new box of `FunDecl` AST.
  pub fn new_boxed(span: Span, name: String, params: Vec<AstBox>, ret: Option<AstBox>) -> AstBox {
    Ast::new_boxed(span, AstKind::FunDecl(Self { name, params, ret }))
  }
}

/// End of file.
#[derive(Debug, PartialEq)]
pub struct End;

impl End {
  /// Creates a new box of `End` AST.
  pub fn new_boxed(span: Span) -> AstBox {
    Ast::new_boxed(span, AstKind::End(Self))
  }
}

/// Error
#[derive(Debug, PartialEq)]
pub struct Error;

impl Error {
  /// Creates a new box of `Error` AST.
  pub fn new_boxed(span: Span) -> AstBox {
    Ast::new_boxed(span, AstKind::Error(Self))
  }
}
