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
  pub(crate) fn new(span: Span, kind: AstKind) -> AstBox {
    Box::new(Self { span, kind })
  }

  /// Accepts an AST visitor, and calls its corresponding visitor method.
  pub fn accept<T: AstVisitor>(&self, visitor: &mut T) -> T::Output {
    match &self.kind {
      AstKind::IntType(ast) => visitor.visit_int_type(&self.span, ast),
      AstKind::ArrayType(ast) => visitor.visit_array_type(&self.span, ast),
      AstKind::PointerType(ast) => visitor.visit_pointer_type(&self.span, ast),
      AstKind::FunType(ast) => visitor.visit_fun_type(&self.span, ast),
      AstKind::SymbolRef(ast) => visitor.visit_symbol_ref(&self.span, ast),
      AstKind::IntVal(ast) => visitor.visit_int_val(&self.span, ast),
      AstKind::UndefVal(ast) => visitor.visit_undef_val(&self.span, ast),
      AstKind::Aggregate(ast) => visitor.visit_aggregate(&self.span, ast),
      AstKind::ZeroInit(ast) => visitor.visit_zero_init(&self.span, ast),
      AstKind::SymbolDef(ast) => visitor.visit_symbol_def(&self.span, ast),
      AstKind::GlobalDef(ast) => visitor.visit_global_def(&self.span, ast),
      AstKind::MemDecl(ast) => visitor.visit_mem_decl(&self.span, ast),
      AstKind::GlobalDecl(ast) => visitor.visit_global_decl(&self.span, ast),
      AstKind::Load(ast) => visitor.visit_load(&self.span, ast),
      AstKind::Store(ast) => visitor.visit_store(&self.span, ast),
      AstKind::GetPointer(ast) => visitor.visit_get_pointer(&self.span, ast),
      AstKind::BinaryExpr(ast) => visitor.visit_binary_expr(&self.span, ast),
      AstKind::UnaryExpr(ast) => visitor.visit_unary_expr(&self.span, ast),
      AstKind::Branch(ast) => visitor.visit_branch(&self.span, ast),
      AstKind::Jump(ast) => visitor.visit_jump(&self.span, ast),
      AstKind::FunCall(ast) => visitor.visit_fun_call(&self.span, ast),
      AstKind::Return(ast) => visitor.visit_return(&self.span, ast),
      AstKind::FunDef(ast) => visitor.visit_fun_def(&self.span, ast),
      AstKind::Block(ast) => visitor.visit_block(&self.span, ast),
      AstKind::FunDecl(ast) => visitor.visit_fun_decl(&self.span, ast),
      AstKind::Phi(ast) => visitor.visit_phi(&self.span, ast),
      AstKind::End(ast) => visitor.visit_end(&self.span, ast),
      AstKind::Error(ast) => visitor.visit_error(&self.span, ast),
    }
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
  BinaryExpr(BinaryExpr),
  UnaryExpr(UnaryExpr),
  Branch(Branch),
  Jump(Jump),
  FunCall(FunCall),
  Return(Return),
  FunDef(FunDef),
  Block(Block),
  FunDecl(FunDecl),
  Phi(Phi),
  End(End),
  Error(Error),
}

/// AST visitor.
pub trait AstVisitor {
  /// Return type of all visitor methods.
  type Output;

  /// Visits `IntType` AST.
  fn visit_int_type(&mut self, span: &Span, ast: &IntType) -> Self::Output;
  /// Visits `ArrayType` AST.
  fn visit_array_type(&mut self, span: &Span, ast: &ArrayType) -> Self::Output;
  /// Visits `PointerType` AST.
  fn visit_pointer_type(&mut self, span: &Span, ast: &PointerType) -> Self::Output;
  /// Visits `FunType` AST.
  fn visit_fun_type(&mut self, span: &Span, ast: &FunType) -> Self::Output;
  /// Visits `SymbolRef` AST.
  fn visit_symbol_ref(&mut self, span: &Span, ast: &SymbolRef) -> Self::Output;
  /// Visits `IntVal` AST.
  fn visit_int_val(&mut self, span: &Span, ast: &IntVal) -> Self::Output;
  /// Visits `UndefVal` AST.
  fn visit_undef_val(&mut self, span: &Span, ast: &UndefVal) -> Self::Output;
  /// Visits `Aggregate` AST.
  fn visit_aggregate(&mut self, span: &Span, ast: &Aggregate) -> Self::Output;
  /// Visits `ZeroInit` AST.
  fn visit_zero_init(&mut self, span: &Span, ast: &ZeroInit) -> Self::Output;
  /// Visits `SymbolDef` AST.
  fn visit_symbol_def(&mut self, span: &Span, ast: &SymbolDef) -> Self::Output;
  /// Visits `GlobalDef` AST.
  fn visit_global_def(&mut self, span: &Span, ast: &GlobalDef) -> Self::Output;
  /// Visits `MemDecl` AST.
  fn visit_mem_decl(&mut self, span: &Span, ast: &MemDecl) -> Self::Output;
  /// Visits `GlobalDecl` AST.
  fn visit_global_decl(&mut self, span: &Span, ast: &GlobalDecl) -> Self::Output;
  /// Visits `Load` AST.
  fn visit_load(&mut self, span: &Span, ast: &Load) -> Self::Output;
  /// Visits `Store` AST.
  fn visit_store(&mut self, span: &Span, ast: &Store) -> Self::Output;
  /// Visits `GetPointer` AST.
  fn visit_get_pointer(&mut self, span: &Span, ast: &GetPointer) -> Self::Output;
  /// Visits `BinaryExpr` AST.
  fn visit_binary_expr(&mut self, span: &Span, ast: &BinaryExpr) -> Self::Output;
  /// Visits `UnaryExpr` AST.
  fn visit_unary_expr(&mut self, span: &Span, ast: &UnaryExpr) -> Self::Output;
  /// Visits `Branch` AST.
  fn visit_branch(&mut self, span: &Span, ast: &Branch) -> Self::Output;
  /// Visits `Jump` AST.
  fn visit_jump(&mut self, span: &Span, ast: &Jump) -> Self::Output;
  /// Visits `FunCall` AST.
  fn visit_fun_call(&mut self, span: &Span, ast: &FunCall) -> Self::Output;
  /// Visits `Return` AST.
  fn visit_return(&mut self, span: &Span, ast: &Return) -> Self::Output;
  /// Visits `FunDef` AST.
  fn visit_fun_def(&mut self, span: &Span, ast: &FunDef) -> Self::Output;
  /// Visits `Block` AST.
  fn visit_block(&mut self, span: &Span, ast: &Block) -> Self::Output;
  /// Visits `FunDecl` AST.
  fn visit_fun_decl(&mut self, span: &Span, ast: &FunDecl) -> Self::Output;
  /// Visits `Phi` AST.
  fn visit_phi(&mut self, span: &Span, ast: &Phi) -> Self::Output;
  /// Visits `End` AST.
  fn visit_end(&mut self, span: &Span, ast: &End) -> Self::Output;
  /// Visits `Error` AST.
  fn visit_error(&mut self, span: &Span, ast: &Error) -> Self::Output;
}

/// 32-bit integer type.
#[derive(Debug, PartialEq)]
pub struct IntType;

impl IntType {
  /// Creates a new box of `IntType` AST.
  pub fn new(span: Span) -> AstBox {
    Ast::new(span, AstKind::IntType(IntType))
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
  pub fn new(span: Span, base: AstBox, len: usize) -> AstBox {
    Ast::new(span, AstKind::ArrayType(ArrayType { base, len }))
  }
}

/// Pointer type.
#[derive(Debug, PartialEq)]
pub struct PointerType {
  pub base: AstBox,
}

impl PointerType {
  /// Creates a new box of `PointerType` AST.
  pub fn new(span: Span, base: AstBox) -> AstBox {
    Ast::new(span, AstKind::PointerType(PointerType { base }))
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
  pub fn new(span: Span, params: Vec<AstBox>, ret: Option<AstBox>) -> AstBox {
    Ast::new(span, AstKind::FunType(FunType { params, ret }))
  }
}

/// Symbol refernce.
#[derive(Debug, PartialEq)]
pub struct SymbolRef {
  pub symbol: String,
}

impl SymbolRef {
  /// Creates a new box of `SymbolRef` AST.
  pub fn new(span: Span, symbol: String) -> AstBox {
    Ast::new(span, AstKind::SymbolRef(SymbolRef { symbol }))
  }
}

/// Integer literal.
#[derive(Debug, PartialEq)]
pub struct IntVal {
  pub value: i32,
}

impl IntVal {
  /// Creates a new box of `IntVal` AST.
  pub fn new(span: Span, value: i32) -> AstBox {
    Ast::new(span, AstKind::IntVal(IntVal { value }))
  }
}

/// Undefined value.
#[derive(Debug, PartialEq)]
pub struct UndefVal;

impl UndefVal {
  /// Creates a new box of `UndefVal` AST.
  pub fn new(span: Span) -> AstBox {
    Ast::new(span, AstKind::UndefVal(UndefVal))
  }
}

/// Aggregate value.
#[derive(Debug, PartialEq)]
pub struct Aggregate {
  pub elems: Vec<AstBox>,
}

impl Aggregate {
  /// Creates a new box of `Aggregate` AST.
  pub fn new(span: Span, elems: Vec<AstBox>) -> AstBox {
    Ast::new(span, AstKind::Aggregate(Aggregate { elems }))
  }
}

/// Zero initializer.
#[derive(Debug, PartialEq)]
pub struct ZeroInit;

impl ZeroInit {
  /// Creates a new box of `ZeroInit` AST.
  pub fn new(span: Span) -> AstBox {
    Ast::new(span, AstKind::ZeroInit(ZeroInit))
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
  pub fn new(span: Span, name: String, value: AstBox) -> AstBox {
    Ast::new(span, AstKind::SymbolDef(SymbolDef { name, value }))
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
  pub fn new(span: Span, name: String, value: AstBox) -> AstBox {
    Ast::new(span, AstKind::GlobalDef(GlobalDef { name, value }))
  }
}

/// Memory declaration.
#[derive(Debug, PartialEq)]
pub struct MemDecl {
  pub ty: AstBox,
}

impl MemDecl {
  /// Creates a new box of `MemDecl` AST.
  pub fn new(span: Span, ty: AstBox) -> AstBox {
    Ast::new(span, AstKind::MemDecl(MemDecl { ty }))
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
  pub fn new(span: Span, ty: AstBox, init: AstBox) -> AstBox {
    Ast::new(span, AstKind::GlobalDecl(GlobalDecl { ty, init }))
  }
}

/// Load.
#[derive(Debug, PartialEq)]
pub struct Load {
  pub symbol: String,
}

impl Load {
  /// Creates a new box of `Load` AST.
  pub fn new(span: Span, symbol: String) -> AstBox {
    Ast::new(span, AstKind::Load(Load { symbol }))
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
  pub fn new(span: Span, value: AstBox, symbol: String) -> AstBox {
    Ast::new(span, AstKind::Store(Store { value, symbol }))
  }
}

/// Pointer calculation.
#[derive(Debug, PartialEq)]
pub struct GetPointer {
  pub symbol: String,
  pub value: AstBox,
  pub step: Option<i32>,
}

impl GetPointer {
  /// Creates a new box of `GetPointer` AST.
  pub fn new(span: Span, symbol: String, value: AstBox, step: Option<i32>) -> AstBox {
    Ast::new(
      span,
      AstKind::GetPointer(GetPointer {
        symbol,
        value,
        step,
      }),
    )
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
  pub fn new(span: Span, op: BinaryOp, lhs: AstBox, rhs: AstBox) -> AstBox {
    Ast::new(span, AstKind::BinaryExpr(BinaryExpr { op, lhs, rhs }))
  }
}

/// Unary expression.
#[derive(Debug, PartialEq)]
pub struct UnaryExpr {
  pub op: UnaryOp,
  pub opr: AstBox,
}

impl UnaryExpr {
  /// Creates a new box of `UnaryExpr` AST.
  pub fn new(span: Span, op: UnaryOp, opr: AstBox) -> AstBox {
    Ast::new(span, AstKind::UnaryExpr(UnaryExpr { op, opr }))
  }
}

/// Branch.
#[derive(Debug, PartialEq)]
pub struct Branch {
  pub cond: AstBox,
  pub tbb: String,
  pub fbb: String,
}

impl Branch {
  /// Creates a new box of `Branch` AST.
  pub fn new(span: Span, cond: AstBox, tbb: String, fbb: String) -> AstBox {
    Ast::new(span, AstKind::Branch(Branch { cond, tbb, fbb }))
  }
}

/// Jump.
#[derive(Debug, PartialEq)]
pub struct Jump {
  pub target: String,
}

impl Jump {
  /// Creates a new box of `Jump` AST.
  pub fn new(span: Span, target: String) -> AstBox {
    Ast::new(span, AstKind::Jump(Jump { target }))
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
  pub fn new(span: Span, fun: String, args: Vec<AstBox>) -> AstBox {
    Ast::new(span, AstKind::FunCall(FunCall { fun, args }))
  }
}

/// Return.
#[derive(Debug, PartialEq)]
pub struct Return {
  pub value: Option<AstBox>,
}

impl Return {
  /// Creates a new box of `Return` AST.
  pub fn new(span: Span, value: Option<AstBox>) -> AstBox {
    Ast::new(span, AstKind::Return(Return { value }))
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
  pub fn new(
    span: Span,
    name: String,
    params: Vec<(String, AstBox)>,
    ret: Option<AstBox>,
    bbs: Vec<AstBox>,
  ) -> AstBox {
    Ast::new(
      span,
      AstKind::FunDef(FunDef {
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
  pub stmts: Vec<AstBox>,
}

impl Block {
  /// Creates a new box of `Block` AST.
  pub fn new(span: Span, name: String, stmts: Vec<AstBox>) -> AstBox {
    Ast::new(span, AstKind::Block(Block { name, stmts }))
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
  pub fn new(span: Span, name: String, params: Vec<AstBox>, ret: Option<AstBox>) -> AstBox {
    Ast::new(span, AstKind::FunDecl(FunDecl { name, params, ret }))
  }
}

/// Phi function.
#[derive(Debug, PartialEq)]
pub struct Phi {
  pub oprs: Vec<(AstBox, String)>,
}

impl Phi {
  /// Creates a new box of `Phi` AST.
  pub fn new(span: Span, oprs: Vec<(AstBox, String)>) -> AstBox {
    Ast::new(span, AstKind::Phi(Phi { oprs }))
  }
}

/// End of file.
#[derive(Debug, PartialEq)]
pub struct End;

impl End {
  /// Creates a new box of `End` AST.
  pub fn new(span: Span) -> AstBox {
    Ast::new(span, AstKind::End(End))
  }
}

/// Error
#[derive(Debug, PartialEq)]
pub struct Error;

impl Error {
  /// Creates a new box of `Error` AST.
  pub fn new(span: Span) -> AstBox {
    Ast::new(span, AstKind::Error(Error))
  }
}
