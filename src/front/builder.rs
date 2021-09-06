use crate::front::ast::{self, AstBox, AstKind};
use crate::front::span::{Error, Span};
use crate::ir::core::ValueRc;
use crate::ir::instructions as inst;
use crate::ir::structs::{self, BasicBlockRc, BasicBlockRef, FunctionRc, FunctionRef, Program};
use crate::ir::types::{Type, TypeKind};
use crate::ir::values;
use crate::{log_error, log_warning, return_error};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Builder for building Koopa IR from AST.
pub struct Builder {
  program: Program,
  global_vars: HashMap<String, ValueRc>,
  global_funcs: HashMap<String, FunctionRef>,
  local_bbs: HashMap<String, BasicBlockInfo>,
  local_symbols: HashSet<String>,
}

/// Basic block information.
struct BasicBlockInfo {
  bb: BasicBlockRc,
  preds: Vec<String>,
  local_defs: HashMap<String, ValueRc>,
}

/// Result returned by value generator methods in `Builder`.
type ValueResult = Result<ValueRc, Error>;

/// Unwraps the specific AST by its kind.
macro_rules! unwrap_ast {
  ($ast:expr, $kind:ident) => {
    match &$ast.kind {
      AstKind::$kind(ast) => ast,
      _ => panic!("invalid `{}` AST", stringify!($kind)),
    }
  };
}

impl Builder {
  /// Creates a new builder.
  pub fn new() -> Self {
    Self {
      program: Program::default(),
      global_vars: HashMap::new(),
      global_funcs: HashMap::new(),
      local_bbs: HashMap::new(),
      local_symbols: HashSet::new(),
    }
  }

  /// Builds the specific AST into IR.
  pub fn build_on(&mut self, ast: &AstBox) {
    match &ast.kind {
      AstKind::GlobalDef(def) => self.build_on_global_def(&ast.span, def),
      AstKind::FunDef(def) => self.build_on_fun_def(&ast.span, def),
      AstKind::FunDecl(decl) => self.build_on_fun_decl(&ast.span, decl),
      AstKind::Error(_) | AstKind::End(_) => { /* ignore errors and ends */ }
      _ => panic!("invalid AST input"),
    }
  }

  /// Consumes and get the generated program.
  pub fn program(self) -> Program {
    self.program
  }

  /// Builds on global symbol definitions.
  fn build_on_global_def(&mut self, span: &Span, ast: &ast::GlobalDef) {
    // create global allocation
    let decl = unwrap_ast!(ast.value, GlobalDecl);
    if let Ok(init) = self.generate_init(&self.generate_type(&decl.ty), &decl.init) {
      let alloc = inst::GlobalAlloc::new(init);
      // set name for the created value
      if !ast.name.is_temp() {
        alloc.borrow_mut().set_name(Some(ast.name.clone()));
      }
      // add to global variable map
      if self
        .global_vars
        .insert(ast.name.clone(), alloc.clone())
        .is_some()
      {
        log_error!(
          span,
          "global variable '{}' has already been defined",
          ast.name
        );
      }
      // add to program
      self.program.add_var(alloc);
    }
  }

  /// Builds on function definitions.
  fn build_on_fun_def(&mut self, span: &Span, ast: &ast::FunDef) {
    // create argument references
    let args = ast.params.iter().enumerate().map(|(i, (name, ty))| {
      // create argument reference
      let arg = values::ArgRef::new(self.generate_type(ty), i);
      if !name.is_temp() {
        arg.borrow_mut().set_name(Some(name.clone()));
      }
      (name.clone(), arg)
    });
    let args: HashMap<_, _> = args.collect();
    // create function definition
    let ret_ty = ast
      .ret
      .as_ref()
      .map_or(Type::get_unit(), |a| self.generate_type(a));
    let def = structs::Function::new(
      ast.name.clone(),
      args.values().cloned().collect(),
      ret_ty.clone(),
    );
    // add to global function map
    if self
      .global_funcs
      .insert(ast.name.clone(), Rc::downgrade(&def))
      .is_some()
    {
      log_error!(span, "function '{}' has already been defined", ast.name);
    }
    // add to program
    self.program.add_func(def.clone());
    // initialize local basic block map
    self.init_local_bbs(def, args, &ast.bbs);
    // reset local symbol set
    self.local_symbols.clear();
    // build on all basic blocks
    for bb in &ast.bbs {
      self.build_on_block(&ret_ty, unwrap_ast!(bb, Block));
    }
  }

  /// Builds on function declarations.
  fn build_on_fun_decl(&mut self, span: &Span, ast: &ast::FunDecl) {
    // get function type
    let ty = Type::get_function(
      ast.params.iter().map(|a| self.generate_type(a)).collect(),
      ast
        .ret
        .as_ref()
        .map_or(Type::get_unit(), |a| self.generate_type(a)),
    );
    // create function declaration
    let decl = structs::Function::new_decl(ast.name.clone(), ty);
    // add to global function map
    if self
      .global_funcs
      .insert(ast.name.clone(), Rc::downgrade(&decl))
      .is_some()
    {
      log_error!(span, "function '{}' has already been defined", ast.name);
    }
    // add to program
    self.program.add_func(decl);
  }

  /// Initializes local basic block map.
  fn init_local_bbs(&mut self, def: FunctionRc, args: HashMap<String, ValueRc>, bbs: &[AstBox]) {
    // create all basic blocks
    self.local_bbs.clear();
    for bb in bbs {
      let block = unwrap_ast!(bb, Block);
      let span = &bb.span;
      let bb = structs::BasicBlock::new((!block.name.is_temp()).then(|| block.name.clone()));
      // add to local basic block map
      if self
        .local_bbs
        .insert(
          block.name.clone(),
          BasicBlockInfo {
            bb: bb.clone(),
            preds: Vec::new(),
            local_defs: HashMap::new(),
          },
        )
        .is_some()
      {
        log_error!(
          span,
          "basic block '{}' has already been defined",
          block.name
        );
      }
      // add to the current function
      def.borrow_mut().add_bb(bb);
    }
    // add argument references to the entry basic block
    let first_bb = unwrap_ast!(bbs.first().unwrap(), Block);
    let first_bb_info = &mut self.local_bbs.get_mut(&first_bb.name).unwrap();
    first_bb_info.local_defs = args;
    // fill predecessors
    for bb in bbs {
      let block = unwrap_ast!(bb, Block);
      let last_inst = block.stmts.last().unwrap();
      let mut add_pred = |bb_name| {
        if let Some(info) = self.local_bbs.get_mut(bb_name) {
          info.preds.push(block.name.clone());
        } else {
          log_error!(last_inst.span, "invalid basic block name {}", bb_name);
        }
      };
      match &last_inst.kind {
        AstKind::Branch(ast::Branch { cond: _, tbb, fbb }) => {
          add_pred(tbb);
          add_pred(fbb);
        }
        AstKind::Jump(ast::Jump { target }) => add_pred(target),
        AstKind::Return(_) | AstKind::Error(_) => {}
        _ => panic!("invalid end statement"),
      }
    }
  }

  /// Builds on basic blocks.
  fn build_on_block(&mut self, ret_ty: &Type, ast: &ast::Block) {
    // generate each statements
    for stmt in &ast.stmts {
      if let Ok(stmt) = self.generate_stmt(&ast.name, &ret_ty, &stmt) {
        // add value to the current basic block
        self.local_bbs[&ast.name].bb.borrow_mut().add_inst(stmt);
      }
    }
  }

  /// Generates the type by the specific AST.
  fn generate_type(&self, ast: &AstBox) -> Type {
    match &ast.kind {
      AstKind::IntType(_) => Type::get_i32(),
      AstKind::ArrayType(ast) => Type::get_array(self.generate_type(&ast.base), ast.len),
      AstKind::PointerType(ast) => Type::get_pointer(self.generate_type(&ast.base)),
      AstKind::FunType(ast) => Type::get_function(
        ast.params.iter().map(|a| self.generate_type(a)).collect(),
        ast
          .ret
          .as_ref()
          .map_or(Type::get_unit(), |a| self.generate_type(a)),
      ),
      _ => panic!("invalid type AST"),
    }
  }

  /// Generates the initializer by the specific AST.
  fn generate_init(&self, ty: &Type, ast: &AstBox) -> ValueResult {
    match &ast.kind {
      AstKind::UndefVal(_) => Ok(values::Undef::get(ty.clone())),
      AstKind::ZeroInit(_) => Ok(values::ZeroInit::get(ty.clone())),
      AstKind::IntVal(int) => {
        if !matches!(ty.kind(), TypeKind::Int32) {
          return_error!(
            ast.span,
            "expected type '{}', but it can not be applied to integers",
            ty
          );
        }
        Ok(values::Integer::get(int.value))
      }
      AstKind::Aggregate(agg) => {
        let ty = match ty.kind() {
          TypeKind::Array(base, len) => {
            if *len != agg.elems.len() {
              log_error!(
                ast.span,
                "expected array length {}, found length {}",
                len,
                agg.elems.len()
              );
            }
            base
          }
          TypeKind::Pointer(base) => base,
          _ => return_error!(ast.span, "invalid aggregate type '{}'", ty),
        };
        Ok(values::Aggregate::new(
          agg
            .elems
            .iter()
            .map(|e| self.generate_init(ty, e))
            .collect::<Result<_, _>>()?,
        ))
      }
      _ => panic!("invalid initializer AST"),
    }
  }

  /// Generates the value by the specific AST.
  fn generate_value(&self, bb_name: &str, ty: &Type, ast: &AstBox) -> ValueResult {
    match &ast.kind {
      AstKind::SymbolRef(sym) => {
        let value = self.generate_symbol(&ast.span, bb_name, &sym.symbol)?;
        // check the type of the value to prevent duplication of definitions
        if value.ty() == ty {
          Ok(value)
        } else {
          return_error!(
            ast.span,
            "type mismatch, expected '{}', found '{}'",
            ty,
            value.ty()
          )
        }
      }
      _ => self.generate_init(ty, ast),
    }
  }

  /// Generates the symbol by the symbol name.
  fn generate_symbol(&self, span: &Span, bb_name: &str, symbol: &str) -> ValueResult {
    // try to find symbol in global scope
    if let Some(value) = self.global_vars.get(symbol) {
      Ok(value.clone())
    } else {
      // not found, find symbol in local definitions
      self.generate_local_symbol(span, bb_name, symbol)
    }
  }

  /// Generates the symbol locally by the symbol name.
  fn generate_local_symbol(&self, span: &Span, bb_name: &str, symbol: &str) -> ValueResult {
    let bb_info = &self.local_bbs[bb_name];
    if let Some(value) = bb_info.local_defs.get(symbol) {
      // symbol found in the current basic block
      Ok(value.clone())
    } else if !bb_info.preds.is_empty() {
      // symbol not found, try to find in all predecessors
      if let Some(value) = bb_info
        .preds
        .iter()
        .find_map(|pred| self.generate_local_symbol(span, pred, symbol).ok())
      {
        Ok(value)
      } else {
        // symbol not found
        return_error!(span, "symbol '{}' not found", symbol);
      }
    } else {
      // symbol not found
      return_error!(span, "symbol '{}' not found", symbol);
    }
  }

  /// Generates the basic block reference by the basic block name.
  fn generate_bb_ref(&self, span: &Span, bb_name: &str) -> Result<BasicBlockRef, Error> {
    if let Some(info) = self.local_bbs.get(bb_name) {
      Ok(Rc::downgrade(&info.bb))
    } else {
      return_error!(span, "invalid basic block name '{}'", bb_name)
    }
  }

  /// Generates the statement by the specific AST.
  fn generate_stmt(&mut self, bb_name: &str, ret_ty: &Type, ast: &AstBox) -> ValueResult {
    match &ast.kind {
      AstKind::Store(store) => self.generate_store(&ast.span, bb_name, store),
      AstKind::Branch(br) => self.generate_branch(&ast.span, bb_name, br),
      AstKind::Jump(jump) => self.generate_jump(&ast.span, jump),
      AstKind::FunCall(call) => self.generate_fun_call(&ast.span, bb_name, call),
      AstKind::Return(ret) => self.generate_return(&ast.span, bb_name, ret_ty, ret),
      AstKind::Error(_) => Error::default().into(),
      AstKind::SymbolDef(def) => {
        // check if has already been defined
        if self.global_vars.get(&def.name).is_some() || !self.local_symbols.insert(def.name.clone())
        {
          log_error!(ast.span, "symbol '{}' has already been defined", def.name);
        }
        // generate the value of the instruction
        let inst = match &def.value.kind {
          AstKind::Phi(phi) => {
            // insert an uninitialized phi to break circular reference
            let ty = self.generate_type(&phi.ty);
            let uninit_phi = inst::Phi::new_uninit(ty.clone());
            self
              .local_bbs
              .get_mut(bb_name)
              .unwrap()
              .local_defs
              .insert(def.name.clone(), uninit_phi.clone());
            // get phi function
            let phi = self.generate_phi(&def.value.span, bb_name, &ty, phi)?;
            uninit_phi
              .borrow_mut()
              .replace_all_uses_with(Some(phi.clone()));
            phi
          }
          _ => self.generate_inst(bb_name, &def.value)?,
        };
        // check type
        if matches!(inst.ty().kind(), TypeKind::Unit) {
          return_error!(
            ast.span,
            "symbol '{}' is defined as a unit type, which is not allowed",
            def.name
          );
        }
        // add to local basic block
        self
          .local_bbs
          .get_mut(bb_name)
          .unwrap()
          .local_defs
          .insert(def.name.clone(), inst.clone());
        Ok(inst)
      }
      _ => panic!("invalid statement"),
    }
  }

  /// Generates the instruction by the specific AST.
  fn generate_inst(&self, bb_name: &str, ast: &AstBox) -> ValueResult {
    match &ast.kind {
      AstKind::MemDecl(ast) => self.generate_mem_decl(ast),
      AstKind::Load(load) => self.generate_load(&ast.span, bb_name, load),
      AstKind::GetPointer(gp) => self.generate_get_pointer(&ast.span, bb_name, gp),
      AstKind::GetElementPointer(gep) => self.generate_get_element_pointer(&ast.span, bb_name, gep),
      AstKind::BinaryExpr(ast) => self.generate_binary_expr(bb_name, ast),
      AstKind::UnaryExpr(ast) => self.generate_unary_expr(bb_name, ast),
      AstKind::FunCall(call) => self.generate_fun_call(&ast.span, bb_name, call),
      _ => panic!("invalid instruction"),
    }
  }

  /// Generates memory declarations.
  fn generate_mem_decl(&self, ast: &ast::MemDecl) -> ValueResult {
    Ok(inst::Alloc::new(self.generate_type(&ast.ty)))
  }

  /// Generates loads.
  fn generate_load(&self, span: &Span, bb_name: &str, ast: &ast::Load) -> ValueResult {
    // get source value
    let src = self.generate_symbol(span, bb_name, &ast.symbol)?;
    // check source type
    if !matches!(src.ty().kind(), TypeKind::Pointer(..)) {
      return_error!(span, "expected pointer type, found '{}'", src.ty());
    }
    Ok(inst::Load::new(src))
  }

  /// Generates stores.
  fn generate_store(&self, span: &Span, bb_name: &str, ast: &ast::Store) -> ValueResult {
    // get destination value
    let dest = self.generate_symbol(span, bb_name, &ast.symbol)?;
    // check destination type & get source type
    let src_ty = match dest.ty().kind() {
      TypeKind::Pointer(base) => base,
      _ => return_error!(span, "expected pointer type, found '{}'", dest.ty()),
    };
    // get source value
    let value = self.generate_value(bb_name, src_ty, &ast.value)?;
    Ok(inst::Store::new(value, dest))
  }

  /// Generates pointer calculations.
  fn generate_get_pointer(&self, span: &Span, bb_name: &str, ast: &ast::GetPointer) -> ValueResult {
    // get source value
    let src = self.generate_symbol(span, bb_name, &ast.symbol)?;
    if !matches!(src.ty().kind(), TypeKind::Pointer(..)) {
      return_error!(span, "expected pointer type, found '{}'", src.ty());
    }
    // get index
    let index = self.generate_value(bb_name, &Type::get_i32(), &ast.value)?;
    Ok(inst::GetPtr::new(src, index))
  }

  /// Generates element pointer calculations.
  fn generate_get_element_pointer(
    &self,
    span: &Span,
    bb_name: &str,
    ast: &ast::GetElementPointer,
  ) -> ValueResult {
    // get source value
    let src = self.generate_symbol(span, bb_name, &ast.symbol)?;
    if !matches!(src.ty().kind(), TypeKind::Pointer(ty) if matches!(ty.kind(), TypeKind::Array(..)))
    {
      return_error!(span, "expected a pointer of array, found '{}'", src.ty());
    }
    // get index
    let index = self.generate_value(bb_name, &Type::get_i32(), &ast.value)?;
    Ok(inst::GetElemPtr::new(src, index))
  }

  /// Generates binary expressions.
  fn generate_binary_expr(&self, bb_name: &str, ast: &ast::BinaryExpr) -> ValueResult {
    let ty = Type::get_i32();
    // get lhs & rhs
    let lhs = self.generate_value(bb_name, &ty, &ast.lhs)?;
    let rhs = self.generate_value(bb_name, &ty, &ast.rhs)?;
    Ok(inst::Binary::new(ast.op, lhs, rhs))
  }

  /// Generates unary expressions.
  fn generate_unary_expr(&self, bb_name: &str, ast: &ast::UnaryExpr) -> ValueResult {
    // get operand
    let opr = self.generate_value(bb_name, &Type::get_i32(), &ast.opr)?;
    Ok(inst::Unary::new(ast.op, opr))
  }

  /// Generates branchs.
  fn generate_branch(&self, span: &Span, bb_name: &str, ast: &ast::Branch) -> ValueResult {
    // get condition
    let cond = self.generate_value(bb_name, &Type::get_i32(), &ast.cond)?;
    // get target basic blocks
    let tbb = self.generate_bb_ref(span, &ast.tbb)?;
    let fbb = self.generate_bb_ref(span, &ast.fbb)?;
    Ok(inst::Branch::new(cond, tbb, fbb))
  }

  /// Generates jumps.
  fn generate_jump(&self, span: &Span, ast: &ast::Jump) -> ValueResult {
    Ok(inst::Jump::new(self.generate_bb_ref(span, &ast.target)?))
  }

  /// Generates function calls.
  fn generate_fun_call(&self, span: &Span, bb_name: &str, ast: &ast::FunCall) -> ValueResult {
    // get callee
    let callee = self
      .global_funcs
      .get(&ast.fun)
      .ok_or_else(|| log_error!(span, "function '{}' not found", ast.fun))?;
    // get arguments
    match callee.upgrade().unwrap().ty().kind() {
      TypeKind::Function(args, _) => {
        // check length of argument list
        if args.len() != ast.args.len() {
          return_error!(
            span,
            "expected {} {}, found {} {}",
            args.len(),
            "arguments".to_plural(args.len()),
            ast.args.len(),
            "arguments".to_plural(ast.args.len())
          );
        }
        Ok(inst::Call::new(
          callee.clone(),
          ast
            .args
            .iter()
            .zip(args)
            .map(|(a, ty)| self.generate_value(bb_name, ty, a))
            .collect::<Result<_, _>>()?,
        ))
      }
      _ => panic!("invalid function"),
    }
  }

  /// Generates returns.
  fn generate_return(
    &self,
    span: &Span,
    bb_name: &str,
    ret_ty: &Type,
    ast: &ast::Return,
  ) -> ValueResult {
    // check return type
    let has_ret = !matches!(ret_ty.kind(), TypeKind::Unit);
    if has_ret && ast.value.is_none() {
      return_error!(
        span,
        "expected return type '{}', but returned nothing",
        ret_ty
      );
    }
    if !has_ret && ast.value.is_some() {
      return_error!(
        span,
        "function has no return value, but a value has been returned"
      );
    }
    Ok(inst::Return::new(
      ast
        .value
        .as_ref()
        .map(|v| self.generate_value(bb_name, ret_ty, v))
        .transpose()?,
    ))
  }

  /// Generates phi functions.
  fn generate_phi(&self, span: &Span, bb_name: &str, ty: &Type, ast: &ast::Phi) -> ValueResult {
    let bb_info = &self.local_bbs[bb_name];
    let opr_len = bb_info.preds.len();
    // check the length of operand list
    if opr_len == 0 {
      return_error!(
        span,
        "invalid phi function, because the current basic block '{}' has no predecessor",
        bb_name
      );
    }
    if ast.oprs.len() != opr_len {
      return_error!(
        span,
        "expected {} {}, found {} {}",
        opr_len,
        "operand".to_plural(opr_len),
        ast.oprs.len(),
        "operand".to_plural(ast.oprs.len())
      );
    }
    // check if all operands are valid
    if let Some(bb) = ast.oprs.iter().find_map(|(_, bb)| {
      bb_info
        .preds
        .iter()
        .find(|&p| p == bb)
        .is_none()
        .then(|| bb)
    }) {
      return_error!(
        span,
        "basic block '{}' is not a predecessor of the current basic block '{}'",
        bb,
        bb_name
      );
    }
    // check if is a redundant phi function
    if opr_len == 1 {
      log_warning!(span, "consider removing this redundant phi function");
    }
    Ok(inst::Phi::new(
      ast
        .oprs
        .iter()
        .map(|(v, bb)| {
          Ok((
            self.generate_value(bb_name, ty, v)?,
            Rc::downgrade(&self.local_bbs[bb].bb),
          ))
        })
        .collect::<Result<_, _>>()?,
    ))
  }
}

/// Helper trait, for checking if the symbol name is a temporary name.
trait Symbol {
  fn is_temp(&self) -> bool;
}

impl Symbol for String {
  fn is_temp(&self) -> bool {
    self.chars().all(|c| c == '%' || c.is_numeric())
  }
}

/// Helper trait, for getting plural form of a specific word.
trait ToPlural {
  fn to_plural(self, num: usize) -> String;
}

impl ToPlural for &str {
  fn to_plural(self, num: usize) -> String {
    if num > 1 {
      format!("{}s", self)
    } else {
      format!("{}", self)
    }
  }
}
