use crate::front::ast::{self, AstBox, AstKind};
use crate::front::span::{Error, Span};
use crate::ir::core::{ValueKind, ValueRc};
use crate::ir::instructions as inst;
use crate::ir::structs::{self, BasicBlockRc, BasicBlockRef, FunctionRc, FunctionRef, Program};
use crate::ir::types::{Type, TypeKind};
use crate::ir::values;
use crate::{log_error, log_warning, return_error};
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

/// Basic block information.
struct BasicBlockInfo {
  bb: BasicBlockRc,
  preds: Vec<String>,
  local_defs: HashMap<String, ValueRc>,
  /// All uninitialized phi functions and there indices in statement list.
  phis: Vec<(ValueRc, usize)>,
}

impl BasicBlockInfo {
  fn new(bb: BasicBlockRc) -> Self {
    Self {
      bb,
      preds: Vec::new(),
      local_defs: HashMap::new(),
      phis: Vec::new(),
    }
  }
}

/// Builder for building Koopa IR from AST.
pub struct Builder {
  program: Program,
  global_vars: HashMap<String, ValueRc>,
  global_funcs: HashMap<String, FunctionRef>,
  local_bbs: HashMap<String, BasicBlockInfo>,
  local_symbols: HashSet<String>,
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
      program: Program::new(),
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
  ///
  /// Available only when no error has occurred.
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
        alloc.inner_mut().set_name(Some(ast.name.clone()));
      }
      // add to global variable map
      if self.global_funcs.contains_key(&ast.name)
        || self
          .global_vars
          .insert(ast.name.clone(), alloc.clone())
          .is_some()
      {
        log_error!(
          span,
          "global symbol '{}' has already been defined",
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
        arg.inner_mut().set_name(Some(name.clone()));
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
    if self.global_vars.contains_key(&ast.name)
      || self
        .global_funcs
        .insert(ast.name.clone(), Rc::downgrade(&def))
        .is_some()
    {
      log_error!(
        span,
        "global symbol '{}' has already been defined",
        ast.name
      );
    }
    // add to program
    self.program.add_func(def.clone());
    // reset local symbol set
    self.local_symbols.clear();
    // get basic block list
    let bbs = self.get_block_list(&ast.bbs);
    // initialize local basic block map
    self.init_local_bbs(def, args, &bbs);
    // build on all basic blocks
    for block in &bbs {
      self.build_on_block(&ret_ty, block);
    }
    // add generated instructions to basic blocks
    self.replace_phis(&bbs);
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
    if self.global_vars.contains_key(&ast.name)
      || self
        .global_funcs
        .insert(ast.name.clone(), Rc::downgrade(&decl))
        .is_some()
    {
      log_error!(
        span,
        "global symbol '{}' has already been defined",
        ast.name
      );
    }
    // add to program
    self.program.add_func(decl);
  }

  /// Gets basic block list in BFS order.
  fn get_block_list<'a>(&self, bbs: &'a [AstBox]) -> Vec<&'a ast::Block> {
    // initialize queue and set
    let mut queue = VecDeque::new();
    let mut visited = HashSet::new();
    let entry_bb_name = &unwrap_ast!(bbs.first().unwrap(), Block).name;
    queue.push_back(entry_bb_name);
    // initialize basic block map
    let mut bb_map = HashMap::new();
    for bb in bbs {
      let block = unwrap_ast!(bb, Block);
      if bb_map.insert(&block.name, (&bb.span, block)).is_some() {
        log_error!(
          bb.span,
          "basic block '{}' has already been defined",
          block.name
        );
      }
    }
    // visit blocks
    let mut bb_list = Vec::new();
    while let Some(bb) = queue.pop_front() {
      if visited.insert(bb) {
        let info = bb_map[bb];
        // add to basic block list
        bb_list.push(info.1);
        // add the successors to queue
        let last_stmt = info.1.stmts.last().unwrap();
        let mut add_target = |bb_name| {
          if bb_name == entry_bb_name {
            log_error!(
              last_stmt.span,
              "the entry basic block should not have any predecessors"
            );
          } else if bb_map.contains_key(bb_name) {
            queue.push_back(bb_name);
          } else {
            log_error!(last_stmt.span, "invalid basic block name '{}'", bb_name);
          }
        };
        match &last_stmt.kind {
          AstKind::Branch(ast::Branch { cond: _, tbb, fbb }) => {
            add_target(tbb);
            add_target(fbb);
          }
          AstKind::Jump(ast::Jump { target }) => add_target(target),
          AstKind::Return(_) | AstKind::Error(_) => {}
          _ => panic!("invalid end statement"),
        }
      }
    }
    // check if there are any unvisited blocks
    for (bb_name, (span, _)) in bb_map {
      if !visited.contains(bb_name) {
        log_warning!(span, "basic block '{}' is unreachable, skipped", bb_name);
      }
    }
    bb_list
  }

  /// Initializes local basic block map.
  fn init_local_bbs(
    &mut self,
    def: FunctionRc,
    args: HashMap<String, ValueRc>,
    bbs: &[&ast::Block],
  ) {
    // create all basic blocks
    self.local_bbs = bbs
      .iter()
      .map(|block| {
        let bb = structs::BasicBlock::new((!block.name.is_temp()).then(|| block.name.clone()));
        // add to the current function
        def.inner_mut().add_bb(bb.clone());
        (block.name.clone(), BasicBlockInfo::new(bb))
      })
      .collect();
    // add argument references to the entry basic block
    let entry_bb_name = &bbs[0].name;
    let entry_info = &mut self.local_bbs.get_mut(entry_bb_name).unwrap();
    entry_info.local_defs = args;
    // fill predecessors
    for block in bbs {
      let last_inst = block.stmts.last().unwrap();
      let mut add_pred = |bb_name| {
        self
          .local_bbs
          .get_mut(bb_name)
          .unwrap()
          .preds
          .push(block.name.clone());
      };
      match &last_inst.kind {
        AstKind::Branch(ast::Branch { cond: _, tbb, fbb }) => {
          add_pred(tbb);
          add_pred(fbb);
        }
        AstKind::Jump(ast::Jump { target }) => add_pred(target),
        _ => {}
      }
    }
  }

  /// Builds on basic blocks.
  fn build_on_block(&mut self, ret_ty: &Type, ast: &ast::Block) {
    // generate each statements
    for (i, stmt) in ast.stmts.iter().enumerate() {
      if let Ok(stmt) = self.generate_stmt(&ast.name, ret_ty, &stmt) {
        let info = self.local_bbs.get_mut(&ast.name).unwrap();
        // record `stmt` if the current statement is a phi function
        if matches!(stmt.kind(), ValueKind::Phi(..)) {
          info.phis.push((stmt.clone(), i));
        }
        // add statement to the current basic block
        info.bb.inner_mut().add_inst(stmt);
      }
    }
  }

  /// Handles all uninitialized phi functions, replaces them with correct phi functions.
  fn replace_phis(&self, bbs: &[&ast::Block]) {
    let mut phis = Vec::new();
    for block in bbs {
      let info = &self.local_bbs[&block.name];
      for (old, i) in &info.phis {
        // generate the current phi function
        let ast = &block.stmts[*i];
        let def = unwrap_ast!(ast, SymbolDef);
        let phi = unwrap_ast!(def.value, Phi);
        if let Ok(new) = self.generate_phi(&ast.span, &block.name, phi) {
          // set value name
          if !def.name.is_temp() {
            new.inner_mut().set_name(Some(def.name.clone()));
          }
          // store the old phi and the new phi
          phis.push((old, new.clone()));
          // replace the phi function in the current basic block
          info.bb.inner_mut().replace_inst(old, new);
        }
      }
    }
    // replace all old uninitialized phis to new phis
    for (old, new) in phis {
      old.inner_mut().replace_all_uses_with(Some(new));
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
        if !ty.is_i32() {
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
    // if not found, find symbol in local definitions
    self
      .global_vars
      .get(symbol)
      .cloned()
      .or_else(|| self.generate_local_symbol(bb_name, symbol))
      .ok_or_else(|| return_error!(span, "symbol '{}' not found", symbol))
  }

  /// Generates the symbol locally by the symbol name.
  fn generate_local_symbol(&self, bb_name: &str, symbol: &str) -> Option<ValueRc> {
    // find symbol in local scope of the current basic block
    // if not found, try to find symbol in all predecessors
    let bb_info = &self.local_bbs[bb_name];
    bb_info.local_defs.get(symbol).cloned().or_else(|| {
      bb_info
        .preds
        .iter()
        .find_map(|pred| self.generate_local_symbol(pred, symbol))
    })
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
        if self.global_vars.contains_key(&def.name) || !self.local_symbols.insert(def.name.clone())
        {
          log_error!(ast.span, "symbol '{}' has already been defined", def.name);
        }
        // generate the value of the instruction
        let inst = self.generate_inst(bb_name, &def.value)?;
        // check type
        if inst.ty().is_unit() {
          return_error!(
            ast.span,
            "symbol '{}' is defined as a unit type, which is not allowed",
            def.name
          );
        }
        // set value name
        if !def.name.is_temp() {
          inst.inner_mut().set_name(Some(def.name.clone()));
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
      AstKind::Phi(ast) => self.generate_uninit_phi(ast),
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
    if !ret_ty.is_unit() && ast.value.is_none() {
      return_error!(
        span,
        "expected return type '{}', but returned nothing",
        ret_ty
      );
    }
    if ret_ty.is_unit() && ast.value.is_some() {
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

  /// Generates uninitialized phi functions.
  fn generate_uninit_phi(&self, ast: &ast::Phi) -> ValueResult {
    Ok(inst::Phi::new_uninit(self.generate_type(&ast.ty)))
  }

  /// Generates phi functions.
  fn generate_phi(&self, span: &Span, bb_name: &str, ast: &ast::Phi) -> ValueResult {
    let bb_info = &self.local_bbs[bb_name];
    let opr_len = bb_info.preds.len();
    // check the length of operand list
    if opr_len == 0 {
      return_error!(
        span,
        "invalid phi function, because the current basic block '{}' has no predecessor",
        bb_name
      );
    } else if ast.oprs.len() != opr_len {
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
    if let Some(bb) = ast
      .oprs
      .iter()
      .find_map(|(_, bb)| (!bb_info.preds.iter().any(|p| p == bb)).then(|| bb))
    {
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
    let ty = self.generate_type(&ast.ty);
    Ok(inst::Phi::new(
      ast
        .oprs
        .iter()
        .map(|(v, bb)| {
          Ok((
            self.generate_value(bb, &ty, v)?,
            Rc::downgrade(&self.local_bbs[bb].bb),
          ))
        })
        .collect::<Result<_, _>>()?,
    ))
  }
}

impl Default for Builder {
  fn default() -> Self {
    Builder::new()
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
      self.into()
    }
  }
}
