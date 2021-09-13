use crate::ir::core::Value;
use crate::ir::structs::{BasicBlock, Function};
use std::borrow::Borrow;
use std::cell::{RefCell, RefMut};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// A manager for storing names and allocating unique temporary
/// names of global variables, functions, basic blocks and values.
pub struct NameManager(Rc<RefCell<NameManagerImpl>>);

#[derive(Default)]
struct NameManagerImpl {
  next_id: usize,
  cur_scope: ScopeKind,
  global_names: HashSet<StringRc>,
  bb_names: HashSet<StringRc>,
  global_vars: HashMap<*const Value, Rc<String>>,
  funcs: HashMap<*const Function, Rc<String>>,
  bbs: HashMap<*const BasicBlock, Rc<String>>,
  values: Option<HashMap<*const Value, Rc<String>>>,
}

impl NameManager {
  /// Creates a new `NameManager`.
  pub fn new() -> Self {
    Self(Rc::new(RefCell::new(NameManagerImpl::default())))
  }

  /// Enters the function scope. Call this method when generating
  /// basic blocks and local value.
  ///
  /// Returns a function scope guard which, when dropped, exits the function scope.
  pub fn enter_func_scope(&self) -> FunctionScopeGuard {
    let mut name_man = self.0.borrow_mut();
    match name_man.cur_scope {
      ScopeKind::Global => {
        name_man.cur_scope = ScopeKind::Function;
        name_man.values = Some(HashMap::new());
        FunctionScopeGuard(self.0.clone())
      }
      _ => panic!("already in function scope"),
    }
  }

  /// Gets the name of the specific function.
  pub fn get_func_name(&self, func: &Function) -> Rc<String> {
    let ptr: *const Function = func;
    if let Some(name) = self.0.as_ref().borrow().funcs.get(&ptr) {
      name.clone()
    } else {
      let name = self.next_name_str(func.name(), |r| &mut r.global_names);
      let mut name_man = self.0.borrow_mut();
      name_man.funcs.insert(ptr, name);
      name_man.funcs[&ptr].clone()
    }
  }

  /// Gets the name of the specific basic block.
  pub fn get_bb_name(&self, bb: &BasicBlock) -> Rc<String> {
    let ptr: *const BasicBlock = bb;
    if let Some(name) = self.0.as_ref().borrow().bbs.get(&ptr) {
      name.clone()
    } else {
      let name = self.next_name(bb.name(), |r| &mut r.bb_names);
      let mut name_man = self.0.borrow_mut();
      name_man.bbs.insert(ptr, name);
      name_man.bbs[&ptr].clone()
    }
  }

  /// Gets the name of the specific value.
  pub fn get_value_name(&self, value: &Value) -> Rc<String> {
    match self.0.as_ref().borrow().cur_scope {
      ScopeKind::Global => self.get_value_name_impl(value, |r| &mut r.global_vars),
      _ => self.get_value_name_impl(value, |r| r.values.as_mut().unwrap()),
    }
  }

  fn get_value_name_impl<F>(&self, value: &Value, value_set: F) -> Rc<String>
  where
    F: for<'a> Fn(&'a mut RefMut<NameManagerImpl>) -> &'a mut HashMap<*const Value, Rc<String>>,
  {
    let ptr: *const Value = value;
    let mut name_man = self.0.borrow_mut();
    if let Some(name) = value_set(&mut name_man).get(&ptr) {
      name.clone()
    } else {
      drop(name_man);
      let name = self.next_name(value.inner().name(), |r| &mut r.global_names);
      let mut name_man = self.0.borrow_mut();
      let values = value_set(&mut name_man);
      values.insert(ptr, name);
      values[&ptr].clone()
    }
  }

  /// Generates the next name by the specific `Option<String>`
  /// and stores it to the specific name set.
  fn next_name<F>(&self, name: &Option<String>, name_set: F) -> Rc<String>
  where
    F: for<'a> FnOnce(&'a mut RefMut<NameManagerImpl>) -> &'a mut HashSet<StringRc>,
  {
    // check if there is a name
    if let Some(name) = name {
      self.next_name_str(name, name_set)
    } else {
      // generate a temporary name
      let mut name_man = self.0.borrow_mut();
      let name = format!("%{}", name_man.next_id);
      name_man.next_id += 1;
      let names = name_set(&mut name_man);
      names.insert(name.clone().into());
      names.get(&name).unwrap().into_rc()
    }
  }

  /// Generates the next name by the specific string
  /// and stores it to the specific name set.
  fn next_name_str<F>(&self, name: &str, name_set: F) -> Rc<String>
  where
    F: for<'a> FnOnce(&'a mut RefMut<NameManagerImpl>) -> &'a mut HashSet<StringRc>,
  {
    let mut name_man = self.0.borrow_mut();
    let names = name_set(&mut name_man);
    // check for duplicate names
    if !names.contains(name) {
      names.insert(name.into());
      names.get(name).unwrap().into_rc()
    } else {
      // generate a new name
      for id in 0.. {
        let new_name = format!("{}_{}", name, id);
        if !names.contains(&new_name) {
          names.insert(new_name.clone().into());
          return names.get(&new_name).unwrap().into_rc();
        }
      }
      unreachable!()
    }
  }
}

/// Scope guard of the function scope.
pub struct FunctionScopeGuard(Rc<RefCell<NameManagerImpl>>);

impl Drop for FunctionScopeGuard {
  fn drop(&mut self) {
    let mut name_man = self.0.borrow_mut();
    let values = name_man.values.take().unwrap();
    for name in values.values() {
      name_man.global_names.remove(name);
    }
    name_man.cur_scope = ScopeKind::Global;
    name_man.bb_names.clear();
    name_man.bbs.clear();
  }
}

/// Kind of scope.
#[derive(Clone, Copy)]
enum ScopeKind {
  Global,
  Function,
}

impl Default for ScopeKind {
  fn default() -> Self {
    Self::Global
  }
}

/// `Rc<String>` that implements `Borrow<str>`.
#[derive(Clone, PartialEq, Eq, Hash)]
struct StringRc(Rc<String>);

impl StringRc {
  fn into_rc(&self) -> Rc<String> {
    self.0.clone()
  }
}

impl From<String> for StringRc {
  fn from(s: String) -> Self {
    Self(Rc::new(s))
  }
}

impl From<&str> for StringRc {
  fn from(s: &str) -> Self {
    Self(Rc::new(s.into()))
  }
}

impl Borrow<Rc<String>> for StringRc {
  fn borrow(&self) -> &Rc<String> {
    &self.0
  }
}

impl Borrow<String> for StringRc {
  fn borrow(&self) -> &String {
    self.0.as_ref()
  }
}

impl Borrow<str> for StringRc {
  fn borrow(&self) -> &str {
    self.0.as_ref()
  }
}

// /// Koopa IR generator.
// pub trait Generator {
//   /// The output type of all generator methods.
//   type Output;

//   fn generate_on(program: &Program) {
//     for var in program.vars() {
//       //
//     }
//     for func in program.funcs() {
//       //
//     }
//   }
// }
