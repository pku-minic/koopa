use super::{Function, NonNull, Type, TypeKind, Val};
use libloading::{Error, Library, Symbol};
use std::collections::HashMap;
use std::ffi::CString;
use std::io::{Error as IoError, ErrorKind, Result as IoResult};
use std::mem::transmute;

struct ExternFuncs<'lib> {
  libs: Vec<Library>,
  funcs: HashMap<String, Symbol<'lib, *const ()>>,
}

impl<'lib> ExternFuncs<'lib> {
  pub unsafe fn new(lib_files: &[&str]) -> Result<Self, Error> {
    Ok(Self {
      libs: lib_files
        .iter()
        .map(|f| Library::new(f))
        .collect::<Result<_, _>>()?,
      funcs: HashMap::new(),
    })
  }

  pub unsafe fn call(&'lib mut self, func: &Function, args: Vec<Val>) -> IoResult<Val> {
    assert!(func.inner().bbs().is_empty(), "expected function declaration");
    let name = func.name();
    let ret_ty = match func.ty().kind() {
      TypeKind::Function(_, ret) => ret,
      _ => panic!("invalid function"),
    };
    if let Some(sym) = self.funcs.get(name) {
      Self::call_ext_func(sym, args, ret_ty)
    } else {
      let sym_name =
        CString::new(name).map_err(|e| IoError::new(ErrorKind::Other, format!("{}", e)))?;
      let sym = self
        .libs
        .iter()
        .find_map(|l| l.get(sym_name.to_bytes_with_nul()).ok())
        .ok_or_else(|| {
          IoError::new(
            ErrorKind::Other,
            format!("external function '{}' not found", name),
          )
        })?;
      self.funcs.insert(name.into(), sym);
      Self::call_ext_func(&self.funcs[name], args, ret_ty)
    }
  }

  unsafe fn call_ext_func(
    sym: &Symbol<'lib, *const ()>,
    args: Vec<Val>,
    ret_ty: &Type,
  ) -> IoResult<Val> {
    macro_rules! call_func_ptr {
      ($fp:expr, $args:expr, $($ty:ident)*) => {
        call_func_ptr!(@args
          transmute::<*const (), unsafe extern "C" fn($(call_func_ptr!(@subst $ty)),*) -> usize>($fp),
          $args, 0, () $(,$ty)*
        )
      };
      (@subst $id:ident) => { usize };
      (@args $func:expr, $args:expr, $i:expr, ($($t:tt)*)) => {
        call_func_ptr!(@call $func, $($t)*)
      };
      (@args $func:expr, $args:expr, $i:expr, ($($t:tt)*), $head:ident $(,$tail:ident)*) => {
        call_func_ptr!(@args
          $func, $args, $i + 1, ($($t)* Self::val_to_usize(&$args[$i]),) $(,$tail)*
        )
      };
      (@call $func:expr, $($args:tt)*) => {
        $func($($args)*)
      };
    }
    let func_ptr = *sym.clone();
    let ret = match args.len() {
      0_ => call_func_ptr!(func_ptr, args,),
      1_ => call_func_ptr!(func_ptr, args, A),
      2_ => call_func_ptr!(func_ptr, args, A A),
      3_ => call_func_ptr!(func_ptr, args, A A A),
      4_ => call_func_ptr!(func_ptr, args, A A A A),
      5_ => call_func_ptr!(func_ptr, args, A A A A A),
      6_ => call_func_ptr!(func_ptr, args, A A A A A A),
      7_ => call_func_ptr!(func_ptr, args, A A A A A A A),
      8_ => call_func_ptr!(func_ptr, args, A A A A A A A A),
      9_ => call_func_ptr!(func_ptr, args, A A A A A A A A A),
      10 => call_func_ptr!(func_ptr, args, A A A A A A A A A A),
      11 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A),
      12 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A),
      13 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A),
      14 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A),
      15 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A),
      16 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A),
      17 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A),
      18 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A),
      19 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A A),
      20 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A A A),
      21 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A A A A),
      22 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A A A A A),
      23 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A A A A A A),
      24 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A A A A A A A),
      25 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A A A A A A A A),
      26 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A A A A A A A A A),
      27 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A A A A A A A A A A),
      28 => call_func_ptr!(func_ptr, args, A A A A A A A A A A A A A A A A A A A A A A A A A A A A),
      _ => {
        return Err(IoError::new(
          ErrorKind::Other,
          format!("argument number exceeded in external function call"),
        ))
      }
    };
    Ok(Self::usize_to_val(ret, ret_ty))
  }

  fn val_to_usize(val: &Val) -> usize {
    match val {
      Val::Undef => 0,
      Val::Int(i) => *i as usize,
      Val::Array(a) => a.as_ptr() as usize,
      Val::Pointer { ptr: Some(p), .. } => p.as_ptr() as usize,
      Val::Pointer { ptr: None, .. } => 0,
      Val::UnsafePointer(Some(p)) => p.as_ptr() as usize,
      Val::UnsafePointer(None) => 0,
    }
  }

  fn usize_to_val(u: usize, ty: &Type) -> Val {
    match ty.kind() {
      TypeKind::Int32 => Val::Int(u as i32),
      TypeKind::Unit => Val::Undef,
      TypeKind::Array(..) | TypeKind::Pointer(..) => Val::UnsafePointer(NonNull::new(u as *mut ())),
      _ => panic!("unsupported value type"),
    }
  }
}
