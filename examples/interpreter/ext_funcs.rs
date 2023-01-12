use super::interpreter::{new_error, Val};
use koopa::ir::{FunctionData, Type, TypeKind};
use libloading::{Error, Library, Symbol};
use std::ffi::{CString, OsStr};
use std::io::Result as IoResult;
use std::mem::transmute;
use std::ptr::NonNull;

pub struct ExternFuncs {
  libs: Vec<Library>,
}

impl ExternFuncs {
  pub unsafe fn new<T: AsRef<OsStr>>(lib_files: &[T]) -> Result<Self, Error> {
    Ok(Self {
      libs: lib_files
        .iter()
        .map(|f| Library::new(f))
        .collect::<Result<_, _>>()?,
    })
  }

  pub unsafe fn call(&mut self, func: &FunctionData, args: Vec<Val>) -> IoResult<Val> {
    assert!(
      func.layout().bbs().is_empty(),
      "expected function declaration"
    );
    assert!(!func.name().is_empty(), "invalid function name");
    let name = &func.name()[1..];
    let ret_ty = match func.ty().kind() {
      TypeKind::Function(_, ret) => ret,
      _ => panic!("invalid function"),
    };
    let sym_name = CString::new(name).map_err(|e| new_error(&format!("{}", e)))?;
    let sym = self
      .libs
      .iter()
      .find_map(|l| l.get(sym_name.to_bytes_with_nul()).ok())
      .ok_or_else(|| new_error(&format!("external function '{}' not found", name)))?;
    Self::call_ext_func(sym, args, ret_ty)
  }

  unsafe fn call_ext_func(
    sym: Symbol<'_, *const ()>,
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
          $func, $args, $i + 1, ($($t)* Self::val_to_usize(&$args[$i])?,) $(,$tail)*
        )
      };
      (@call $func:expr, $($args:tt)*) => {
        $func($($args)*)
      };
    }
    let func_ptr = *sym.clone();
    let ret = match args.len() {
      0 => call_func_ptr!(func_ptr, args,),
      1 => call_func_ptr!(func_ptr, args, A),
      2 => call_func_ptr!(func_ptr, args, A A),
      3 => call_func_ptr!(func_ptr, args, A A A),
      4 => call_func_ptr!(func_ptr, args, A A A A),
      5 => call_func_ptr!(func_ptr, args, A A A A A),
      6 => call_func_ptr!(func_ptr, args, A A A A A A),
      7 => call_func_ptr!(func_ptr, args, A A A A A A A),
      8 => call_func_ptr!(func_ptr, args, A A A A A A A A),
      9 => call_func_ptr!(func_ptr, args, A A A A A A A A A),
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
        return Err(new_error(
          "argument number exceeded in external function call",
        ))
      }
    };
    Self::usize_to_val(ret, ret_ty)
  }

  fn val_to_usize(val: &Val) -> IoResult<usize> {
    match val {
      Val::Undef => Ok(0),
      Val::Int(i) => Ok(*i as usize),
      Val::Pointer { ptr: Some(p), .. } => Ok(p.as_ptr() as usize),
      Val::Pointer { ptr: None, .. } => Ok(0),
      Val::UnsafePointer(Some(p)) => Ok(p.as_ptr() as usize),
      Val::UnsafePointer(None) => Ok(0),
      _ => Err(new_error("unsupported value")),
    }
  }

  fn usize_to_val(u: usize, ty: &Type) -> IoResult<Val> {
    match ty.kind() {
      TypeKind::Int32 => Ok(Val::Int(u as i32)),
      TypeKind::Unit => Ok(Val::Undef),
      TypeKind::Pointer(_) => Ok(Val::UnsafePointer(NonNull::new(u as *mut ()))),
      _ => Err(new_error("unsupported value type")),
    }
  }
}
