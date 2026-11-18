use super::interpreter::{Val, new_error};
use koopa::ir::{FunctionData, Type, TypeKind};
use libffi::middle::{Arg, Cif, CodePtr, Type as FfiType};
use libloading::{Error, Library};
use std::ffi::CString;
use std::io::Result as IoResult;
use std::ptr::NonNull;

pub struct ExternFuncs {
  libs: Vec<Library>,
  #[cfg(all(test, not(miri)))]
  test_symbols: Vec<(&'static str, *const ())>,
}

impl ExternFuncs {
  pub unsafe fn new(lib_files: &[String]) -> Result<Self, Error> {
    Ok(Self {
      libs: lib_files
        .iter()
        .map(|f| unsafe { Library::new(f) })
        .collect::<Result<_, _>>()?,
      #[cfg(all(test, not(miri)))]
      test_symbols: Vec::new(),
    })
  }

  pub unsafe fn call(&mut self, func: &FunctionData, args: Vec<Val>) -> IoResult<Val> {
    assert!(
      func.layout().bbs().is_empty(),
      "expected function declaration"
    );
    assert!(!func.name().is_empty(), "invalid function name");
    let name = &func.name()[1..];
    let TypeKind::Function(params_ty, ret_ty) = func.ty().kind() else {
      panic!("invalid function");
    };
    #[cfg(all(test, not(miri)))]
    if let Some((_, symbol)) = self.test_symbols.iter().find(|(n, _)| *n == name) {
      return unsafe { Self::call_ext_func(*symbol, args, params_ty, ret_ty) };
    }
    let sym_name = CString::new(name).map_err(|e| new_error(&format!("{}", e)))?;
    let sym = self
      .libs
      .iter()
      .find_map(|l| unsafe { l.get::<*const ()>(sym_name.to_bytes_with_nul()) }.ok())
      .ok_or_else(|| new_error(&format!("external function '{}' not found", name)))?;
    unsafe { Self::call_ext_func(*sym, args, params_ty, ret_ty) }
  }

  #[cfg(all(test, not(miri)))]
  pub fn with_test_symbols(symbols: Vec<(&'static str, *const ())>) -> Self {
    Self {
      libs: Vec::new(),
      test_symbols: symbols,
    }
  }

  unsafe fn call_ext_func(
    func_ptr: *const (),
    args: Vec<Val>,
    params_ty: &[Type],
    ret_ty: &Type,
  ) -> IoResult<Val> {
    if args.len() != params_ty.len() {
      return Err(new_error("external function argument count mismatch"));
    }
    let arg_types = params_ty
      .iter()
      .map(ffi_type)
      .collect::<IoResult<Vec<_>>>()?;
    if params_ty.iter().any(Type::is_unit) {
      return Err(new_error("unsupported external argument type"));
    }
    let cif = Cif::try_new(arg_types, ffi_type(ret_ty)?)
      .map_err(|e| new_error(&format!("invalid external function signature: {e:?}")))?;
    let values = args
      .iter()
      .zip(params_ty)
      .map(|(value, ty)| FfiValue::new(value, ty))
      .collect::<IoResult<Vec<_>>>()?;
    let args: Vec<_> = values.iter().map(FfiValue::arg).collect();
    let code = CodePtr(func_ptr.cast_mut().cast());
    // Each libffi signature and backing argument has the exact C type from
    // the IR declaration. In particular, i32 stack arguments are not usize.
    Ok(match ret_ty.kind() {
      TypeKind::Int32 => Val::Int(unsafe { cif.call::<i32>(code, &args) }),
      TypeKind::Unit => {
        unsafe { cif.call::<()>(code, &args) };
        Val::Undef
      }
      TypeKind::Pointer(_) => {
        Val::UnsafePointer(NonNull::new(unsafe { cif.call::<*mut ()>(code, &args) }))
      }
      _ => return Err(new_error("unsupported external return type")),
    })
  }
}

fn ffi_type(ty: &Type) -> IoResult<FfiType> {
  match ty.kind() {
    TypeKind::Int32 => Ok(FfiType::i32()),
    TypeKind::Pointer(_) => Ok(FfiType::pointer()),
    TypeKind::Unit => Ok(FfiType::void()),
    _ => Err(new_error("unsupported external value type")),
  }
}

enum FfiValue {
  Int(i32),
  Pointer(*mut ()),
}

impl FfiValue {
  fn new(value: &Val, ty: &Type) -> IoResult<Self> {
    match (value, ty.kind()) {
      (Val::Int(value), TypeKind::Int32) => Ok(Self::Int(*value)),
      (Val::Undef, TypeKind::Int32) => Ok(Self::Int(0)),
      (Val::Pointer { ptr, .. }, TypeKind::Pointer(_)) => Ok(Self::Pointer(
        ptr.map_or(std::ptr::null_mut(), |p| p.as_ptr().cast()),
      )),
      (Val::UnsafePointer(ptr), TypeKind::Pointer(_)) => Ok(Self::Pointer(
        ptr.map_or(std::ptr::null_mut(), |p| p.as_ptr()),
      )),
      (Val::Undef, TypeKind::Pointer(_)) => Ok(Self::Pointer(std::ptr::null_mut())),
      _ => Err(new_error("unsupported external argument value")),
    }
  }

  fn arg(&self) -> Arg<'_> {
    match self {
      Self::Int(value) => Arg::new(value),
      Self::Pointer(value) => Arg::new(value),
    }
  }
}

#[cfg(all(test, not(miri)))]
mod tests {
  use super::*;

  extern "C" fn sum_ten(
    a: i32,
    b: i32,
    c: i32,
    d: i32,
    e: i32,
    f: i32,
    g: i32,
    h: i32,
    i: i32,
    j: i32,
  ) -> i32 {
    a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i + 10 * j
  }

  unsafe extern "C" fn write_int(dest: *mut i32, value: i32) {
    unsafe { *dest = value };
  }

  extern "C" fn identity_pointer(value: *mut i32) -> *mut i32 {
    value
  }

  #[test]
  fn external_calls_use_i32_register_and_stack_arguments() {
    let values = [1, -2, 3, -4, 5, -6, 7, -8, 9, -10];
    let expected = sum_ten(1, -2, 3, -4, 5, -6, 7, -8, 9, -10);
    let result = unsafe {
      ExternFuncs::call_ext_func(
        sum_ten as *const (),
        values.into_iter().map(Val::Int).collect(),
        &vec![Type::get_i32(); 10],
        &Type::get_i32(),
      )
    }
    .unwrap();
    assert!(matches!(result, Val::Int(value) if value == expected));
  }

  #[test]
  fn external_calls_preserve_void_and_pointer_types() {
    let mut value = 0i32;
    let pointer = Val::UnsafePointer(NonNull::new((&mut value as *mut i32).cast()));
    let ptr_ty = Type::get_pointer(Type::get_i32());
    let result = unsafe {
      ExternFuncs::call_ext_func(
        write_int as *const (),
        vec![pointer.clone(), Val::Int(-42)],
        &[ptr_ty.clone(), Type::get_i32()],
        &Type::get_unit(),
      )
    }
    .unwrap();
    assert!(matches!(result, Val::Undef));
    assert_eq!(value, -42);
    let result = unsafe {
      ExternFuncs::call_ext_func(
        identity_pointer as *const (),
        vec![pointer],
        &[ptr_ty.clone()],
        &ptr_ty,
      )
    }
    .unwrap();
    assert!(
      matches!(result, Val::UnsafePointer(Some(ptr)) if ptr.as_ptr() == (&mut value as *mut i32).cast())
    );
  }
}
