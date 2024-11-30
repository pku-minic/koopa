use std::mem::MaybeUninit;

/// Creates a new object `t` and returns its pointer.
pub(crate) fn new_pointer<T>(t: T) -> *mut T {
  Box::into_raw(Box::new(t))
}

/// Drops the given pointer that created by [`new_pointer`].
///
/// # Safety
///
/// Safe if `ptr` is returned by [`new_pointer`].
pub(crate) unsafe fn drop_pointer<T>(ptr: *mut T) {
  drop(Box::from_raw(ptr));
}

/// Returns a new uninitialized box.
///
/// # Safety
///
/// The returned box must be initialized before it can be read.
pub(crate) unsafe fn new_uninit_box<T>() -> Box<T> {
  let b = Box::new(MaybeUninit::<T>::uninit());
  Box::from_raw(Box::into_raw(b) as *mut T)
}

/// Defines FFI functions.
macro_rules! ffi {
  {
    $(#[$attr:meta])*
    fn $name:ident$(<$($lt:lifetime)+>)?
    ($($arg:ident : $ty:ty),* $(,)?) $(-> $ret:ty)? $body:block
    $($rest:tt)*
   } => {
    $(#[$attr])*
    #[no_mangle]
    pub extern "C" fn $name$(<$($lt)+>)? ($($arg: $ty),*) $(-> $ret)? $body
    $crate::utils::ffi!($($rest)*);
  };
  {
    $(#[$attr:meta])*
    unsafe fn $name:ident$(<$($lt:lifetime)+>)?
    ($($arg:ident : $ty:ty),* $(,)?) $(-> $ret:ty)? $body:block
    $($rest:tt)*
   } => {
    $(#[$attr])*
    #[no_mangle]
    pub unsafe extern "C" fn $name$(<$($lt)+>)? ($($arg: $ty),*) $(-> $ret)? $body
    $crate::utils::ffi!($($rest)*);
  };
  () => {};
}
pub(crate) use ffi;
