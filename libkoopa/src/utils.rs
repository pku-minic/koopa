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
  drop(unsafe { Box::from_raw(ptr) });
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
    #[unsafe(no_mangle)]
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
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn $name$(<$($lt)+>)? ($($arg: $ty),*) $(-> $ret)? $body
    $crate::utils::ffi!($($rest)*);
  };
  () => {};
}
pub(crate) use ffi;
