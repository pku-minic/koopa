/// Creates a new object `t` and returns its pointer.
pub fn new_pointer<T>(t: T) -> *mut T {
  Box::into_raw(Box::new(t))
}

/// Drops the given pointer that created by [`new_pointer`].
pub fn drop_pointer<T>(ptr: *mut T) {
  unsafe { Box::from_raw(ptr) };
}

/// Defines FFI functions.
macro_rules! ffi {
  {
    $($(#[$attr:meta])*
    fn $name:ident($($arg:ident : $ty:ty),* $(,)?) $(-> $ret:ty)? $body:block)*
  } => {
    $($(#[$attr])*
    #[no_mangle]
    pub extern "C" fn $name($($arg: $ty),*) $(-> $ret)? $body)*
  };
}
pub(crate) use ffi;
