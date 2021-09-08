use std::mem::MaybeUninit;
use std::ptr;
use std::rc::{Rc, Weak};

/// Helper trait for creating an `Rc` with its own weak reference.
pub trait NewWithRef<T> {
  /// Creates an `Rc` with its own weak reference.
  fn new_with_ref<F>(init: F) -> Self
  where
    F: FnOnce(Weak<T>) -> T;
}

impl<T> NewWithRef<T> for Rc<T> {
  fn new_with_ref<F>(init: F) -> Self
  where
    F: FnOnce(Weak<T>) -> T,
  {
    // create an uninitialized `Rc`
    let rc = unsafe { Rc::from_raw(Rc::into_raw(Rc::new(MaybeUninit::<T>::uninit())) as *const T) };
    // get data by calling function `init`
    let weak = Rc::downgrade(&rc);
    let data = init(weak);
    // initialize the created `Rc`
    let ptr = Rc::into_raw(rc);
    unsafe {
      ptr::write(ptr as *mut T, data);
      Rc::from_raw(ptr)
    }
  }
}
