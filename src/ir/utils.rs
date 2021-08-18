use intrusive_collections::PointerOps;
use std::marker::PhantomData;
use std::rc::Weak;

/// `PointerOps` that implements `Weak<T>`.
pub struct WeakPointerOps<T>(PhantomData<T>);

impl<T> WeakPointerOps<T> {
  #[inline]
  pub const fn new() -> Self {
    WeakPointerOps(PhantomData)
  }
}

impl<T> Clone for WeakPointerOps<T> {
  #[inline]
  fn clone(&self) -> Self {
    *self
  }
}

impl<T> Copy for WeakPointerOps<T> {}

impl<T> Default for WeakPointerOps<T> {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

unsafe impl<T: ?Sized> PointerOps for WeakPointerOps<Weak<T>> {
  type Value = T;
  type Pointer = Weak<T>;

  #[inline]
  unsafe fn from_raw(&self, raw: *const T) -> Weak<T> {
    Weak::from_raw(raw)
  }

  #[inline]
  unsafe fn into_raw(&self, ptr: Weak<T>) -> *const T {
    ptr.into_raw()
  }
}

macro_rules! intrusive_adapter {
  (@impl
    $(#[$attr:meta])* $vis:vis $name:ident ($($args:tt),*)
    = $pointer:ty [$ptrops:tt]: $value:path { $field:ident: $link:ty } $($where_:tt)*
  ) => {
    #[allow(explicit_outlives_requirements)]
    $(#[$attr])*
    $vis struct $name<$($args),*> $($where_)* {
      link_ops: <$link as intrusive_collections::DefaultLinkOps>::Ops,
      pointer_ops: $ptrops<$pointer>,
    }
    unsafe impl<$($args),*> Send for $name<$($args),*> $($where_)* {}
    unsafe impl<$($args),*> Sync for $name<$($args),*> $($where_)* {}
    impl<$($args),*> Copy for $name<$($args),*> $($where_)* {}
    impl<$($args),*> Clone for $name<$($args),*> $($where_)* {
      #[inline]
      fn clone(&self) -> Self {
        *self
      }
    }
    impl<$($args),*> Default for $name<$($args),*> $($where_)* {
      #[inline]
      fn default() -> Self {
        Self::NEW
      }
    }
    #[allow(dead_code)]
    impl<$($args),*> $name<$($args),*> $($where_)* {
      pub const NEW: Self = $name {
        link_ops: <$link as intrusive_collections::DefaultLinkOps>::NEW,
        pointer_ops: $ptrops::<$pointer>::new(),
      };
      #[inline]
      pub fn new() -> Self {
        Self::NEW
      }
    }
    #[allow(dead_code, unsafe_code)]
    unsafe impl<$($args),*> intrusive_collections::Adapter for $name<$($args),*> $($where_)* {
      type LinkOps = <$link as intrusive_collections::DefaultLinkOps>::Ops;
      type PointerOps = $ptrops<$pointer>;
      #[inline]
      unsafe fn get_value(&self, link: <Self::LinkOps as intrusive_collections::LinkOps>::LinkPtr) -> *const <Self::PointerOps as intrusive_collections::PointerOps>::Value {
        intrusive_collections::container_of!(link.as_ptr(), $value, $field)
      }
      #[inline]
      unsafe fn get_link(&self, value: *const <Self::PointerOps as intrusive_collections::PointerOps>::Value) -> <Self::LinkOps as intrusive_collections::LinkOps>::LinkPtr {
        let ptr = (value as *const u8).add(intrusive_collections::offset_of!($value, $field));
        core::ptr::NonNull::new_unchecked(ptr as *mut _)
      }
      #[inline]
      fn link_ops(&self) -> &Self::LinkOps {
        &self.link_ops
      }
      #[inline]
      fn link_ops_mut(&mut self) -> &mut Self::LinkOps {
        &mut self.link_ops
      }
      #[inline]
      fn pointer_ops(&self) -> &Self::PointerOps {
        &self.pointer_ops
      }
    }
  };
  ($($t:tt)*) => {
    intrusive_collections::intrusive_adapter!($($t)*);
  };
}

pub(crate) use intrusive_adapter;
