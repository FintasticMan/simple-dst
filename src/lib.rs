//! Traits for allocating and using DSTs.
//!
//! The design is inspired by the great [slice-dst] crate, but with more of a
//! focus on implementability and use of modern Rust features.
//!
//! [slice-dst]: https://lib.rs/crates/slice-dst

#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(test)]
mod tests;

#[cfg(feature = "alloc")]
use alloc::{
    alloc::{alloc, dealloc, handle_alloc_error},
    boxed::Box,
    rc::Rc,
    sync::Arc,
};
use core::{
    alloc::{Layout, LayoutError},
    borrow::Borrow,
    convert::Infallible,
    mem::{self, MaybeUninit},
    ptr,
};

#[cfg(feature = "simple-dst-derive")]
pub use simple_dst_derive::{CloneToUninit, Dst, ToOwned};

/// A dynamically sized type.
///
/// # Safety
///
/// Must be implemented as described.
// FUTURE: switch to metadata rather than length once the `ptr_metadata` feature
// has stabilised.
pub unsafe trait Dst {
    /// The length of the DST.
    ///
    /// This is NOT the size of the type, for that you should use [`Layout::for_value`].
    fn len(&self) -> usize;

    /// Returns the layout of the DST, assuming it has the given length.
    fn layout(len: usize) -> Result<Layout, LayoutError>;

    /// Convert the given thin pointer to a fat pointer to the DST, adding the
    /// length to the metadata.
    ///
    /// # Safety
    ///
    /// This function is safe but the returned pointer is not necessarily safe
    /// to dereference.
    fn retype(ptr: *mut u8, len: usize) -> *mut Self;
}

unsafe impl<T> Dst for [T] {
    fn len(&self) -> usize {
        self.len()
    }

    fn layout(len: usize) -> Result<Layout, LayoutError> {
        Layout::array::<T>(len)
    }

    fn retype(ptr: *mut u8, len: usize) -> *mut Self {
        ptr::slice_from_raw_parts_mut(ptr.cast(), len)
    }
}

unsafe impl Dst for str {
    fn len(&self) -> usize {
        self.len()
    }

    fn layout(len: usize) -> Result<Layout, LayoutError> {
        Layout::array::<u8>(len)
    }

    fn retype(ptr: *mut u8, len: usize) -> *mut Self {
        // FUTURE: switch to ptr::from_raw_parts_mut() when it has stabilised.
        ptr::slice_from_raw_parts_mut(ptr, len) as *mut _
    }
}

/// A generalization of [`Clone`] to dynamically-sized types stored in arbitrary containers.
// FUTURE: switch to `CloneToUninit` when it is stabilised.
pub unsafe trait CloneToUninit {
    unsafe fn clone_to_uninit(&self, dest: *mut u8);
}

unsafe impl<T: Clone> CloneToUninit for T {
    #[inline]
    unsafe fn clone_to_uninit(&self, dest: *mut u8) {
        unsafe {
            dest.cast::<Self>().write(self.clone());
        }
    }
}

unsafe impl<T: Clone> CloneToUninit for [T] {
    // Copied from the standard library's implementation.
    unsafe fn clone_to_uninit(&self, dest: *mut u8) {
        /// Ownership of a collection of values stored in a non-owned `[MaybeUninit<T>]`, some of which
        /// are not yet initialized. This is sort of like a `Vec` that doesn't own its allocation.
        /// Its responsibility is to provide cleanup on unwind by dropping the values that *are*
        /// initialized, unless disarmed by forgetting.
        ///
        /// This is a helper for `impl<T: Clone> CloneToUninit for [T]`.
        struct InitializingSlice<'a, T> {
            data: &'a mut [MaybeUninit<T>],
            /// Number of elements of `*self.data` that are initialized.
            initialized_len: usize,
        }

        impl<'a, T> InitializingSlice<'a, T> {
            #[inline]
            fn from_fully_uninit(data: &'a mut [MaybeUninit<T>]) -> Self {
                Self {
                    data,
                    initialized_len: 0,
                }
            }

            /// Push a value onto the end of the initialized part of the slice.
            ///
            /// # Panics
            ///
            /// Panics if the slice is already fully initialized.
            #[inline]
            fn push(&mut self, value: T) {
                MaybeUninit::write(&mut self.data[self.initialized_len], value);
                self.initialized_len += 1;
            }
        }

        impl<'a, T> Drop for InitializingSlice<'a, T> {
            #[cold] // will only be invoked on unwind
            fn drop(&mut self) {
                let initialized_slice = ptr::slice_from_raw_parts_mut(
                    self.data.as_mut_ptr().cast::<T>(),
                    self.initialized_len,
                );

                // SAFETY:
                // * the pointer is valid because it was made from a mutable reference
                // * `initialized_len` counts the initialized elements as an invariant of this type,
                //   so each of the pointed-to elements is initialized and may be dropped.
                unsafe {
                    ptr::drop_in_place::<[T]>(initialized_slice);
                }
            }
        }

        // SAFETY: The produced `&mut` is valid because:
        // * The caller is obligated to provide a pointer which is valid for writes.
        // * All bytes pointed to are in MaybeUninit, so we don't care about the memory's
        //   initialization status.
        let uninit_ref = unsafe {
            &mut *ptr::slice_from_raw_parts_mut(dest.cast::<MaybeUninit<T>>(), self.len())
        };

        // Copy the elements
        let mut initializing = InitializingSlice::from_fully_uninit(uninit_ref);
        for element_ref in self {
            // If the clone() panics, `initializing` will take care of the cleanup.
            initializing.push(element_ref.clone());
        }

        // If we reach here, then the entire slice is initialized, and we've satisfied our
        // responsibilities to the caller. Disarm the cleanup guard by forgetting it.
        mem::forget(initializing);
    }
}

unsafe impl CloneToUninit for str {
    unsafe fn clone_to_uninit(&self, dest: *mut u8) {
        unsafe {
            ptr::copy_nonoverlapping(self.as_ptr(), dest.cast(), self.len());
        }
    }
}

/// Type that can allocate a DST and store it inside it.
///
/// # Safety
///
/// Must be implemented as described.
// FUTURE: use the Allocator trait once it has stabilised.
pub unsafe trait AllocDst<T: ?Sized + Dst>: Sized + Borrow<T> {
    /// Allocate the DST with the given length, initialize the data with the
    /// given fallible function, and store it in the type.
    ///
    /// # Safety
    ///
    /// The `init` function must correctly initialize the data pointed to, or return an
    /// error.
    unsafe fn try_new_dst<F, E>(len: usize, layout: Layout, init: F) -> Result<Self, E>
    where
        F: FnOnce(*mut T) -> Result<(), E>;

    /// Allocate the DST with the given length, initialize the data with the
    /// given function, and store it in the type.
    ///
    /// # Safety
    ///
    /// The `init` function must correctly initialize the data pointed to.
    unsafe fn new_dst<F>(len: usize, layout: Layout, init: F) -> Self
    where
        F: FnOnce(*mut T),
    {
        unsafe {
            match Self::try_new_dst(len, layout, |ptr| Ok::<(), Infallible>(init(ptr))) {
                Ok(a) => a,
                Err(infallible) => match infallible {},
            }
        }
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized + Dst> AllocDst<T> for Box<T> {
    unsafe fn try_new_dst<F, E>(len: usize, layout: Layout, init: F) -> Result<Self, E>
    where
        F: FnOnce(*mut T) -> Result<(), E>,
    {
        struct RawBox<T: ?Sized + Dst>(ptr::NonNull<T>, Layout);

        impl<T: ?Sized + Dst> RawBox<T> {
            unsafe fn new(len: usize, layout: Layout) -> Self {
                let ptr = unsafe {
                    if layout.size() == 0 {
                        // FUTURE: switch to Layout::dangling() when it has stabilised.
                        ptr::without_provenance_mut(layout.align())
                    } else {
                        alloc(layout)
                    }
                };
                let ptr = ptr::NonNull::new(T::retype(ptr, len))
                    .unwrap_or_else(|| handle_alloc_error(layout));

                Self(ptr, layout)
            }

            unsafe fn finalize(self) -> Box<T> {
                let b = unsafe { Box::from_raw(self.0.as_ptr()) };
                mem::forget(self);
                b
            }
        }

        impl<T: ?Sized + Dst> Drop for RawBox<T> {
            fn drop(&mut self) {
                if self.1.size() != 0 {
                    unsafe {
                        dealloc(self.0.cast().as_ptr(), self.1);
                    };
                }
            }
        }

        unsafe {
            let b = RawBox::new(len, layout);
            init(b.0.as_ptr())?;
            Ok(b.finalize())
        }
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized + Dst> AllocDst<T> for Rc<T> {
    unsafe fn try_new_dst<F, E>(len: usize, layout: Layout, init: F) -> Result<Self, E>
    where
        F: FnOnce(*mut T) -> Result<(), E>,
    {
        Ok(Self::from(unsafe { Box::try_new_dst(len, layout, init) }?))
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized + Dst> AllocDst<T> for Arc<T> {
    unsafe fn try_new_dst<F, E>(len: usize, layout: Layout, init: F) -> Result<Self, E>
    where
        F: FnOnce(*mut T) -> Result<(), E>,
    {
        Ok(Self::from(unsafe { Box::try_new_dst(len, layout, init) }?))
    }
}
