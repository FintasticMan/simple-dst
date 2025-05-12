//! Traits for implementing and using DSTs.
//!
//! The design is inspired by the great [slice-dst] crate, but with more of a
//! focus on implementability and use of modern Rust features.
//!
//! [slice-dst]: https://lib.rs/crates/slice-dst

#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

mod errors;
#[cfg(test)]
mod tests;

#[cfg(feature = "alloc")]
use alloc::{
    alloc::{alloc, dealloc, handle_alloc_error},
    boxed::Box,
};
use core::{
    alloc::{Layout, LayoutError},
    borrow::Borrow,
    error::Error,
    ptr,
};

#[cfg(feature = "simple-dst-derive")]
pub use simple_dst_derive::Dst;

pub use errors::*;

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
    /// This is NOT the size of the type, for that you should use [Self::layout].
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

/// A generalization of [`Clone`] to dynamically-sized types stored in arbitrary containers.
// FUTURE: switch to `CloneToUninit` when it is stabilised.
pub unsafe trait CloneToUninitDst {
    unsafe fn clone_to_uninit(&self, dst: *mut u8);
}

unsafe impl<T: Clone> CloneToUninitDst for T {
    #[inline]
    unsafe fn clone_to_uninit(&self, dst: *mut u8) {
        unsafe {
            ptr::write(dst.cast(), self.clone());
        }
    }
}

/// DSTs whose values can be duplicated simply by copying bits.
///
/// This exists because to implement `Copy` you need to implement `Clone` which
/// is impossible for DSTs.
pub trait CopyDst: CloneToUninitDst {}

impl<T: Copy + CloneToUninitDst> CopyDst for T {}

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

unsafe impl<T: CloneToUninitDst> CloneToUninitDst for [T] {
    unsafe fn clone_to_uninit(&self, dst: *mut u8) {
        let dst: *mut T = dst.cast();
        for (i, elem) in self.iter().enumerate() {
            unsafe {
                elem.clone_to_uninit(dst.add(i).cast());
            };
        }
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

unsafe impl CloneToUninitDst for str {
    unsafe fn clone_to_uninit(&self, dst: *mut u8) {
        unsafe {
            ptr::copy_nonoverlapping(self.as_ptr(), dst, self.len());
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
    /// given function, and store it in the type.
    ///
    /// # Safety
    ///
    /// The `init` function may not panic, otherwise there will be a memory leak.
    unsafe fn new_dst<F, E: Error>(len: usize, init: F) -> Result<Self, AllocDstError<E>>
    where
        F: FnOnce(ptr::NonNull<T>) -> Result<(), E>;
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized + Dst> AllocDst<T> for Box<T> {
    unsafe fn new_dst<F, E: Error>(len: usize, init: F) -> Result<Self, AllocDstError<E>>
    where
        F: FnOnce(ptr::NonNull<T>) -> Result<(), E>,
    {
        let layout = T::layout(len)?;

        unsafe {
            // FUTURE: switch to Layout::dangling() when it has stabilised.
            let raw = if layout.size() == 0 {
                ptr::without_provenance_mut(layout.align())
            } else {
                alloc(layout)
            };
            let ptr = ptr::NonNull::new(T::retype(raw, len))
                .unwrap_or_else(|| handle_alloc_error(layout));
            init(ptr).map_err(|e| {
                if layout.size() != 0 {
                    dealloc(raw, layout);
                }
                AllocDstError::Init(e)
            })?;
            Ok(Box::from_raw(ptr.as_ptr()))
        }
    }
}
