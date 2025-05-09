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
    convert::Infallible,
    error::Error,
    ptr,
};

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
    fn retype(ptr: ptr::NonNull<u8>, len: usize) -> ptr::NonNull<Self>;

    /// Writes the data contained in this DST to the pointer given.
    ///
    /// # Safety
    ///
    /// The given pointer must be valid for the DST and have the same length as
    /// `self`.
    unsafe fn clone_to_raw(&self, ptr: ptr::NonNull<Self>);
}

unsafe impl<T> Dst for [T] {
    fn len(&self) -> usize {
        self.len()
    }

    fn layout(len: usize) -> Result<Layout, LayoutError> {
        Layout::array::<T>(len)
    }

    fn retype(ptr: ptr::NonNull<u8>, len: usize) -> ptr::NonNull<Self> {
        // FUTURE: switch to ptr::NonNull:from_raw_parts() when it has stabilised.
        let ptr = ptr::NonNull::slice_from_raw_parts(ptr.cast::<()>(), len);
        unsafe { ptr::NonNull::new_unchecked(ptr.as_ptr() as *mut _) }
    }

    unsafe fn clone_to_raw(&self, ptr: ptr::NonNull<Self>) {
        unsafe { ptr::copy_nonoverlapping(self.as_ptr(), ptr.as_ptr().cast(), self.len()) };
    }
}

unsafe impl Dst for str {
    fn len(&self) -> usize {
        self.len()
    }

    fn layout(len: usize) -> Result<Layout, LayoutError> {
        Layout::array::<u8>(len)
    }

    fn retype(ptr: ptr::NonNull<u8>, len: usize) -> ptr::NonNull<Self> {
        // FUTURE: switch to ptr::NonNull:from_raw_parts() when it has stabilised.
        let ptr = ptr::NonNull::slice_from_raw_parts(ptr.cast::<()>(), len);
        unsafe { ptr::NonNull::new_unchecked(ptr.as_ptr() as *mut _) }
    }

    unsafe fn clone_to_raw(&self, ptr: ptr::NonNull<Self>) {
        unsafe { ptr::copy_nonoverlapping(self.as_ptr(), ptr.as_ptr().cast(), self.len()) };
    }
}

/// Type that can allocate a DST and store it inside it.
///
/// # Safety
///
/// Must be implemented as described.
// FUTURE: use the Allocator trait once it has stabilised.
pub unsafe trait AllocDst<T: ?Sized + Dst>: Sized {
    /// Allocate the DST with the given length, initialize the data with the
    /// given function, and store it in the type.
    ///
    /// # Safety
    ///
    /// The `init` function may not panic, otherwise there will be a memory leak.
    unsafe fn new_dst<F>(len: usize, init: F) -> Result<Self, AllocDstError>
    where
        F: FnOnce(ptr::NonNull<T>) -> ();
}

/// Blanket implementation for all types that implement [TryAllocDst].
unsafe impl<A, T: ?Sized + Dst> AllocDst<T> for A
where
    A: TryAllocDst<T>,
{
    unsafe fn new_dst<F>(len: usize, init: F) -> Result<Self, AllocDstError>
    where
        F: FnOnce(ptr::NonNull<T>) -> (),
    {
        match unsafe { Self::try_new_dst(len, |ptr| Ok::<(), Infallible>(init(ptr))) } {
            Ok(value) => Ok(value),
            Err(TryAllocDstError::Layout(e)) => Err(AllocDstError::Layout(e)),
            Err(TryAllocDstError::Init(infallible)) => match infallible {},
        }
    }
}

/// Type that can allocate a DST and store it inside it.
///
/// # Safety
///
/// Must be implemented as described. The `try_new_dst` function must not leak
/// memory in the case of `init` returning an error.
pub unsafe trait TryAllocDst<T: ?Sized + Dst>: Sized + AllocDst<T> {
    /// Allocate the DST with the given length, initialize the data with the
    /// given function, and store it in the type.
    ///
    /// # Safety
    ///
    /// The `init` function may not panic, otherwise there will be a memory leak.
    unsafe fn try_new_dst<F, E: Error>(len: usize, init: F) -> Result<Self, TryAllocDstError<E>>
    where
        F: FnOnce(ptr::NonNull<T>) -> Result<(), E>;
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized + Dst> TryAllocDst<T> for Box<T> {
    unsafe fn try_new_dst<F, E: Error>(len: usize, init: F) -> Result<Self, TryAllocDstError<E>>
    where
        F: FnOnce(ptr::NonNull<T>) -> Result<(), E>,
    {
        let layout = T::layout(len)?;

        unsafe {
            let raw = if layout.size() == 0 {
                // FUTURE: switch to Layout::dangling() when it has stabilised.
                ptr::NonNull::new(ptr::without_provenance_mut(layout.align()))
            } else {
                ptr::NonNull::new(alloc(layout))
            }
            .unwrap_or_else(|| handle_alloc_error(layout));
            let ptr = T::retype(raw, len);
            init(ptr).map_err(|e| {
                if layout.size() != 0 {
                    dealloc(raw.as_ptr(), layout);
                }
                TryAllocDstError::Init(e)
            })?;
            Ok(Box::from_raw(ptr.as_ptr()))
        }
    }
}
