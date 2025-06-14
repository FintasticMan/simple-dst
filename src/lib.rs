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
    fn metadata(&self) -> usize;

    /// Returns the layout of the DST, assuming it has the given length.
    fn layout(metadata: usize) -> Result<Layout, LayoutError>;

    /// Convert the given thin pointer to a fat pointer to the DST, adding the
    /// length to the metadata.
    ///
    /// # Safety
    ///
    /// This function is safe but the returned pointer is not necessarily safe
    /// to dereference.
    fn retype(ptr: *mut u8, metadata: usize) -> *mut Self;
}

unsafe impl<T> Dst for [T] {
    fn metadata(&self) -> usize {
        self.len()
    }

    fn layout(metadata: usize) -> Result<Layout, LayoutError> {
        Layout::array::<T>(metadata)
    }

    fn retype(ptr: *mut u8, metadata: usize) -> *mut Self {
        ptr::slice_from_raw_parts_mut(ptr.cast(), metadata)
    }
}

unsafe impl Dst for str {
    fn metadata(&self) -> usize {
        self.len()
    }

    fn layout(metadata: usize) -> Result<Layout, LayoutError> {
        Layout::array::<u8>(metadata)
    }

    fn retype(ptr: *mut u8, metadata: usize) -> *mut Self {
        // FUTURE: switch to ptr::from_raw_parts_mut() when it has stabilised.
        ptr::slice_from_raw_parts_mut(ptr, metadata) as *mut _
    }
}

/// A generalization of [`Clone`] to [dynamically-sized types][DST] stored in arbitrary containers.
///
/// This trait is implemented for all types implementing [`Clone`], [slices](slice) of all
/// such types, and other dynamically-sized types in the standard library.
/// You may also implement this trait to enable cloning custom DSTs
/// (structures containing dynamically-sized fields), or use it as a supertrait to enable
/// cloning a [trait object].
///
/// This trait is normally used via operations on container types which support DSTs,
/// so you should not typically need to call `.clone_to_uninit()` explicitly except when
/// implementing such a container or otherwise performing explicit management of an allocation,
/// or when implementing `CloneToUninit` itself.
///
/// # Safety
///
/// Implementations must ensure that when `.clone_to_uninit(dest)` returns normally rather than
/// panicking, it always leaves `*dest` initialized as a valid value of type `Self`.
///
/// # Examples
///
/// If you are defining a trait, you can add `CloneToUninit` as a supertrait to enable cloning of
/// `dyn` values of your trait:
///
/// ```ignore
/// #![feature(clone_to_uninit)]
/// use std::rc::Rc;
///
/// trait Foo: std::fmt::Debug + std::clone::CloneToUninit {
///     fn modify(&mut self);
///     fn value(&self) -> i32;
/// }
///
/// impl Foo for i32 {
///     fn modify(&mut self) {
///         *self *= 10;
///     }
///     fn value(&self) -> i32 {
///         *self
///     }
/// }
///
/// let first: Rc<dyn Foo> = Rc::new(1234);
///
/// let mut second = first.clone();
/// Rc::make_mut(&mut second).modify(); // make_mut() will call clone_to_uninit()
///
/// assert_eq!(first.value(), 1234);
/// assert_eq!(second.value(), 12340);
/// ```
///
/// The following is an example of implementing `CloneToUninit` for a custom DST.
/// (It is essentially a limited form of what `derive(CloneToUninit)` would do,
/// if such a derive macro existed.)
///
/// ```ignore
/// #![feature(clone_to_uninit)]
/// use std::clone::CloneToUninit;
/// use std::mem::offset_of;
/// use std::rc::Rc;
///
/// #[derive(PartialEq)]
/// struct MyDst<T: ?Sized> {
///     label: String,
///     contents: T,
/// }
///
/// unsafe impl<T: ?Sized + CloneToUninit> CloneToUninit for MyDst<T> {
///     unsafe fn clone_to_uninit(&self, dest: *mut u8) {
///         // The offset of `self.contents` is dynamic because it depends on the alignment of T
///         // which can be dynamic (if `T = dyn SomeTrait`). Therefore, we have to obtain it
///         // dynamically by examining `self`, rather than using `offset_of!`.
///         //
///         // SAFETY: `self` by definition points somewhere before `&self.contents` in the same
///         // allocation.
///         let offset_of_contents = unsafe {
///             (&raw const self.contents).byte_offset_from_unsigned(self)
///         };
///
///         // Clone the *sized* fields of `self` (just one, in this example).
///         // (By cloning this first and storing it temporarily in a local variable, we avoid
///         // leaking it in case of any panic, using the ordinary automatic cleanup of local
///         // variables. Such a leak would be sound, but undesirable.)
///         let label = self.label.clone();
///
///         // SAFETY: The caller must provide a `dest` such that these field offsets are valid
///         // to write to.
///         unsafe {
///             // Clone the unsized field directly from `self` to `dest`.
///             self.contents.clone_to_uninit(dest.add(offset_of_contents));
///
///             // Now write all the sized fields.
///             //
///             // Note that we only do this once all of the clone() and clone_to_uninit() calls
///             // have completed, and therefore we know that there are no more possible panics;
///             // this ensures no memory leaks in case of panic.
///             dest.add(offset_of!(Self, label)).cast::<String>().write(label);
///         }
///         // All fields of the struct have been initialized; therefore, the struct is initialized,
///         // and we have satisfied our `unsafe impl CloneToUninit` obligations.
///     }
/// }
///
/// fn main() {
///     // Construct MyDst<[u8; 4]>, then coerce to MyDst<[u8]>.
///     let first: Rc<MyDst<[u8]>> = Rc::new(MyDst {
///         label: String::from("hello"),
///         contents: [1, 2, 3, 4],
///     });
///
///     let mut second = first.clone();
///     // make_mut() will call clone_to_uninit().
///     for elem in Rc::make_mut(&mut second).contents.iter_mut() {
///         *elem *= 10;
///     }
///
///     assert_eq!(first.contents, [1, 2, 3, 4]);
///     assert_eq!(second.contents, [10, 20, 30, 40]);
///     assert_eq!(second.label, "hello");
/// }
/// ```
///
/// # See Also
///
/// * [`Clone::clone_from`] is a safe function which may be used instead when [`Self: Sized`](Sized)
///   and the destination is already initialized; it may be able to reuse allocations owned by
///   the destination, whereas `clone_to_uninit` cannot, since its destination is assumed to be
///   uninitialized.
/// * [`ToOwned`], which allocates a new destination container.
///
/// [`ToOwned`]: ../../std/borrow/trait.ToOwned.html
/// [DST]: https://doc.rust-lang.org/reference/dynamically-sized-types.html
/// [trait object]: https://doc.rust-lang.org/reference/types/trait-object.html
// FUTURE: switch to `CloneToUninit` when it is stabilised.
pub unsafe trait CloneToUninit {
    /// Performs copy-assignment from `self` to `dest`.
    ///
    /// This is analogous to `std::ptr::write(dest.cast(), self.clone())`,
    /// except that `Self` may be a dynamically-sized type ([`!Sized`](Sized)).
    ///
    /// Before this function is called, `dest` may point to uninitialized memory.
    /// After this function is called, `dest` will point to initialized memory; it will be
    /// sound to create a `&Self` reference from the pointer with the [pointer metadata]
    /// from `self`.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if any of the following conditions are violated:
    ///
    /// * `dest` must be [valid] for writes for `size_of_val(self)` bytes.
    /// * `dest` must be properly aligned to `align_of_val(self)`.
    ///
    /// [valid]: crate::ptr#safety
    /// [pointer metadata]: crate::ptr::metadata()
    ///
    /// # Panics
    ///
    /// This function may panic. (For example, it might panic if memory allocation for a clone
    /// of a value owned by `self` fails.)
    /// If the call panics, then `*dest` should be treated as uninitialized memory; it must not be
    /// read or dropped, because even if it was previously valid, it may have been partially
    /// overwritten.
    ///
    /// The caller may wish to take care to deallocate the allocation pointed to by `dest`,
    /// if applicable, to avoid a memory leak (but this is not a requirement).
    ///
    /// Implementors should avoid leaking values by, upon unwinding, dropping all component values
    /// that might have already been created. (For example, if a `[Foo]` of length 3 is being
    /// cloned, and the second of the three calls to `Foo::clone()` unwinds, then the first `Foo`
    /// cloned should be dropped.)
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
    /// Allocate the DST with the given metadata, initialize the data with the
    /// given fallible function, and store it in the type.
    ///
    /// # Safety
    ///
    /// The `init` function must correctly initialize the data pointed to, or return an
    /// error.
    unsafe fn try_new_dst<F, E>(metadata: usize, layout: Layout, init: F) -> Result<Self, E>
    where
        F: FnOnce(*mut T) -> Result<(), E>;

    /// Allocate the DST with the given metadata, initialize the data with the
    /// given function, and store it in the type.
    ///
    /// # Safety
    ///
    /// The `init` function must correctly initialize the data pointed to.
    unsafe fn new_dst<F>(metadata: usize, layout: Layout, init: F) -> Self
    where
        F: FnOnce(*mut T),
    {
        unsafe {
            match Self::try_new_dst(metadata, layout, |ptr| {
                init(ptr);
                Ok::<(), Infallible>(())
            }) {
                Ok(a) => a,
                Err(infallible) => match infallible {},
            }
        }
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized + Dst> AllocDst<T> for Box<T> {
    unsafe fn try_new_dst<F, E>(metadata: usize, layout: Layout, init: F) -> Result<Self, E>
    where
        F: FnOnce(*mut T) -> Result<(), E>,
    {
        struct RawBox<T: ?Sized + Dst>(ptr::NonNull<T>, Layout);

        impl<T: ?Sized + Dst> RawBox<T> {
            unsafe fn new(metadata: usize, layout: Layout) -> Self {
                let ptr = unsafe {
                    if layout.size() == 0 {
                        // FUTURE: switch to Layout::dangling() when it has stabilised.
                        ptr::without_provenance_mut(layout.align())
                    } else {
                        alloc(layout)
                    }
                };
                let ptr = ptr::NonNull::new(T::retype(ptr, metadata))
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
            let b = RawBox::new(metadata, layout);
            init(b.0.as_ptr())?;
            Ok(b.finalize())
        }
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized + Dst> AllocDst<T> for Rc<T> {
    unsafe fn try_new_dst<F, E>(metadata: usize, layout: Layout, init: F) -> Result<Self, E>
    where
        F: FnOnce(*mut T) -> Result<(), E>,
    {
        // TODO: this allocates memory twice because Rc needs to store data in front of the data
        // pointer. Find a way to only allocate once.
        Ok(Self::from(unsafe {
            Box::try_new_dst(metadata, layout, init)
        }?))
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized + Dst> AllocDst<T> for Arc<T> {
    unsafe fn try_new_dst<F, E>(metadata: usize, layout: Layout, init: F) -> Result<Self, E>
    where
        F: FnOnce(*mut T) -> Result<(), E>,
    {
        // TODO: this allocates memory twice because Arc needs to store data in front of the data
        // pointer. Find a way to only allocate once.
        Ok(Self::from(unsafe {
            Box::try_new_dst(metadata, layout, init)
        }?))
    }
}
