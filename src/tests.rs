use core::{convert::Infallible, mem::offset_of};

use crate::*;

#[cfg(feature = "alloc")]
#[test]
fn str_test() {
    let str = "thisisatest";
    let boxed: Box<str> = unsafe {
        Box::new_dst(str.len(), |ptr| {
            str.clone_to_uninit(ptr.cast().as_ptr());
            Ok::<(), Infallible>(())
        })
    }
    .unwrap();

    assert_eq!(boxed.len(), str.len());
    assert_eq!(boxed.as_ref(), str);
}

#[cfg(feature = "alloc")]
#[test]
fn zst_test() {
    let arr: [(); 0] = [];
    let boxed: Box<[()]> = unsafe {
        Box::new_dst(arr.len(), |ptr| {
            arr.clone_to_uninit(ptr.cast().as_ptr());
            Ok::<(), Infallible>(())
        })
    }
    .unwrap();

    assert_eq!(boxed.len(), arr.len());
    assert_eq!(boxed.as_ref(), arr);
}

#[repr(C)]
struct Type {
    data1: i16,
    data2: usize,
    data3: u32,
    slice: [i128],
}

unsafe impl Dst for Type {
    fn len(&self) -> usize {
        self.slice.len()
    }

    fn layout(len: usize) -> Result<Layout, LayoutError> {
        let (layout, _) = Self::__dst_impl_layout_offsets(len)?;
        Ok(layout)
    }

    fn retype(ptr: *mut u8, len: usize) -> *mut Self {
        // FUTURE: switch to ptr::from_raw_parts_mut() when it has stabilised.
        ptr::slice_from_raw_parts_mut(ptr, len) as *mut _
    }
}

unsafe impl CloneToUninitDst for Type {
    unsafe fn clone_to_uninit(&self, dst: *mut u8) {
        // FUTURE: switch to byte_offset_from_unsigned when it has stabilised.
        let slice_offset = unsafe {
            usize::try_from((&raw const self.slice).byte_offset_from(self)).unwrap_unchecked()
        };

        unsafe {
            Self::__dst_impl_write_to_uninit(
                dst,
                slice_offset,
                self.data1.clone(),
                self.data2.clone(),
                self.data3.clone(),
                &self.slice,
            )
        }
    }
}

impl Type {
    fn __dst_impl_layout_offsets(len: usize) -> Result<(Layout, [usize; 4]), LayoutError> {
        let data1_layout = Layout::new::<i16>();
        let data2_layout = Layout::new::<usize>();
        let data3_layout = Layout::new::<u32>();
        let slice_layout = Layout::array::<i128>(len)?;
        let layouts = [data1_layout, data2_layout, data3_layout, slice_layout];
        let mut layout = layouts[0];
        let mut offsets = [0; 4];
        for i in 1..4 {
            let (new_layout, offset) = layout.extend(layouts[i])?;
            layout = new_layout;
            offsets[i] = offset;
        }
        Ok((layout.pad_to_align(), offsets))
    }

    unsafe fn __dst_impl_write_to_uninit(
        dst: *mut u8,
        slice_offset: usize,
        data1: i16,
        data2: usize,
        data3: u32,
        slice: &[i128],
    ) {
        unsafe {
            slice.clone_to_uninit(dst.add(slice_offset));

            dst.add(offset_of!(Self, data1)).cast::<i16>().write(data1);
            dst.add(offset_of!(Self, data2))
                .cast::<usize>()
                .write(data2);
            dst.add(offset_of!(Self, data3)).cast::<u32>().write(data3);
        }
    }

    fn new_internal(data1: i16, data2: usize, data3: u32, slice: &[i128]) -> Box<Self> {
        unsafe {
            Box::new_dst(slice.len(), |ptr| {
                let (_, offsets) = Self::__dst_impl_layout_offsets(slice.len())?;
                Self::__dst_impl_write_to_uninit(
                    ptr.cast().as_ptr(),
                    offsets[3],
                    data1,
                    data2,
                    data3,
                    slice,
                );
                Ok::<(), LayoutError>(())
            })
            .unwrap()
        }
    }
}

#[cfg(feature = "alloc")]
#[test]
fn complex_test() {
    let v = Type::new_internal(-12, 65537, 50, &[-2, 5, 20]);
    assert_eq!(v.data1, -12);
    assert_eq!(v.data2, 65537);
    assert_eq!(v.data3, 50);
    assert_eq!(v.slice[0], -2);
    assert_eq!(v.slice[1], 5);
    assert_eq!(v.slice[2], 20);
    assert_eq!(v.len(), 3);
    assert_eq!(v.len(), v.slice.len());
}

#[cfg(feature = "alloc")]
#[test]
fn clone_test() {
    let v1 = Type::new_internal(-12, 65537, 50, &[-2, 5, 20]);

    let v2 = unsafe {
        Box::new_dst(v1.len(), |ptr: ptr::NonNull<Type>| {
            v1.as_ref().clone_to_uninit(ptr.as_ptr().cast());
            Ok::<(), Infallible>(())
        })
        .unwrap()
    };
    assert_eq!(v2.data1, v1.data1);
    assert_eq!(v2.data2, v1.data2);
    assert_eq!(v2.data3, v1.data3);
    assert_eq!(v2.slice[0], v1.slice[0]);
    assert_eq!(v2.slice[1], v1.slice[1]);
    assert_eq!(v2.slice[2], v1.slice[2]);
    assert_eq!(v2.len(), v1.len());
}
