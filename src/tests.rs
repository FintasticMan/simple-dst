use crate::*;

#[cfg(feature = "alloc")]
#[test]
fn str_test() {
    let str = "thisisatest";
    let boxed: Box<str> = unsafe {
        Box::new_dst(str.len(), |ptr| {
            str.clone_to_raw(ptr);
        })
        .unwrap()
    };

    assert_eq!(boxed.len(), str.len());
    assert_eq!(boxed.as_ref(), str);
}

#[cfg(feature = "alloc")]
#[test]
fn zst_test() {
    let arr: [(); 0] = [];
    let boxed: Box<[()]> = unsafe {
        Box::new_dst(arr.len(), |ptr| {
            arr.clone_to_raw(ptr);
        })
        .unwrap()
    };

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
        let (layout, _) = Self::layout_offsets(len)?;
        Ok(layout)
    }

    fn retype(ptr: ptr::NonNull<u8>, len: usize) -> ptr::NonNull<Self> {
        // FUTURE: switch to ptr::NonNull:from_raw_parts() when it has stabilised.
        let ptr = ptr::NonNull::slice_from_raw_parts(ptr.cast::<()>(), len);
        unsafe { ptr::NonNull::new_unchecked(ptr.as_ptr() as *mut _) }
    }

    unsafe fn clone_to_raw(&self, ptr: ptr::NonNull<Self>) {
        unsafe {
            Self::write_to_raw(ptr, self.data1, self.data2, self.data3, &self.slice);
        }
    }
}

impl Type {
    fn layout_offsets(len: usize) -> Result<(Layout, [usize; 4]), LayoutError> {
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

    unsafe fn write_to_raw(
        ptr: ptr::NonNull<Self>,
        data1: i16,
        data2: usize,
        data3: u32,
        slice: &[i128],
    ) {
        let (layout, offsets) = Self::layout_offsets(slice.len()).unwrap();
        let (data1_offset, data2_offset, data3_offset, slice_offset) =
            (offsets[0], offsets[1], offsets[2], offsets[3]);
        unsafe {
            let raw = ptr.cast::<u8>();
            ptr::write(raw.add(data1_offset).cast().as_ptr(), data1);
            ptr::write(raw.add(data2_offset).cast().as_ptr(), data2);
            ptr::write(raw.add(data3_offset).cast().as_ptr(), data3);
            slice.clone_to_raw(<[i128]>::retype(raw.add(slice_offset), slice.len()));
            assert_eq!(Layout::for_value(ptr.as_ref()), layout);
        }
    }

    fn new(data1: i16, data2: usize, data3: u32, slice: &[i128]) -> Box<Self> {
        unsafe {
            Box::new_dst(slice.len(), |ptr| {
                Self::write_to_raw(ptr, data1, data2, data3, slice)
            })
            .unwrap()
        }
    }
}

#[cfg(feature = "alloc")]
#[test]
fn complex_test() {
    let v = Type::new(-12, 65537, 50, &[-2, 5, 20]);
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
    let v1 = Type::new(-12, 65537, 50, &[-2, 5, 20]);

    let v2 = unsafe { Box::new_dst(v1.len(), |ptr| v1.clone_to_raw(ptr)).unwrap() };
    assert_eq!(v2.data1, v1.data1);
    assert_eq!(v2.data2, v1.data2);
    assert_eq!(v2.data3, v1.data3);
    assert_eq!(v2.slice[0], v1.slice[0]);
    assert_eq!(v2.slice[1], v1.slice[1]);
    assert_eq!(v2.slice[2], v1.slice[2]);
    assert_eq!(v2.len(), v1.len());
}
