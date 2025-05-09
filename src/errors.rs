use core::{alloc::LayoutError, error::Error, fmt::Display};

// FUTURE: add Alloc once AllocError has stabilised.
#[derive(Debug)]
pub enum AllocDstError {
    Layout(LayoutError),
}

impl Display for AllocDstError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let AllocDstError::Layout(e) = self;
        Display::fmt(e, f)
    }
}

impl Error for AllocDstError {}

impl From<LayoutError> for AllocDstError {
    fn from(value: LayoutError) -> Self {
        AllocDstError::Layout(value)
    }
}

// FUTURE: add Alloc once AllocError has stabilised.
#[derive(Debug)]
pub enum TryAllocDstError<E: Error> {
    Layout(LayoutError),
    Init(E),
}

impl<E: Error> Display for TryAllocDstError<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Layout(e) => Display::fmt(e, f),
            Self::Init(e) => Display::fmt(e, f),
        }
    }
}

impl<E: Error> Error for TryAllocDstError<E> {}

impl<E: Error> From<LayoutError> for TryAllocDstError<E> {
    fn from(value: LayoutError) -> Self {
        Self::Layout(value)
    }
}
