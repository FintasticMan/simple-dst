use core::{alloc::LayoutError, error::Error, fmt::Display};

// FUTURE: add Alloc once AllocError has stabilised.
#[derive(Debug, PartialEq, Eq)]
pub enum AllocDstError<E: Error + 'static> {
    Layout(LayoutError),
    Init(E),
}

impl<E: Error + 'static> Display for AllocDstError<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Layout(e) => Display::fmt(e, f),
            Self::Init(e) => Display::fmt(e, f),
        }
    }
}

impl<E: Error + 'static> Error for AllocDstError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Layout(e) => Some(e),
            Self::Init(e) => Some(e),
        }
    }
}

impl<E: Error + 'static> From<LayoutError> for AllocDstError<E> {
    fn from(value: LayoutError) -> Self {
        AllocDstError::Layout(value)
    }
}
