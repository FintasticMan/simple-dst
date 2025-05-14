use core::{alloc::LayoutError, error::Error, fmt::Display};

// FUTURE: add Alloc once AllocError has stabilised.
#[derive(Debug, PartialEq, Eq)]
pub enum AllocDstError {
    Layout(LayoutError),
}

impl Display for AllocDstError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Layout(e) => Display::fmt(e, f),
        }
    }
}

impl Error for AllocDstError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Layout(e) => Some(e),
        }
    }
}

impl From<LayoutError> for AllocDstError {
    fn from(value: LayoutError) -> Self {
        AllocDstError::Layout(value)
    }
}
