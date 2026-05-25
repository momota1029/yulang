use std::fmt;

use yulang_typed_ir as typed_ir;

pub type MonomorphizeResult<T> = Result<T, MonomorphizeDiagnostic>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MonomorphizeDiagnostic {
    MissingBinding {
        binding: typed_ir::Path,
    },
    UnsupportedRootShape,
    PrincipalTypeIsNotCallable {
        binding: typed_ir::Path,
        actual: typed_ir::Type,
    },
    IncompleteGraph {
        binding: typed_ir::Path,
    },
    ConflictingBounds {
        var: typed_ir::TypeVar,
        previous: typed_ir::Type,
        next: typed_ir::Type,
    },
}

#[derive(Debug)]
pub enum MonomorphizeError {
    Finalize(MonomorphizeDiagnostic),
    Runtime(yulang_runtime::RuntimeError),
}

impl From<MonomorphizeDiagnostic> for MonomorphizeError {
    fn from(error: MonomorphizeDiagnostic) -> Self {
        Self::Finalize(error)
    }
}

impl From<yulang_runtime::RuntimeError> for MonomorphizeError {
    fn from(error: yulang_runtime::RuntimeError) -> Self {
        Self::Runtime(error)
    }
}

impl fmt::Display for MonomorphizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Finalize(error) => write!(f, "runtime-finalize failed: {error:?}"),
            Self::Runtime(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for MonomorphizeError {}
