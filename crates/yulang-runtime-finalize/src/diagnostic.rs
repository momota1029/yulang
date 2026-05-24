use std::fmt;

use yulang_typed_ir as typed_ir;

pub type FinalizeResult<T> = Result<T, FinalizeDiagnostic>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FinalizeDiagnostic {
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
pub enum FinalizeMonomorphizeError {
    Finalize(FinalizeDiagnostic),
    Runtime(yulang_runtime::RuntimeError),
}

impl From<FinalizeDiagnostic> for FinalizeMonomorphizeError {
    fn from(error: FinalizeDiagnostic) -> Self {
        Self::Finalize(error)
    }
}

impl From<yulang_runtime::RuntimeError> for FinalizeMonomorphizeError {
    fn from(error: yulang_runtime::RuntimeError) -> Self {
        Self::Runtime(error)
    }
}

impl fmt::Display for FinalizeMonomorphizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Finalize(error) => write!(f, "runtime-finalize failed: {error:?}"),
            Self::Runtime(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for FinalizeMonomorphizeError {}
