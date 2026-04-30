use std::fmt;

use yulang_core_ir as core_ir;

pub type RuntimeResult<T> = Result<T, RuntimeError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeError {
    MissingBindingType {
        path: core_ir::Path,
    },
    MissingRootType {
        index: usize,
    },
    MissingLocalType {
        path: core_ir::Path,
    },
    MissingExpectedType {
        node: &'static str,
    },
    MissingApplyEvidence,
    MissingJoinEvidence {
        node: &'static str,
    },
    NonFunctionCallee {
        ty: core_ir::Type,
    },
    ExpectedThunk {
        ty: core_ir::Type,
    },
    TypeMismatch {
        expected: core_ir::Type,
        actual: core_ir::Type,
        source: TypeSource,
    },
    UnsupportedPatternShape {
        pattern: &'static str,
        ty: core_ir::Type,
    },
    UnsupportedSelectBase {
        field: core_ir::Name,
        ty: core_ir::Type,
    },
    UnboundVariable {
        path: core_ir::Path,
    },
    ResidualAny {
        ty: core_ir::Type,
        source: TypeSource,
    },
    NonRuntimeType {
        ty: core_ir::Type,
        source: TypeSource,
    },
    ResidualPolymorphicBinding {
        path: core_ir::Path,
        vars: Vec<core_ir::TypeVar>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeSource {
    BindingScheme,
    BindingGraph,
    RootGraph,
    ApplyEvidence,
    JoinEvidence,
    Expected,
    Local,
    Literal,
    Structural,
    Validation,
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::MissingBindingType { path } => {
                write!(f, "missing binding type for {}", display_path(path))
            }
            RuntimeError::MissingRootType { index } => {
                write!(f, "missing root type for root #{index}")
            }
            RuntimeError::MissingLocalType { path } => {
                write!(f, "missing local type for {}", display_path(path))
            }
            RuntimeError::MissingExpectedType { node } => {
                write!(f, "missing expected type for {node}")
            }
            RuntimeError::MissingApplyEvidence => write!(f, "missing apply evidence"),
            RuntimeError::MissingJoinEvidence { node } => {
                write!(f, "missing join evidence for {node}")
            }
            RuntimeError::NonFunctionCallee { ty } => {
                write!(f, "callee is not a function: {ty:?}")
            }
            RuntimeError::ExpectedThunk { ty } => {
                write!(f, "expected thunk, actual {ty:?}")
            }
            RuntimeError::TypeMismatch {
                expected,
                actual,
                source,
            } => write!(
                f,
                "type mismatch from {source:?}: expected {expected:?}, actual {actual:?}"
            ),
            RuntimeError::UnsupportedPatternShape { pattern, ty } => {
                write!(f, "unsupported {pattern} pattern against type {ty:?}")
            }
            RuntimeError::UnsupportedSelectBase { field, ty } => {
                write!(f, "cannot select {} from {ty:?}", field.0)
            }
            RuntimeError::UnboundVariable { path } => {
                write!(f, "unbound variable {}", display_path(path))
            }
            RuntimeError::ResidualAny { ty, source } => {
                write!(f, "residual Any from {source:?}: {ty:?}")
            }
            RuntimeError::NonRuntimeType { ty, source } => {
                write!(f, "non-runtime type from {source:?}: {ty:?}")
            }
            RuntimeError::ResidualPolymorphicBinding { path, vars } => write!(
                f,
                "residual polymorphic runtime IR binding {} with vars {:?}",
                display_path(path),
                vars
            ),
        }
    }
}

impl std::error::Error for RuntimeError {}

fn display_path(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
