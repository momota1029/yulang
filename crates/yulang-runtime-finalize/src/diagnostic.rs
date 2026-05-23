use yulang_runtime_ir::Type as RuntimeType;
use yulang_typed_ir as typed_ir;

pub type FinalizeResult<T> = Result<T, FinalizeError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FinalizeError {
    Diagnostic(FinalizeDiagnostic),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FinalizeDiagnostic {
    PrincipalTypeIsNotCallable {
        binding: typed_ir::Path,
        actual: typed_ir::Type,
    },
    IncompletePrincipalInstance {
        binding: typed_ir::Path,
        reason: PrincipalIncompleteReason,
    },
    UnsupportedBodyShape {
        binding: typed_ir::Path,
        reason: BodyIncompleteReason,
    },
    MissingBinding {
        binding: typed_ir::Path,
    },
    MissingRootExpr {
        index: usize,
    },
    BodyResultMismatch {
        binding: typed_ir::Path,
        expected: RuntimeType,
        actual: RuntimeType,
    },
    UnboundLocal {
        name: typed_ir::Path,
    },
    ConflictingLower {
        var: typed_ir::TypeVar,
        previous: typed_ir::Type,
        next: typed_ir::Type,
    },
    ShapeMismatch {
        expected: typed_ir::Type,
        actual: RuntimeType,
    },
    Validation {
        reason: ValidationReason,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrincipalIncompleteReason {
    OpenParameter,
    OpenResult,
    OpenEffect,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BodyIncompleteReason {
    NonLambdaBinding,
    MissingInstanceParameter,
    UnsupportedExpression,
    OpenExpressionType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationReason {
    MissingBinding {
        binding: typed_ir::Path,
    },
    OpenRuntimeType {
        ty: RuntimeType,
    },
    OpenCoreType {
        ty: typed_ir::Type,
    },
    UnboundVariable {
        path: typed_ir::Path,
    },
    TypeMismatch {
        expected: RuntimeType,
        actual: RuntimeType,
    },
    NonFunctionCallee {
        ty: RuntimeType,
    },
    ExpectedThunk {
        ty: RuntimeType,
    },
    InvalidRootExpr {
        index: usize,
    },
}
