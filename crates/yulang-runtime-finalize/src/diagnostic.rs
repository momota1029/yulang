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
