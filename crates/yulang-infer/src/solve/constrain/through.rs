use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};

impl Infer {
    pub(super) fn propagate_through(
        &self,
        _from: TypeVar,
        _to: TypeVar,
        _cause: &ConstraintCause,
        _cache: &mut StepCache,
    ) {
        // Through is attached to freshly introduced effect variables. Propagating it
        // through ordinary var-to-var constraints makes handler scrutinees transparent
        // after co-occurrence, which erases the guarded rows that shallow handlers need.
    }

    pub(super) fn propagate_invariant_arg_through(
        &self,
        _pp: PosId,
        _pn: NegId,
        _np: PosId,
        _nn: NegId,
    ) {
        // See propagate_through: through is not a unification property.
    }
}
