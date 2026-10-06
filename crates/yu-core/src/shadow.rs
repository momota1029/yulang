//! Default-off read-only facade for HIR-owned structural research artifacts.
//! This module performs no parsing, identity minting, solving or production routing.

pub use yu_hir::shadow::{
    AnnotationId, AnnotationOccurrence, ApplicationSourceOccurrence, Binder, BinderId,
    CaptureUseIncidence, ClosureCorrespondence, Correspondence, ExprId, Expression, Form,
    MAX_RAW_ELEMENTS, MAX_SYNTAX_DEPTH, ParameterAnnotationIncidence, PendingPremise, Position,
    PositionId, Premise, ResolvedCallIncidence, ShadowArtifact, ShadowError, Skeleton, UseId,
};
