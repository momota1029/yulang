//! Default-off read-only facade for HIR-owned structural research artifacts.
//! This module performs no parsing, identity minting, solving or production routing.

pub use yu_hir::shadow::{
    AnnotationOccurrence, Binder, BinderId, Correspondence, ExprId, Expression, Form,
    MAX_RAW_ELEMENTS, MAX_SYNTAX_DEPTH, PendingPremise, Position, PositionId, Premise,
    ShadowArtifact, ShadowError, Skeleton, UseId,
};
