//! `mono` から軽量 control 表現へ下げる IR crate。
//!
//! `mono-runtime` は oracle として tree をそのまま読む。この crate は evidence-vm が読む
//! `ExprId` 参照の軽量表現と、その表現から作る evidence summary を持つ。

#![forbid(unsafe_code)]

mod application_provenance;
mod evidence_ir;
mod ir;
mod lower;

pub use application_provenance::ApplicationProvenanceTable;

pub use evidence_ir::{
    ControlAdapterEvidence, ControlDelayedBoundary, ControlDelayedBoundaryKind,
    ControlEffectEvidence, ControlEffectUseKind, ControlEvidenceInstance, ControlEvidenceProgram,
    ControlEvidenceRoute, ControlFallbackEvidence, ControlFallbackKind, ControlHandlerArmEvidence,
    ControlHandlerEvidence, ControlTypeEvidence, ControlTypeEvidenceOwner, ControlTypedExprSlot,
    format_control_evidence_program,
};
pub use ir::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprId, Instance, InstanceId, Pat, Program, RecordField,
    RecordSpread, Root, SelectResolution, Stmt,
};
pub use lower::{LowerError, LowerOutput, lower, lower_with_application_provenance};
