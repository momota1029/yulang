//! Runtime lowering for Yulang.
//!
//! The crate is intentionally narrow: it owns `lower_core_program` and its
//! supporting machinery (profiles, adapter evidence, …). The runtime IR data
//! structures live in `yulang-runtime-ir`, type representation and
//! type-system helpers live in `yulang-runtime-types`, refine / validate /
//! invariant / hygiene live in `yulang-runtime-refine`, and monomorphization
//! lives in `yulang-monomorphize`.

pub mod lower;

pub use lower::{
    CoreShapeProfile, DerivedExpectedEvidenceProfile, ExpectedAdapterEvidenceProfile,
    ExpectedArgEvidenceProfile, ObservedAdapterEvidence, ObservedAdapterEvidenceKind,
    RuntimeAdapterEvent, RuntimeAdapterEventKind, RuntimeAdapterProfile, RuntimeApplyAdapterPhase,
    RuntimeLowerOutput, RuntimeLowerProfile, lower_core_program, lower_core_program_profiled,
    lower_principal_module,
};
