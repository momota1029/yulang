//! Public work and diagnostic types for `AnalysisSession`.
//!
//! `AnalysisSession` owns the queue, but these small enums describe the protocol
//! used by lowering, resolution, and SCC routing.

use poly::expr::{DefId, RefId, SelectId, SelectResolution};

use crate::scc::SccInput;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnalysisDiagnostic {
    ComputedFetchCycle {
        component: Vec<DefId>,
        parent: DefId,
        target: DefId,
    },
}

impl AnalysisDiagnostic {
    /// Return the definition that diagnostics should attach to first.
    pub fn primary_def(&self) -> DefId {
        match self {
            Self::ComputedFetchCycle { parent, .. } => *parent,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnalysisWork {
    /// Ask the name resolver to resolve this reference.
    ResolveRef(RefId),
    /// Re-check whether the receiver/effect constraints now determine a selection.
    ProbeSelect(SelectId),
    /// Apply a resolved reference to `poly` and the SCC dependency graph.
    ApplyRefResolution { ref_id: RefId, target: DefId },
    /// Apply a resolved selection to `poly`, constraints, and SCC dependency graph.
    ApplySelectionResolution {
        select_id: SelectId,
        target: SelectionTarget,
    },
    /// Forward lowering/resolution events to the SCC machine through the same queue.
    Scc(SccInput),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SelectionTarget {
    /// Plain record projection. It constrains the receiver but does not add an SCC edge.
    RecordField,
    /// Nominal type method selected from a receiver type.
    Method { def: DefId },
    /// Effect method selected from the receiver effect row.
    EffectMethod { def: DefId },
    /// Role method selected through the role solver.
    TypeclassMethod {
        /// Receiver-specific demand is not fabricated here. Method instantiation
        /// creates the only demand, with receiver flowing into its first input.
        member: DefId,
    },
}

impl SelectionTarget {
    /// Convert the analysis-side target into the compact `poly` selection result.
    pub fn resolution(&self) -> SelectResolution {
        match self {
            Self::RecordField => SelectResolution::RecordField,
            Self::Method { def } => SelectResolution::Method { def: *def },
            Self::EffectMethod { def } => SelectResolution::Method { def: *def },
            Self::TypeclassMethod { member } => {
                SelectResolution::TypeclassMethod { member: *member }
            }
        }
    }
}
