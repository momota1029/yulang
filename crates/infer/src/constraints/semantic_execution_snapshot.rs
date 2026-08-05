//! CPK-0a semantic-execution baseline capture.
//!
//! The trace is test-only and opt-in. Production builds contain neither the trace field nor its
//! hot-path hooks. Logical proof relations deliberately remain outside this module (CPK-0b).

use super::*;
use crate::scc::{SccEvent, SccStats};

thread_local! {
    static CAPTURE_NEW_MACHINES: Cell<usize> = const { Cell::new(0) };
}

pub(crate) fn with_semantic_execution_snapshot_capture_for_new_machines<R>(
    f: impl FnOnce() -> R,
) -> R {
    struct Reset(usize);
    impl Drop for Reset {
        fn drop(&mut self) {
            CAPTURE_NEW_MACHINES.set(self.0);
        }
    }

    let previous = CAPTURE_NEW_MACHINES.get();
    CAPTURE_NEW_MACHINES.set(previous.saturating_add(1));
    let _reset = Reset(previous);
    f()
}

pub(super) fn trace_for_new_constraint_machine() -> Option<SemanticExecutionTrace> {
    CAPTURE_NEW_MACHINES
        .get()
        .ne(&0)
        .then(SemanticExecutionTrace::default)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SemanticExecutionSnapshot {
    pub(crate) queue_events: Vec<SemanticQueueEvent>,
    pub(crate) constraints: Vec<SemanticConstraintSnapshot>,
    pub(crate) canonical_constraint_count: usize,
    pub(crate) bounds: Vec<SemanticBoundSnapshot>,
    pub(crate) replay: ReplayExecutionSnapshot,
    pub(crate) row: RowExecutionSnapshot,
    pub(crate) publication: PublicationSnapshot,
    pub(crate) scc: SccExecutionSnapshot,
    pub(crate) output: SemanticOutputSnapshot,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SemanticQueueEvent {
    Enqueued {
        ordinal: usize,
        work: SemanticWorkSnapshot,
    },
    Dequeued {
        ordinal: usize,
        work: SemanticWorkSnapshot,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SemanticWorkSnapshot {
    Subtype {
        record: ConstraintRecordId,
        key: SubtypeConstraintKey,
    },
    Subtract {
        effect: TypeVar,
        id: SubtractId,
        subtractability: Subtractability,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SemanticConstraintSnapshot {
    pub(crate) record: ConstraintRecordId,
    pub(crate) key: SubtypeConstraintKey,
    pub(crate) queue_admitted: bool,
    pub(crate) canonicalization_dispositions: Vec<ConstraintCanonicalizationDisposition>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SemanticBoundSnapshot {
    pub(crate) record: BoundRecordId,
    pub(crate) direction: BoundDirection,
    pub(crate) owner: TypeVar,
    pub(crate) endpoint: BoundEndpoint,
    pub(crate) weights: ConstraintWeights,
    pub(crate) state: BoundRecordState,
    pub(crate) disposition: Option<BoundDispositionRecordId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReplayExecutionSnapshot {
    pub(crate) lower_inputs: usize,
    pub(crate) upper_inputs: usize,
    pub(crate) lower_accepted: usize,
    pub(crate) upper_accepted: usize,
    pub(crate) lower_enqueued: usize,
    pub(crate) upper_enqueued: usize,
    pub(crate) lower_canonical_duplicate: usize,
    pub(crate) upper_canonical_duplicate: usize,
    pub(crate) lower_trivial: usize,
    pub(crate) upper_trivial: usize,
    pub(crate) lower_evidence_only: usize,
    pub(crate) upper_evidence_only: usize,
    pub(crate) lower_prefiltered: usize,
    pub(crate) upper_prefiltered: usize,
    pub(crate) canonical_constraint_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RowExecutionSnapshot {
    pub(crate) residuals: Vec<RowResidualSnapshot>,
    pub(crate) reductions: Vec<RowReductionSnapshot>,
    pub(crate) subtract_facts: Vec<RowSubtractFactSnapshot>,
    pub(crate) lower_filters: Vec<RowLowerFilterSnapshot>,
    pub(crate) derivation_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RowResidualSnapshot {
    pub(crate) record: RowResidualRecordId,
    pub(crate) source: TypeVar,
    pub(crate) retained_families: Vec<(Vec<String>, Vec<NeuId>)>,
    pub(crate) weight: LeftConstraintWeight,
    pub(crate) fresh_tail: TypeVar,
    pub(crate) derivation_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RowReductionSnapshot {
    pub(crate) source: TypeVar,
    pub(crate) producer: Option<ConstraintRecordId>,
    pub(crate) original_items: Vec<NegId>,
    pub(crate) original_tail: NegId,
    pub(crate) original_upper: NegId,
    pub(crate) consumed_items: Vec<NegId>,
    pub(crate) remaining_items: Vec<NegId>,
    pub(crate) current_reduced_upper: NegId,
    pub(crate) current_record: BoundRecordId,
    pub(crate) processed_lower_records: Vec<BoundRecordId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RowSubtractFactSnapshot {
    pub(crate) record: SubtractFactRecordId,
    pub(crate) effect: TypeVar,
    pub(crate) fact: SubtractFact,
    pub(crate) active: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RowLowerFilterSnapshot {
    pub(crate) record: LowerFilterRecordId,
    pub(crate) var: TypeVar,
    pub(crate) filter: Subtractability,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SemanticEpochKind {
    Constraint,
    Provenance,
    RoleSolveSupplemental,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SemanticEpochEvent {
    pub(crate) kind: SemanticEpochKind,
    pub(crate) constraint: u64,
    pub(crate) provenance: u64,
    pub(crate) role_solve_supplemental: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PublicationSnapshot {
    pub(crate) constraint_events: Vec<ConstraintEvent>,
    pub(crate) epochs: Vec<SemanticEpochEvent>,
    pub(crate) final_constraint_epoch: u64,
    pub(crate) final_provenance_epoch: u64,
    pub(crate) final_role_solve_supplemental_epoch: u64,
    pub(crate) projectability_included_owners: Vec<TypeVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SccExecutionSnapshot {
    pub(crate) stats: SccStats,
    pub(crate) events: Vec<SccEvent>,
    pub(crate) generalization_restart_census: Vec<(String, usize)>,
}

impl SccExecutionSnapshot {
    pub(crate) fn new(stats: SccStats, events: Vec<SccEvent>) -> Self {
        Self {
            stats,
            events,
            generalization_restart_census: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct SemanticOutputSnapshot {
    pub(crate) finalized_schemes: Vec<(DefId, String, String)>,
    pub(crate) alpha_equivalence_view: Vec<(DefId, String)>,
    pub(crate) role_predicates: Vec<(DefId, Vec<String>)>,
    pub(crate) unresolved_selections: Vec<String>,
    pub(crate) lowering_errors: Vec<String>,
    pub(crate) diagnostics: Vec<String>,
    pub(crate) poly_arena_dump: String,
    pub(crate) compiled_surfaces: Vec<String>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct SemanticExecutionTrace {
    queue_events: Vec<SemanticQueueEvent>,
    publication_events: Vec<ConstraintEvent>,
    epoch_events: Vec<SemanticEpochEvent>,
    next_enqueue_ordinal: usize,
    next_dequeue_ordinal: usize,
}

impl ConstraintMachine {
    pub(crate) fn semantic_execution_snapshot(
        &self,
        scc: SccExecutionSnapshot,
        output: SemanticOutputSnapshot,
    ) -> SemanticExecutionSnapshot {
        let trace = self
            .semantic_execution_trace
            .as_ref()
            .expect("SemanticExecutionSnapshot capture must be explicitly enabled");
        let queue_admitted = trace
            .queue_events
            .iter()
            .filter_map(|event| match event {
                SemanticQueueEvent::Enqueued {
                    work: SemanticWorkSnapshot::Subtype { record, .. },
                    ..
                } => Some(*record),
                _ => None,
            })
            .collect::<FxHashSet<_>>();
        let constraints = self
            .constraint_records
            .iter()
            .enumerate()
            .map(|(index, record)| SemanticConstraintSnapshot {
                record: ConstraintRecordId(index as u32),
                key: record.key.clone(),
                queue_admitted: queue_admitted.contains(&ConstraintRecordId(index as u32)),
                canonicalization_dispositions: record.canonicalization_dispositions.clone(),
            })
            .collect();
        let bounds = self
            .bounds
            .records
            .iter()
            .enumerate()
            .map(|(index, record)| SemanticBoundSnapshot {
                record: BoundRecordId(index as u32),
                direction: record.direction,
                owner: record.owner,
                endpoint: record.endpoint,
                weights: record.weights.clone(),
                state: record.state,
                disposition: record.disposition,
            })
            .collect();
        let timing = self.timing();
        let replay = ReplayExecutionSnapshot {
            lower_inputs: timing.lower_replay_inputs,
            upper_inputs: timing.upper_replay_inputs,
            lower_accepted: timing.lower_replay_accepted,
            upper_accepted: timing.upper_replay_accepted,
            lower_enqueued: timing.lower_replay_enqueued,
            upper_enqueued: timing.upper_replay_enqueued,
            lower_canonical_duplicate: timing.lower_replay_duplicate,
            upper_canonical_duplicate: timing.upper_replay_duplicate,
            lower_trivial: timing.lower_replay_trivial,
            upper_trivial: timing.upper_replay_trivial,
            lower_evidence_only: timing.lower_replay_evidence_only,
            upper_evidence_only: timing.upper_replay_evidence_only,
            lower_prefiltered: timing.lower_replay_prefiltered,
            upper_prefiltered: timing.upper_replay_prefiltered,
            canonical_constraint_count: timing.canonical_subtype_constraints,
        };
        let row = self.semantic_row_execution_snapshot();
        let mut constraint_events = trace.publication_events.clone();
        constraint_events.extend(self.events.iter().cloned());
        let mut projectability_included_owners = self
            .bounds
            .scheme_projection_claimed_lower_owners
            .iter()
            .copied()
            .collect::<Vec<_>>();
        projectability_included_owners.sort_by_key(|var| var.0);
        let publication = PublicationSnapshot {
            constraint_events,
            epochs: trace.epoch_events.clone(),
            final_constraint_epoch: self.epoch.as_u64(),
            final_provenance_epoch: self.provenance_epoch.as_u64(),
            final_role_solve_supplemental_epoch: self.role_solve_supplemental_epoch.as_u64(),
            projectability_included_owners,
        };
        SemanticExecutionSnapshot {
            queue_events: trace.queue_events.clone(),
            constraints,
            canonical_constraint_count: self.canonical_constraint_count(),
            bounds,
            replay,
            row,
            publication,
            scc,
            output,
        }
    }

    fn semantic_row_execution_snapshot(&self) -> RowExecutionSnapshot {
        let residuals = self
            .row_residual_records
            .iter()
            .enumerate()
            .map(|(index, record)| RowResidualSnapshot {
                record: RowResidualRecordId(index as u32),
                source: record.key.source,
                retained_families: record
                    .key
                    .retained_families
                    .iter()
                    .map(|family| (family.path.clone(), family.args.clone()))
                    .collect(),
                weight: record.key.weight.clone(),
                fresh_tail: record.gamma,
                derivation_count: record.derivations.len(),
            })
            .collect();
        let reductions = self
            .unweighted_row_reduction_records
            .iter()
            .map(|record| {
                let mut processed_lower_records = record
                    .processed_lower_records
                    .iter()
                    .copied()
                    .collect::<Vec<_>>();
                processed_lower_records.sort_by_key(|record| record.0);
                RowReductionSnapshot {
                    source: record.source,
                    producer: record.producer_constraint,
                    original_items: record.original_items.clone(),
                    original_tail: record.original_tail,
                    original_upper: record.original_upper,
                    consumed_items: record.consumed_items.clone(),
                    remaining_items: record.remaining_items.clone(),
                    current_reduced_upper: record.current_reduced_upper.endpoint,
                    current_record: record.current_reduced_upper.record,
                    processed_lower_records,
                }
            })
            .collect();
        let subtract_facts = self
            .subtracts
            .records
            .iter()
            .enumerate()
            .map(|(index, record)| RowSubtractFactSnapshot {
                record: SubtractFactRecordId(index as u32),
                effect: record.key.effect,
                fact: record.key.fact.clone(),
                active: record.active,
            })
            .collect();
        let lower_filters = self
            .lower_filter_records
            .iter()
            .enumerate()
            .map(|(index, record)| RowLowerFilterSnapshot {
                record: LowerFilterRecordId(index as u32),
                var: record.var,
                filter: record.filter.clone(),
            })
            .collect();
        RowExecutionSnapshot {
            residuals,
            reductions,
            subtract_facts,
            lower_filters,
            derivation_count: self.row_derivations.len(),
        }
    }

    pub(super) fn record_semantic_queue_enqueue(&mut self, work: &ConstraintWork) {
        let Some(trace) = self.semantic_execution_trace.as_mut() else {
            return;
        };
        let work = semantic_work_snapshot(work, &self.constraint_records);
        let ordinal = trace.next_enqueue_ordinal;
        trace.next_enqueue_ordinal = ordinal.saturating_add(1);
        trace
            .queue_events
            .push(SemanticQueueEvent::Enqueued { ordinal, work });
    }

    pub(super) fn record_semantic_queue_dequeue(&mut self, work: &ConstraintWork) {
        let Some(trace) = self.semantic_execution_trace.as_mut() else {
            return;
        };
        let work = semantic_work_snapshot(work, &self.constraint_records);
        let ordinal = trace.next_dequeue_ordinal;
        trace.next_dequeue_ordinal = ordinal.saturating_add(1);
        trace
            .queue_events
            .push(SemanticQueueEvent::Dequeued { ordinal, work });
    }

    pub(super) fn record_semantic_publication_events(&mut self) {
        let Some(trace) = self.semantic_execution_trace.as_mut() else {
            return;
        };
        trace.publication_events.extend(self.events.iter().cloned());
    }

    pub(super) fn record_semantic_epoch_event(&mut self, kind: SemanticEpochKind) {
        let Some(trace) = self.semantic_execution_trace.as_mut() else {
            return;
        };
        trace.epoch_events.push(SemanticEpochEvent {
            kind,
            constraint: self.epoch.as_u64(),
            provenance: self.provenance_epoch.as_u64(),
            role_solve_supplemental: self.role_solve_supplemental_epoch.as_u64(),
        });
    }
}

fn semantic_work_snapshot(
    work: &ConstraintWork,
    constraints: &[ConstraintRecord],
) -> SemanticWorkSnapshot {
    match work {
        ConstraintWork::Subtype(record) => SemanticWorkSnapshot::Subtype {
            record: *record,
            key: constraints[record.0 as usize].key.clone(),
        },
        ConstraintWork::SubtractFact(fact) => SemanticWorkSnapshot::Subtract {
            effect: fact.effect,
            id: fact.fact.id,
            subtractability: fact.fact.subtractability.clone(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scc::SccMachine;

    #[test]
    fn cpk_0a_captures_semantic_execution_end_to_end_without_adding_work() {
        let machine = with_semantic_execution_snapshot_capture_for_new_machines(|| {
            let mut machine = ConstraintMachine::new();
            let pivot = TypeVar(0);
            let lower = machine.alloc_pos(Pos::Con(vec!["lower".into()], Vec::new()));
            let pivot_neg = machine.alloc_neg(Neg::Var(pivot));
            machine.subtype(lower, pivot_neg, OriginId::unknown_internal());

            let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
            let upper = machine.alloc_neg(Neg::Con(vec!["upper".into()], Vec::new()));
            machine.subtype(pivot_pos, upper, OriginId::unknown_internal());

            machine.subtract_fact(
                pivot,
                SubtractId(0),
                Subtractability::Set(vec!["io".into()], Vec::new()),
            );
            machine
        });

        let mut scc = SccMachine::new();
        scc.register_def(DefId(0), TypeVar(0));
        scc.finish_def(DefId(0));
        let scc = SccExecutionSnapshot::new(scc.stats(), scc.take_events());
        let output = SemanticOutputSnapshot {
            finalized_schemes: vec![(
                DefId(0),
                "lower <: upper".into(),
                "fixture-scheme-raw".into(),
            )],
            alpha_equivalence_view: vec![(DefId(0), "alpha-0".into())],
            poly_arena_dump: "fixture-poly-arena".into(),
            ..SemanticOutputSnapshot::default()
        };

        let timing_before = machine.timing();
        let pending_before = machine.pending_constraint_work();
        let snapshot = machine.semantic_execution_snapshot(scc, output);

        assert!(snapshot.queue_events.len() >= 8);
        assert_eq!(
            snapshot
                .queue_events
                .iter()
                .filter(|event| matches!(event, SemanticQueueEvent::Enqueued { .. }))
                .count(),
            snapshot
                .queue_events
                .iter()
                .filter(|event| matches!(event, SemanticQueueEvent::Dequeued { .. }))
                .count(),
        );
        assert_eq!(
            snapshot.canonical_constraint_count,
            snapshot.constraints.len()
        );
        assert!(
            snapshot
                .constraints
                .iter()
                .all(|record| record.queue_admitted)
        );
        assert!(snapshot.bounds.len() >= 2);
        assert!(snapshot.replay.lower_inputs + snapshot.replay.upper_inputs > 0);
        assert_eq!(snapshot.row.subtract_facts.len(), 1);
        assert!(!snapshot.publication.constraint_events.is_empty());
        assert!(!snapshot.publication.epochs.is_empty());
        assert!(!snapshot.scc.events.is_empty());
        assert_eq!(snapshot.output.finalized_schemes[0].0, DefId(0));

        assert_eq!(machine.timing(), timing_before);
        assert_eq!(machine.pending_constraint_work(), pending_before);
    }
}
