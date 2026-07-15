use std::panic::{AssertUnwindSafe, catch_unwind};

use super::*;
use crate::analysis::session::shadow_dirty_oracle::ShadowDirtyDependencyInventory;

#[test]
fn every_shadow_oracle_read_kind_has_one_typed_dependency_kind() {
    let inventory = ShadowDirtyDependencyInventory {
        scc_roots: 1,
        owner_raw_roles: 1,
        owner_selections: 1,
        constraint_bounds: 1,
        constraint_neighbors: 1,
        constraint_subtract_facts: 1,
        constraint_levels: 1,
        constraint_birth_levels: 1,
        constraint_pre_pop_families: 1,
        candidate_buckets: 1,
        method_taint_entries: 1,
        projection_selections: 1,
        applied_resolutions: 1,
    };

    let mapping = inventory.typed_key_kind_counts();
    assert_eq!(
        mapping.map(|(kind, _)| kind),
        DependencyKeyKind::ALL,
        "the exact Stage 0 fingerprint inventory must map one-for-one to the Stage 1 vocabulary"
    );
    assert!(mapping.into_iter().all(|(_, count)| count == 1));
}

#[test]
fn mutation_contract_matrix_is_deterministic_and_exhaustive() {
    let matrix = mutation_contract_matrix();
    assert_eq!(matrix, mutation_contract_matrix());
    assert_eq!(
        matrix
            .iter()
            .filter_map(|row| match &row.mutation {
                ContractMutation::Known(mutation) => Some(mutation.kind()),
                ContractMutation::Unrecognized { .. } => None,
            })
            .collect::<Vec<_>>(),
        KnownMutationKind::ALL,
        "every current effective mutation kind must have exactly one deterministic matrix row"
    );

    let mut sites = matrix.iter().map(|row| row.site).collect::<Vec<_>>();
    sites.sort_unstable();
    let site_count = sites.len();
    sites.dedup();
    assert_eq!(sites.len(), site_count, "matrix site labels must be unique");

    for row in matrix {
        let actual = record_one(row.mutation);
        let expected = match row.expected {
            MutationContractExpectation::Changed(keys) => changed_events(keys),
            MutationContractExpectation::InvalidateAll(reason) => {
                vec![MethodRoleMutation::InvalidateAll {
                    serial: MutationSerial::new(1),
                    reason,
                }]
            }
        };
        assert_eq!(actual, expected, "contract matrix drift at {}", row.site);
    }
}

#[test]
fn bounds_add_evidence_promotion_prune_and_no_replay_store_expect_bounds_events() {
    let var = TypeVar(40);
    let expected = vec![DependencyKey::ConstraintBounds(var)];
    let adversaries = [
        KnownMutation::LowerBoundAdded { var },
        KnownMutation::UpperBoundAdded { var },
        KnownMutation::EvidenceLowerAdded { var },
        KnownMutation::EvidenceUpperAdded { var },
        KnownMutation::EvidenceLowerPromotedAndRemoved { var },
        KnownMutation::EvidenceUpperPromotedAndRemoved { var },
        KnownMutation::UpperRowPruned { source: var },
        KnownMutation::RowEffectUpperStoredWithoutReplay { source: var },
    ];

    for mutation in adversaries {
        assert_eq!(
            record_one(ContractMutation::Known(mutation)),
            changed_events(expected.clone())
        );
    }
}

#[test]
fn neighbor_add_and_remove_expect_both_endpoint_events() {
    let left = TypeVar(41);
    let right = TypeVar(42);
    let expected = changed_events(vec![
        DependencyKey::ConstraintNeighbors(left),
        DependencyKey::ConstraintNeighbors(right),
    ]);

    assert_eq!(
        record_one(ContractMutation::Known(KnownMutation::NeighborAdded {
            left,
            right,
        })),
        expected
    );
    assert_eq!(
        record_one(ContractMutation::Known(KnownMutation::NeighborRemoved {
            left,
            right,
        })),
        expected
    );
}

#[test]
fn level_birth_subtract_and_pre_pop_changes_expect_their_typed_events() {
    let var = TypeVar(43);
    assert_eq!(
        record_one(ContractMutation::Known(
            KnownMutation::ConstraintLevelLowered { var }
        )),
        changed_events(vec![DependencyKey::ConstraintLevel(var)])
    );
    assert_eq!(
        record_one(ContractMutation::Known(KnownMutation::TypeVarRegistered {
            var,
        })),
        changed_events(vec![
            DependencyKey::ConstraintLevel(var),
            DependencyKey::ConstraintBirthLevel(var),
        ])
    );
    assert_eq!(
        record_one(ContractMutation::Known(KnownMutation::SubtractFactAdded {
            effect: var,
        })),
        changed_events(vec![DependencyKey::ConstraintSubtractFacts(var)])
    );
    assert_eq!(
        record_one(ContractMutation::Known(
            KnownMutation::PrePopFamiliesChanged { var }
        )),
        changed_events(vec![DependencyKey::ConstraintPrePopFamilies(var)])
    );
}

#[test]
fn selection_role_root_taint_and_applied_membership_changes_expect_complete_events() {
    let select = SelectId(50);
    let old_parent = DefId(51);
    let new_parent = DefId(52);
    let var = TypeVar(53);
    let applied = sample_role_resolution_key("Applied");

    assert_eq!(
        record_one(ContractMutation::Known(KnownMutation::SelectionAdded {
            select,
            parent: old_parent,
        })),
        changed_events(vec![
            DependencyKey::Selection(select),
            DependencyKey::OwnerSelections(old_parent),
        ])
    );
    assert_eq!(
        record_one(ContractMutation::Known(KnownMutation::SelectionRemoved {
            select,
            old_parent,
        })),
        changed_events(vec![
            DependencyKey::Selection(select),
            DependencyKey::OwnerSelections(old_parent),
        ])
    );
    assert_eq!(
        record_one(ContractMutation::Known(KnownMutation::SelectionReplaced {
            select,
            parent: old_parent,
        })),
        changed_events(vec![
            DependencyKey::Selection(select),
            DependencyKey::OwnerSelections(old_parent),
        ])
    );
    assert_eq!(
        record_one(ContractMutation::Known(
            KnownMutation::SelectionReparented {
                select,
                old_parent,
                new_parent,
            }
        )),
        changed_events(vec![
            DependencyKey::Selection(select),
            DependencyKey::OwnerSelections(old_parent),
            DependencyKey::OwnerSelections(new_parent),
        ])
    );
    assert_eq!(
        record_one(ContractMutation::Known(KnownMutation::OwnerRawRoleAdded {
            owner: old_parent,
        })),
        changed_events(vec![DependencyKey::OwnerRawRoles(old_parent)])
    );
    assert_eq!(
        record_one(ContractMutation::Known(KnownMutation::SccRootRegistered {
            owner: old_parent,
        })),
        changed_events(vec![DependencyKey::SccRoot(old_parent)])
    );
    assert_eq!(
        record_one(ContractMutation::Known(
            KnownMutation::SccOpenComponentRemoved {
                owners: vec![old_parent, new_parent],
            }
        )),
        changed_events(vec![
            DependencyKey::SccRoot(old_parent),
            DependencyKey::SccRoot(new_parent),
        ])
    );
    assert_eq!(
        record_one(ContractMutation::Known(
            KnownMutation::MethodTaintProjectionChanged { var }
        )),
        changed_events(vec![DependencyKey::MethodTaint(var)])
    );
    assert_eq!(
        record_one(ContractMutation::Known(
            KnownMutation::AppliedResolutionInserted {
                key: applied.clone(),
            }
        )),
        changed_events(vec![DependencyKey::AppliedResolution(applied)])
    );
}

#[test]
fn candidate_and_prerequisite_changes_cover_transitively_read_buckets() {
    let role_a = role_path("A");
    let role_b = role_path("B");
    let role_c = role_path("C");
    let collector = SessionLocalOwnerReadCollector::default();
    let capture = collector.activate();
    collector.record(DependencyKey::CandidateBucket(role_a.clone()));
    collector.record(DependencyKey::CandidateBucket(role_b.clone()));
    collector.record(DependencyKey::CandidateBucket(role_c.clone()));
    collector.record(DependencyKey::CandidateBucket(role_b.clone()));
    let reads = capture.finish();
    assert_eq!(
        reads.dependencies(),
        [
            DependencyKey::CandidateBucket(role_a.clone()),
            DependencyKey::CandidateBucket(role_b.clone()),
            DependencyKey::CandidateBucket(role_c.clone()),
        ],
        "top-level and recursively reached prerequisite buckets must use the same typed key"
    );

    assert_eq!(
        record_one(ContractMutation::Known(
            KnownMutation::CandidateRegistered {
                role: role_b.clone(),
            }
        )),
        changed_events(vec![DependencyKey::CandidateBucket(role_b)])
    );
    assert_eq!(
        record_one(ContractMutation::Known(
            KnownMutation::CandidatePrerequisitesExtended {
                candidate_roles: vec![role_a.clone(), role_c.clone()],
            }
        )),
        changed_events(vec![
            DependencyKey::CandidateBucket(role_a),
            DependencyKey::CandidateBucket(role_c),
        ])
    );
}

#[test]
fn unrecognized_mutation_invalidates_all_and_never_falls_through_silently() {
    let mut harness = MutationContractHarness::new(16);
    let expected = vec![MethodRoleMutation::InvalidateAll {
        serial: MutationSerial::new(1),
        reason: InvalidateAllReason::UnrecognizedMutation {
            site: "future-side-table-mutation",
        },
    }];

    assert_eq!(
        harness.record(ContractMutation::Unrecognized {
            site: "future-side-table-mutation",
        }),
        expected
    );
    assert_eq!(harness.journal(), expected);
    assert_eq!(
        harness.record(ContractMutation::Known(KnownMutation::LowerBoundAdded {
            var: TypeVar(60),
        })),
        expected,
        "once contract provenance is unknown, later recognized changes cannot restore eligibility"
    );
}

#[test]
fn journal_capacity_and_serial_overflow_invalidate_all() {
    let mut capacity = MutationContractHarness::new(1);
    assert_eq!(
        capacity.record(ContractMutation::Known(KnownMutation::NeighborAdded {
            left: TypeVar(61),
            right: TypeVar(62),
        })),
        vec![MethodRoleMutation::InvalidateAll {
            serial: MutationSerial::new(1),
            reason: InvalidateAllReason::JournalOverflow,
        }]
    );

    let mut serial =
        MutationContractHarness::with_last_serial(usize::MAX, MutationSerial::new(u64::MAX));
    assert_eq!(
        serial.record(ContractMutation::Known(KnownMutation::LowerBoundAdded {
            var: TypeVar(63),
        })),
        vec![MethodRoleMutation::InvalidateAll {
            serial: MutationSerial::new(u64::MAX),
            reason: InvalidateAllReason::MutationSerialOverflow,
        }]
    );
}

#[test]
fn session_local_read_collector_is_inactive_by_default_and_clears_on_finish_or_unwind() {
    let collector = SessionLocalOwnerReadCollector::default();
    let var = TypeVar(70);

    record_six_constraint_reads(&collector, var);
    assert!(collector.activate().finish().dependencies().is_empty());

    let capture = collector.activate();
    record_six_constraint_reads(&collector, var);
    collector.record_constraint_bounds(var);
    assert_eq!(
        capture.finish().dependencies(),
        [
            DependencyKey::ConstraintBounds(var),
            DependencyKey::ConstraintNeighbors(var),
            DependencyKey::ConstraintSubtractFacts(var),
            DependencyKey::ConstraintLevel(var),
            DependencyKey::ConstraintBirthLevel(var),
            DependencyKey::ConstraintPrePopFamilies(var),
        ]
    );

    collector.record_constraint_bounds(var);
    assert!(collector.activate().finish().dependencies().is_empty());

    let unwind = catch_unwind(AssertUnwindSafe(|| {
        let _capture = collector.activate();
        collector.record_constraint_bounds(var);
        panic!("exercise collector unwind cleanup");
    }));
    assert!(unwind.is_err());
    assert!(collector.activate().finish().dependencies().is_empty());

    let source = include_str!("../dirty_scheduling_contract.rs");
    assert!(!source.contains("thread_local!"));
    assert!(!source.contains("OwnerDependencyFingerprint"));
}

fn record_one(mutation: ContractMutation) -> Vec<MethodRoleMutation> {
    MutationContractHarness::new(usize::MAX).record(mutation)
}

fn changed_events(keys: Vec<DependencyKey>) -> Vec<MethodRoleMutation> {
    keys.into_iter()
        .map(|key| MethodRoleMutation::Changed {
            serial: MutationSerial::new(1),
            key,
        })
        .collect()
}

fn record_six_constraint_reads(collector: &SessionLocalOwnerReadCollector, var: TypeVar) {
    collector.record_constraint_bounds(var);
    collector.record_constraint_neighbors(var);
    collector.record_constraint_subtract_facts(var);
    collector.record_constraint_level(var);
    collector.record_constraint_birth_level(var);
    collector.record_constraint_pre_pop_families(var);
}
