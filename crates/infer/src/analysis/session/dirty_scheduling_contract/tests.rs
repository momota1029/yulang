use std::panic::{AssertUnwindSafe, catch_unwind};

use poly::expr::{Arena as PolyArena, Def, Vis};
use poly::types::{Neg, Pos};

use super::*;
use crate::analysis::AnalysisSession;
use crate::analysis::session::shadow_dirty_oracle::ShadowDirtyDependencyInventory;
use crate::roles::{RoleConstraint, RoleImplCandidate};
use crate::scc::SccInput;
use crate::uses::SelectionUse;

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
fn production_outbox_is_inactive_by_default_and_clears_on_finish_or_unwind() {
    let mut outbox = MethodRoleMutationOutbox::new();
    outbox.record(DependencyKey::ConstraintBounds(TypeVar(64)));
    assert!(outbox.mutations().is_empty());
    assert_eq!(outbox.generation(), MutationGeneration::default());

    {
        let activation = outbox.activate();
        assert!(outbox.is_active());
        outbox.record(DependencyKey::ConstraintBounds(TypeVar(64)));
        assert_eq!(
            outbox.mutations(),
            [MethodRoleMutation::Changed {
                serial: MutationSerial::new(1),
                key: DependencyKey::ConstraintBounds(TypeVar(64)),
            }]
        );
        activation.finish();
    }
    assert!(!outbox.is_active());
    outbox.take();

    let unwind = catch_unwind(AssertUnwindSafe(|| {
        let _activation = outbox.activate();
        outbox.record(DependencyKey::ConstraintLevel(TypeVar(65)));
        panic!("exercise mutation journal unwind cleanup");
    }));
    assert!(unwind.is_err());
    assert!(!outbox.is_active());
    outbox.record(DependencyKey::ConstraintBirthLevel(TypeVar(65)));
    assert_eq!(
        changed_keys(outbox.take()),
        [DependencyKey::ConstraintLevel(TypeVar(65))],
        "unwinding disables later emission but preserves events already produced in the window"
    );
}

#[test]
fn production_outbox_overflow_and_audit_disagreement_clear_owner_eligibility() {
    let mut capacity = MethodRoleMutationOutbox::with_capacity(1);
    let capacity_activation = capacity.activate();
    capacity.record_many([
        DependencyKey::ConstraintNeighbors(TypeVar(66)),
        DependencyKey::ConstraintNeighbors(TypeVar(67)),
    ]);
    assert_eq!(
        capacity.mutations(),
        [MethodRoleMutation::InvalidateAll {
            serial: MutationSerial::new(1),
            reason: InvalidateAllReason::JournalOverflow,
        }]
    );
    assert!(!capacity.owner_eligibility());
    capacity_activation.finish();

    let mut serial = MethodRoleMutationOutbox::with_state(
        usize::MAX,
        MutationSerial::new(u64::MAX),
        MutationGeneration::default(),
    );
    let serial_activation = serial.activate();
    serial.record(DependencyKey::ConstraintBounds(TypeVar(68)));
    assert!(matches!(
        serial.mutations(),
        [MethodRoleMutation::InvalidateAll {
            reason: InvalidateAllReason::MutationSerialOverflow,
            ..
        }]
    ));
    assert!(!serial.owner_eligibility());
    serial_activation.finish();

    let mut generation = MethodRoleMutationOutbox::with_state(
        usize::MAX,
        MutationSerial::default(),
        MutationGeneration::new(u64::MAX),
    );
    let generation_activation = generation.activate();
    generation.record(DependencyKey::ConstraintBounds(TypeVar(69)));
    assert!(matches!(
        generation.mutations(),
        [MethodRoleMutation::InvalidateAll {
            reason: InvalidateAllReason::MutationGenerationOverflow,
            ..
        }]
    ));
    assert!(!generation.owner_eligibility());
    generation_activation.finish();

    let mut audit = MethodRoleMutationOutbox::new();
    let audit_activation = audit.activate();
    let before = audit.generation();
    audit.audit_generation(before, true, "test observable without journal entry");
    assert_eq!(
        audit.mutations(),
        [MethodRoleMutation::InvalidateAll {
            serial: MutationSerial::new(1),
            reason: InvalidateAllReason::AuditFenceDisagreement {
                site: "test observable without journal entry",
            },
        }]
    );
    assert!(!audit.owner_eligibility());
    audit_activation.finish();
}

#[test]
fn session_journal_activation_opens_and_clears_every_outbox_on_unwind() {
    let mut session = AnalysisSession::new(PolyArena::new());
    assert!(!session.method_role_mutation_journal_active());
    assert!(
        !session
            .infer
            .constraints()
            .method_role_mutation_journal_active()
    );
    assert!(!session.roles.method_role_mutation_journal_active());
    assert!(!session.role_impls.method_role_mutation_journal_active());

    let unwind = catch_unwind(AssertUnwindSafe(|| {
        let _activation = session.activate_method_role_mutation_journal();
        assert!(session.method_role_mutation_journal_active());
        assert!(
            session
                .infer
                .constraints()
                .method_role_mutation_journal_active()
        );
        assert!(session.roles.method_role_mutation_journal_active());
        assert!(session.role_impls.method_role_mutation_journal_active());
        panic!("exercise whole-session journal unwind cleanup");
    }));
    assert!(unwind.is_err());
    assert!(!session.method_role_mutation_journal_active());
    assert!(
        !session
            .infer
            .constraints()
            .method_role_mutation_journal_active()
    );
    assert!(!session.roles.method_role_mutation_journal_active());
    assert!(!session.role_impls.method_role_mutation_journal_active());
}

#[test]
fn real_session_mutators_are_silent_inactive_and_publish_typed_keys_active() {
    let mut poly = PolyArena::new();
    let owner = poly.defs.fresh();
    poly.defs.set(
        owner,
        Def::Let {
            vis: Vis::My,
            scheme: None,
            body: None,
            children: Vec::new(),
        },
    );
    let mut session = AnalysisSession::new(poly);

    let inactive_select = session.poly.add_select("inactive_member");
    let inactive_use = selection_use(owner, 90);
    session.register_selection_use(inactive_select, inactive_use);
    assert_eq!(
        session.remove_unresolved_selection(inactive_select),
        Some(inactive_use)
    );
    let inactive_impl = DefId(91);
    let inactive_role = vec!["InactiveCandidate".to_owned()];
    session.register_role_impl_candidate(RoleImplCandidate {
        impl_def: Some(inactive_impl),
        role: inactive_role.clone(),
        inputs: Vec::new(),
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    assert_eq!(
        session.role_impls.role_buckets_for_impl(inactive_impl),
        [inactive_role]
    );
    assert!(
        session.take_method_role_mutations().is_empty(),
        "session-owned production mutators must be a no-op while the journal is inactive"
    );

    let journal = session.activate_method_role_mutation_journal();
    let select = session.poly.add_select("member");
    let other_owner = DefId(101);
    let use_site = selection_use(owner, 110);
    session.register_selection_use(select, use_site);
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[
            DependencyKey::Selection(select),
            DependencyKey::OwnerSelections(owner),
        ],
    );

    let replacement = SelectionUse {
        receiver_value: TypeVar(120),
        ..use_site
    };
    session.register_selection_use(select, replacement);
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[
            DependencyKey::Selection(select),
            DependencyKey::OwnerSelections(owner),
        ],
    );

    let reparented = SelectionUse {
        parent: other_owner,
        ..replacement
    };
    session.register_selection_use(select, reparented);
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[
            DependencyKey::Selection(select),
            DependencyKey::OwnerSelections(owner),
            DependencyKey::OwnerSelections(other_owner),
        ],
    );
    assert_eq!(
        session.remove_unresolved_selection(select),
        Some(reparented)
    );
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[
            DependencyKey::Selection(select),
            DependencyKey::OwnerSelections(other_owner),
        ],
    );

    session.roles.insert(
        owner,
        RoleConstraint {
            role: vec!["RawRole".to_owned()],
            inputs: Vec::new(),
            associated: Vec::new(),
        },
    );
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[DependencyKey::OwnerRawRoles(owner)],
    );

    let impl_def = DefId(130);
    let candidate_role = vec!["CandidateRole".to_owned()];
    let second_candidate_role = vec!["SecondCandidateRole".to_owned()];
    session.register_role_impl_candidate(RoleImplCandidate {
        impl_def: Some(impl_def),
        role: candidate_role.clone(),
        inputs: Vec::new(),
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[DependencyKey::CandidateBucket(candidate_role.clone())],
    );
    session.register_role_impl_candidate(RoleImplCandidate {
        impl_def: Some(impl_def),
        role: second_candidate_role.clone(),
        inputs: Vec::new(),
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[DependencyKey::CandidateBucket(
            second_candidate_role.clone(),
        )],
    );
    assert_eq!(
        session.role_impls.role_buckets_for_impl(impl_def),
        [candidate_role.clone(), second_candidate_role.clone()]
    );

    session.extend_role_impl_prerequisites(
        impl_def,
        [RoleConstraint {
            role: vec!["Prerequisite".to_owned()],
            inputs: Vec::new(),
            associated: Vec::new(),
        }],
    );
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[
            DependencyKey::CandidateBucket(candidate_role.clone()),
            DependencyKey::CandidateBucket(second_candidate_role.clone()),
        ],
    );

    session
        .role_impls
        .add_method_for_impl(impl_def, DefId(131), DefId(132));
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[
            DependencyKey::CandidateBucket(candidate_role),
            DependencyKey::CandidateBucket(second_candidate_role),
        ],
    );

    let root = session.infer.fresh_type_var();
    session.take_method_role_mutations();
    session.apply_scc_input(SccInput::RegisterDef { def: owner, root });
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[DependencyKey::SccRoot(owner)],
    );
    session.apply_scc_input(SccInput::DefFinished { def: owner });
    session.route_scc_events();
    assert!(
        changed_keys(session.take_method_role_mutations()).contains(&DependencyKey::SccRoot(owner))
    );

    let applied = sample_role_resolution_key("AppliedProduction");
    assert!(session.insert_applied_method_role_resolution(applied.clone()));
    assert!(!session.insert_applied_method_role_resolution(applied.clone()));
    assert_changed_keys(
        session.take_method_role_mutations(),
        &[DependencyKey::AppliedResolution(applied)],
    );
    assert!(session.method_role_owner_eligibility());
    journal.finish();

    session.roles.insert(
        owner,
        RoleConstraint {
            role: vec!["InactiveRawRole".to_owned()],
            inputs: Vec::new(),
            associated: Vec::new(),
        },
    );
    assert!(session.take_method_role_mutations().is_empty());
}

#[test]
fn real_constraint_mutators_are_silent_inactive_and_publish_compact_observable_keys_active() {
    use poly::types::{StackWeight, SubtractId, Subtractability};

    use crate::constraints::{ConstraintMachine, TypeLevel};

    let mut machine = ConstraintMachine::new();
    machine.register_type_var(TypeVar(159), TypeLevel::root());
    assert!(machine.take_method_role_mutations().is_empty());

    let journal = machine.activate_method_role_mutations();
    let source = TypeVar(160);
    let target = TypeVar(161);
    machine.register_type_var(source, TypeLevel::root().child());
    assert_changed_keys(
        machine.take_method_role_mutations(),
        &[
            DependencyKey::ConstraintLevel(source),
            DependencyKey::ConstraintBirthLevel(source),
        ],
    );
    machine.register_type_var(target, TypeLevel::root());
    machine.take_method_role_mutations();

    let source_pos = machine.alloc_pos(Pos::Var(source));
    let target_neg = machine.alloc_neg(Neg::Var(target));
    machine.subtype(source_pos, target_neg);
    let mutations = changed_keys(machine.take_method_role_mutations());
    assert!(mutations.contains(&DependencyKey::ConstraintLevel(source)));
    assert!(mutations.contains(&DependencyKey::ConstraintBounds(source)));
    assert!(mutations.contains(&DependencyKey::ConstraintBounds(target)));
    assert!(mutations.contains(&DependencyKey::ConstraintNeighbors(source)));
    assert!(mutations.contains(&DependencyKey::ConstraintNeighbors(target)));

    let subtract = SubtractId(170);
    machine.subtract_fact(source, subtract, Subtractability::All);
    assert!(
        changed_keys(machine.take_method_role_mutations())
            .contains(&DependencyKey::ConstraintSubtractFacts(source))
    );

    let stacked = machine.alloc_pos(Pos::Stack {
        inner: source_pos,
        weight: StackWeight::push(
            subtract,
            Subtractability::Set(vec!["effect".to_owned()], Vec::new()),
        ),
    });
    machine.subtype(stacked, target_neg);
    assert!(
        changed_keys(machine.take_method_role_mutations())
            .contains(&DependencyKey::ConstraintPrePopFamilies(target))
    );

    machine.invalidate_method_role_mutations_for_test(InvalidateAllReason::JournalTruncated);
    assert!(matches!(
        machine.method_role_mutations(),
        [MethodRoleMutation::InvalidateAll {
            reason: InvalidateAllReason::JournalTruncated,
            ..
        }]
    ));
    assert!(!machine.method_role_owner_eligibility());
    journal.finish();
}

#[test]
fn stolen_active_source_mutation_trips_the_session_audit_fence() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let journal = session.activate_method_role_mutation_journal();
    session
        .infer
        .constraints_mut()
        .register_type_var(TypeVar(180), crate::constraints::TypeLevel::root());
    let stolen = session.infer.constraints_mut().take_method_role_mutations();
    assert!(!stolen.is_empty());
    assert!(matches!(
        session.take_method_role_mutations().as_slice(),
        [MethodRoleMutation::InvalidateAll {
            reason: InvalidateAllReason::AuditFenceDisagreement {
                site: "ConstraintMachine::mutation_outbox",
            },
            ..
        }]
    ));
    assert!(!session.method_role_owner_eligibility());
    journal.finish();
}

#[test]
fn coarse_contract_generation_is_additive_to_the_existing_whole_session_guard() {
    let mut session = AnalysisSession::new(PolyArena::new());
    session.record_no_progress_method_role_pass();
    let previous = session
        .last_no_progress_method_role_pass
        .expect("recorded no-progress snapshot");

    let journal = session.activate_method_role_mutation_journal();
    session
        .method_role_mutations
        .record(DependencyKey::MethodTaint(TypeVar(150)));
    let current = session.method_role_pass_input_snapshot();
    assert_ne!(previous.contract_generation, current.contract_generation);
    assert!(previous.guard_inputs_equal(current));
    assert!(
        !session.method_role_pass_inputs_changed(),
        "Stage 2 must not consult the additive contract generation for df1c23f3 skipping"
    );
    journal.finish();
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

fn selection_use(parent: DefId, base: u32) -> SelectionUse {
    SelectionUse {
        parent,
        method_value: TypeVar(base),
        selected_value: TypeVar(base + 1),
        receiver_value: TypeVar(base + 2),
        receiver_effect: TypeVar(base + 3),
        local_method_scope: None,
        recursive_self_value: None,
    }
}

fn assert_changed_keys(actual: Vec<MethodRoleMutation>, expected: &[DependencyKey]) {
    assert_eq!(changed_keys(actual), expected);
}

fn changed_keys(actual: Vec<MethodRoleMutation>) -> Vec<DependencyKey> {
    actual
        .into_iter()
        .map(|mutation| match mutation {
            MethodRoleMutation::Changed { key, .. } => key,
            MethodRoleMutation::InvalidateAll { reason, .. } => {
                panic!("unexpected InvalidateAll: {reason:?}")
            }
        })
        .collect()
}
