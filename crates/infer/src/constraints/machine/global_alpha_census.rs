//! Shadow-only census for replay consequences under a rooted global alpha view.
//!
//! The semantic replay path remains authoritative.  This module observes its decisions only while
//! an explicit test capture is installed; it never suppresses or rewrites a constraint.

use std::cell::RefCell;
use std::collections::hash_map::Entry;

use poly::types::{
    NeuId, PosId, RolePredicate, RolePredicateArg, Scheme, SubtractId, Subtractability, TypeArena,
    TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::interface_oracle::{
    BoundaryInterface, ClosureScan, InterfaceViolation, SchemeAlphaView,
};

use super::*;

/// The four mutually exclusive classes requested by the Mechanism-2 census.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct GlobalAlphaConsequenceCensusSnapshot {
    pub(crate) exact_duplicate_or_trivial: usize,
    pub(crate) locally_isomorphic_but_distinct: usize,
    pub(crate) globally_alpha_equivalent: usize,
    pub(crate) genuinely_novel: usize,
    pub(crate) exact_duplicates: usize,
    pub(crate) trivial: usize,
    pub(crate) accepted: usize,
    pub(crate) pair_candidates: usize,
    pub(crate) oracle_comparisons: usize,
    pub(crate) oracle_mismatches: usize,
    pub(crate) max_component_constraints: usize,
}

impl GlobalAlphaConsequenceCensusSnapshot {
    pub(crate) fn classified_total(self) -> usize {
        self.exact_duplicate_or_trivial
            + self.locally_isomorphic_but_distinct
            + self.globally_alpha_equivalent
            + self.genuinely_novel
    }
}

#[derive(Default)]
struct CaptureState {
    snapshot: GlobalAlphaConsequenceCensusSnapshot,
    accepted: Vec<AcceptedAlphaViews>,
}

struct AcceptedAlphaViews {
    local: SchemeAlphaView,
    global: SchemeAlphaView,
}

std::thread_local! {
    static TEST_CAPTURE: RefCell<Option<CaptureState>> = const { RefCell::new(None) };
}

pub(crate) fn capture_global_alpha_consequence_census<T>(
    run: impl FnOnce() -> T,
) -> (T, GlobalAlphaConsequenceCensusSnapshot) {
    TEST_CAPTURE.with(|capture| {
        assert!(
            capture.borrow().is_none(),
            "nested global-alpha consequence census capture"
        );
        *capture.borrow_mut() = Some(CaptureState::default());
    });
    let output = run();
    let state = TEST_CAPTURE.with(|capture| {
        capture
            .borrow_mut()
            .take()
            .expect("global-alpha consequence census capture must remain installed")
    });
    (output, state.snapshot)
}

pub(super) fn record_prefiltered_trivial() {
    update_capture(|state| {
        state.snapshot.trivial += 1;
        state.snapshot.exact_duplicate_or_trivial += 1;
        state.snapshot.pair_candidates += 1;
    });
}

pub(super) fn record_prefiltered_exact_duplicate() {
    record_exact_duplicate();
}

pub(super) fn record_delayed_exact_duplicate() {
    record_exact_duplicate();
}

fn record_exact_duplicate() {
    update_capture(|state| {
        state.snapshot.exact_duplicates += 1;
        state.snapshot.exact_duplicate_or_trivial += 1;
        state.snapshot.pair_candidates += 1;
    });
}

pub(super) fn record_accepted_consequence(
    machine: &ConstraintMachine,
    root: &SubtypeConstraintKey,
    derivation: BinaryReplayDerivation,
) {
    if !capture_active() {
        return;
    }

    let Some(views) = build_alpha_views(machine, root, derivation) else {
        // A strict oracle construction failure is a parity failure, never a reason to use a looser
        // alpha relation.  Keep the consequence novel so the census remains conservative.
        update_capture(|state| {
            state.snapshot.pair_candidates += 1;
            state.snapshot.accepted += 1;
            state.snapshot.genuinely_novel += 1;
            state.snapshot.oracle_mismatches += 1;
        });
        return;
    };

    update_capture(|state| {
        state.snapshot.pair_candidates += 1;
        state.snapshot.accepted += 1;
        state.snapshot.max_component_constraints = state
            .snapshot
            .max_component_constraints
            .max(views.component_constraints);

        let mut local_match = false;
        let mut global_match = false;
        for previous in &state.accepted {
            state.snapshot.oracle_comparisons += 1;
            if previous.local != views.views.local {
                continue;
            }
            local_match = true;
            if previous.global == views.views.global {
                global_match = true;
                break;
            }
        }

        if global_match {
            state.snapshot.globally_alpha_equivalent += 1;
        } else if local_match {
            state.snapshot.locally_isomorphic_but_distinct += 1;
        } else {
            state.snapshot.genuinely_novel += 1;
        }
        state.accepted.push(views.views);
    });
}

fn capture_active() -> bool {
    TEST_CAPTURE.with(|capture| capture.borrow().is_some())
}

fn update_capture(update: impl FnOnce(&mut CaptureState)) {
    TEST_CAPTURE.with(|capture| {
        if let Some(state) = capture.borrow_mut().as_mut() {
            update(state);
        }
    });
}

struct BuiltAlphaViews {
    views: AcceptedAlphaViews,
    component_constraints: usize,
}

fn build_alpha_views(
    machine: &ConstraintMachine,
    root: &SubtypeConstraintKey,
    derivation: BinaryReplayDerivation,
) -> Option<BuiltAlphaViews> {
    let component = rooted_constraint_component(machine, root);
    let local = local_alpha_view(machine, root)?;
    let global = global_alpha_view(machine, root, derivation, &component)?;
    Some(BuiltAlphaViews {
        views: AcceptedAlphaViews { local, global },
        component_constraints: component.len(),
    })
}

fn rooted_constraint_component(
    machine: &ConstraintMachine,
    root: &SubtypeConstraintKey,
) -> Vec<ConstraintRecordId> {
    let mut connected = constraint_vars(&machine.types, root);
    let inventories = machine
        .constraint_records
        .iter()
        .map(|record| constraint_vars(&machine.types, &record.key))
        .collect::<Vec<_>>();
    let mut included = vec![false; inventories.len()];
    let mut changed = true;
    while changed {
        changed = false;
        for (index, vars) in inventories.iter().enumerate() {
            if included[index] || vars.is_disjoint(&connected) {
                continue;
            }
            included[index] = true;
            connected.extend(vars.iter().copied());
            changed = true;
        }
    }
    included
        .into_iter()
        .enumerate()
        .filter_map(|(index, included)| included.then_some(ConstraintRecordId(index as u32)))
        .collect()
}

fn local_alpha_view(
    machine: &ConstraintMachine,
    root: &SubtypeConstraintKey,
) -> Option<SchemeAlphaView> {
    let mut roles = Vec::new();
    let mut subtract_names = AlphaIdentityNames::default();
    roles.push(constraint_role("root", root, &mut subtract_names));
    let vars = constraint_vars(&machine.types, root);
    alpha_view(
        &machine.types,
        root.lower,
        roles,
        vars.iter().copied().collect(),
        Vec::new(),
        collect_scheme_subtracts(&machine.types, root, std::iter::empty()),
    )
}

fn global_alpha_view(
    machine: &ConstraintMachine,
    root: &SubtypeConstraintKey,
    derivation: BinaryReplayDerivation,
    component: &[ConstraintRecordId],
) -> Option<SchemeAlphaView> {
    let mut identities = AlphaIdentityNames::default();
    let mut roles = Vec::new();
    let root_record = machine.canonical_constraints.get(root).copied();
    roles.push(constraint_role(
        &format!(
            "root:{}:{}:{}:{}",
            replay_rule_name(derivation.rule),
            identities.type_var(derivation.pivot),
            identities.bound(derivation.lower),
            identities.bound(derivation.upper),
        ),
        root,
        &mut identities,
    ));

    let mut instance_vars: FxHashMap<TypeVar, FxHashSet<SchemeInstantiationId>> =
        FxHashMap::default();
    for &record_id in component {
        let record = &machine.constraint_records[record_id.0 as usize];
        let constraint_name = identities.constraint(record_id);
        if Some(record_id) != root_record {
            roles.push(constraint_role(
                &format!("edge:{constraint_name}"),
                &record.key,
                &mut identities,
            ));
        }
        for instantiation in record
            .scheme_instantiation_derivations
            .iter()
            .map(|item| item.instantiation)
            .chain(
                record
                    .scheme_instantiation_routes
                    .iter()
                    .map(|item| item.derivation.instantiation),
            )
        {
            mark_constraint_instance_vars(
                &machine.types,
                &record.key,
                instantiation,
                &mut instance_vars,
            );
        }
    }

    for bound_id in [derivation.lower, derivation.upper] {
        let Some(bound) = machine.bounds.record(bound_id) else {
            return None;
        };
        roles.push(bound_role(bound_id, bound, &mut identities));
        for bound_derivation in bound.derivations() {
            roles.push(bound_derivation_role(
                bound_id,
                bound,
                bound_derivation,
                &mut identities,
            ));
            if let BoundDerivation::SchemeInstantiation(instantiation) = bound_derivation {
                mark_bound_instance_vars(
                    &machine.types,
                    bound,
                    instantiation.instantiation,
                    &mut instance_vars,
                );
            }
        }
    }

    let instance_use_values = instance_vars
        .values()
        .filter(|instances| instances.len() == 1)
        .filter_map(|instances| {
            let instance = *instances.iter().next().expect("one instance");
            machine
                .scheme_instantiations
                .get(instance.0 as usize)
                .map(|record| (record.use_value, instance))
        })
        .collect::<Vec<_>>();
    for (use_value, instance) in instance_use_values {
        instance_vars.entry(use_value).or_default().insert(instance);
    }

    let mut all_vars = constraint_vars(&machine.types, root);
    for &record_id in component {
        all_vars.extend(constraint_vars(
            &machine.types,
            &machine.constraint_records[record_id.0 as usize].key,
        ));
    }
    for bound_id in [derivation.lower, derivation.upper] {
        if let Some(bound) = machine.bounds.record(bound_id) {
            all_vars.insert(bound.owner());
            let mut scan = ClosureScan::new(&machine.types);
            match bound.endpoint() {
                BoundEndpoint::Lower(pos) => scan.pos(pos),
                BoundEndpoint::Upper(neg) => scan.neg(neg),
            }
            all_vars.extend(scan.vars);
        }
    }
    let (per_use, boundary): (Vec<_>, Vec<_>) = all_vars
        .into_iter()
        .partition(|var| instance_vars.get(var).is_some_and(|ids| ids.len() == 1));

    let component_keys = component
        .iter()
        .map(|id| &machine.constraint_records[id.0 as usize].key);
    let mut subtracts = collect_scheme_subtracts(&machine.types, root, component_keys)
        .into_iter()
        .collect::<FxHashSet<_>>();
    for bound_id in [derivation.lower, derivation.upper] {
        let Some(bound) = machine.bounds.record(bound_id) else {
            continue;
        };
        let mut scan = ClosureScan::new(&machine.types);
        match bound.endpoint() {
            BoundEndpoint::Lower(pos) => scan.pos(pos),
            BoundEndpoint::Upper(neg) => scan.neg(neg),
        }
        scan_constraint_weights(&mut scan, bound.weights());
        subtracts.extend(scan.subtracts);
    }
    alpha_view(
        &machine.types,
        root.lower,
        roles,
        per_use,
        boundary,
        subtracts.into_iter().collect(),
    )
}

fn alpha_view(
    types: &TypeArena,
    predicate: PosId,
    role_predicates: Vec<RolePredicate>,
    mut per_use: Vec<TypeVar>,
    mut boundary: Vec<TypeVar>,
    mut stack_quantifiers: Vec<SubtractId>,
) -> Option<SchemeAlphaView> {
    per_use.sort_by_key(|var| var.0);
    per_use.dedup();
    boundary.sort_by_key(|var| var.0);
    boundary.dedup();
    stack_quantifiers.sort_by_key(|id| id.0);
    stack_quantifiers.dedup();
    let scheme = Scheme {
        quantifiers: per_use,
        role_predicates,
        recursive_bounds: Vec::new(),
        stack_quantifiers,
        predicate,
    };
    let boundary = BoundaryInterface {
        binders: &boundary,
        bounds: &[],
    };
    // A live solver component is not a finalized interface: its shared boundary variables do not
    // yet own one frozen `BoundaryBound` apiece.  Characterization still gives those variables the
    // oracle's disjoint Boundary namespace.  MissingBoundaryBound is therefore expected here;
    // every other closure violation rejects the view instead of weakening alpha equality.
    let characterization = SchemeAlphaView::characterize_current_scheme(types, &scheme, boundary);
    if characterization
        .violations
        .iter()
        .all(|violation| matches!(violation, InterfaceViolation::MissingBoundaryBound { .. }))
    {
        return Some(characterization.view);
    }
    eprintln!(
        "global-alpha census strict-view violations: {:?}",
        characterization.violations
    );
    None
}

fn constraint_role(
    name: &str,
    constraint: &SubtypeConstraintKey,
    identities: &mut AlphaIdentityNames,
) -> RolePredicate {
    let mut inputs = vec![
        RolePredicateArg::Covariant(constraint.lower),
        RolePredicateArg::Contravariant(constraint.upper),
    ];
    let weight = weight_shape(&constraint.weights, identities, &mut inputs);
    RolePredicate {
        role: vec!["global_alpha_census".into(), name.into(), weight],
        inputs,
        associated: Vec::new(),
    }
}

fn bound_role(
    id: BoundRecordId,
    bound: &BoundRecord,
    identities: &mut AlphaIdentityNames,
) -> RolePredicate {
    let mut inputs = Vec::new();
    match bound.endpoint() {
        BoundEndpoint::Lower(pos) => inputs.push(RolePredicateArg::Covariant(pos)),
        BoundEndpoint::Upper(neg) => inputs.push(RolePredicateArg::Contravariant(neg)),
    }
    let weight = weight_shape(bound.weights(), identities, &mut inputs);
    RolePredicate {
        role: vec![
            "global_alpha_census_carrier".into(),
            identities.bound(id),
            format!("{:?}", bound.direction()),
            identities.type_var(bound.owner()),
            weight,
        ],
        inputs,
        associated: Vec::new(),
    }
}

fn bound_derivation_role(
    bound_id: BoundRecordId,
    bound: &BoundRecord,
    derivation: &BoundDerivation,
    identities: &mut AlphaIdentityNames,
) -> RolePredicate {
    let detail = match derivation {
        BoundDerivation::Constraint(id) => format!("constraint:{}", identities.constraint(*id)),
        BoundDerivation::Origin(id) => format!("origin:{}", identities.origin(*id)),
        BoundDerivation::ReplayEvidence(replay) => format!(
            "replay:{}:{}:{}:{}",
            replay_rule_name(replay.rule),
            identities.type_var(replay.pivot),
            identities.bound(replay.lower),
            identities.bound(replay.upper),
        ),
        BoundDerivation::Row(id) => format!("row:{}", identities.row(*id)),
        BoundDerivation::SchemeInstantiation(item) => format!(
            "inst:{}:{}:{:?}",
            identities.instantiation(item.instantiation),
            identities.witness(item.source_witness),
            item.path,
        ),
        BoundDerivation::IncompleteReplay => "incomplete".into(),
    };
    let inputs = match bound.endpoint() {
        BoundEndpoint::Lower(pos) => vec![RolePredicateArg::Covariant(pos)],
        BoundEndpoint::Upper(neg) => vec![RolePredicateArg::Contravariant(neg)],
    };
    RolePredicate {
        role: vec![
            "global_alpha_census_provenance".into(),
            identities.bound(bound_id),
            identities.type_var(bound.owner()),
            detail,
        ],
        inputs,
        associated: Vec::new(),
    }
}

fn replay_rule_name(rule: ReplayRule) -> &'static str {
    match rule {
        ReplayRule::LowerBoundAdded => "lower",
        ReplayRule::UpperBoundAdded => "upper",
    }
}

#[derive(Default)]
struct AlphaIdentityNames {
    type_vars: FxHashMap<TypeVar, usize>,
    subtracts: FxHashMap<SubtractId, usize>,
    bounds: FxHashMap<BoundRecordId, usize>,
    constraints: FxHashMap<ConstraintRecordId, usize>,
    origins: FxHashMap<OriginId, usize>,
    rows: FxHashMap<RowDerivationId, usize>,
    instantiations: FxHashMap<SchemeInstantiationId, usize>,
    witnesses: FxHashMap<GeneralizedSchemeWitnessId, usize>,
}

impl AlphaIdentityNames {
    fn type_var(&mut self, id: TypeVar) -> String {
        intern_name(&mut self.type_vars, id, "V")
    }
    fn subtract(&mut self, id: SubtractId) -> String {
        intern_name(&mut self.subtracts, id, "S")
    }
    fn bound(&mut self, id: BoundRecordId) -> String {
        intern_name(&mut self.bounds, id, "B")
    }
    fn constraint(&mut self, id: ConstraintRecordId) -> String {
        intern_name(&mut self.constraints, id, "C")
    }
    fn origin(&mut self, id: OriginId) -> String {
        intern_name(&mut self.origins, id, "O")
    }
    fn row(&mut self, id: RowDerivationId) -> String {
        intern_name(&mut self.rows, id, "R")
    }
    fn instantiation(&mut self, id: SchemeInstantiationId) -> String {
        intern_name(&mut self.instantiations, id, "I")
    }
    fn witness(&mut self, id: GeneralizedSchemeWitnessId) -> String {
        intern_name(&mut self.witnesses, id, "W")
    }
}

fn intern_name<K: Eq + std::hash::Hash + Copy>(
    names: &mut FxHashMap<K, usize>,
    id: K,
    prefix: &str,
) -> String {
    let next = names.len();
    let index = match names.entry(id) {
        Entry::Occupied(entry) => *entry.get(),
        Entry::Vacant(entry) => {
            entry.insert(next);
            next
        }
    };
    format!("{prefix}{index}")
}

fn weight_shape(
    weights: &ConstraintWeights,
    identities: &mut AlphaIdentityNames,
    inputs: &mut Vec<RolePredicateArg>,
) -> String {
    let left_entries = weights
        .left
        .entries()
        .iter()
        .map(|entry| {
            let family = entry
                .family
                .as_ref()
                .map(|family| subtractability_shape(family, inputs))
                .unwrap_or_else(|| "none".into());
            format!(
                "{}:{}:{}:{}",
                identities.subtract(entry.id),
                entry.leading_pops,
                family,
                entry.pushes,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let right_entries = weights
        .right
        .entries()
        .iter()
        .map(|entry| format!("{}:{}", identities.subtract(entry.id), entry.pops))
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "L[{}|{}]R[{}]",
        subtractability_shape(weights.left.filter_set(), inputs),
        left_entries,
        right_entries,
    )
}

fn subtractability_shape(item: &Subtractability, inputs: &mut Vec<RolePredicateArg>) -> String {
    match item {
        Subtractability::Empty => "empty".into(),
        Subtractability::All => "all".into(),
        Subtractability::AllExcept(path, args) => family_shape("all_except", path, args, inputs),
        Subtractability::AllExceptMany(families) => {
            many_family_shape("all_except_many", families, inputs)
        }
        Subtractability::Set(path, args) => family_shape("set", path, args, inputs),
        Subtractability::SetMany(families) => many_family_shape("set_many", families, inputs),
    }
}

fn family_shape(
    kind: &str,
    path: &[String],
    args: &[NeuId],
    inputs: &mut Vec<RolePredicateArg>,
) -> String {
    inputs.extend(args.iter().copied().map(RolePredicateArg::Invariant));
    format!("{kind}:{}:{}", path.join("::"), args.len())
}

fn many_family_shape(
    kind: &str,
    families: &[(Vec<String>, Vec<NeuId>)],
    inputs: &mut Vec<RolePredicateArg>,
) -> String {
    let parts = families
        .iter()
        .map(|(path, args)| family_shape("family", path, args, inputs))
        .collect::<Vec<_>>()
        .join(";");
    format!("{kind}:{parts}")
}

fn mark_constraint_instance_vars(
    types: &TypeArena,
    constraint: &SubtypeConstraintKey,
    instance: SchemeInstantiationId,
    out: &mut FxHashMap<TypeVar, FxHashSet<SchemeInstantiationId>>,
) {
    for var in constraint_vars(types, constraint) {
        out.entry(var).or_default().insert(instance);
    }
}

fn mark_bound_instance_vars(
    types: &TypeArena,
    bound: &BoundRecord,
    instance: SchemeInstantiationId,
    out: &mut FxHashMap<TypeVar, FxHashSet<SchemeInstantiationId>>,
) {
    out.entry(bound.owner()).or_default().insert(instance);
    let mut scan = ClosureScan::new(types);
    match bound.endpoint() {
        BoundEndpoint::Lower(pos) => scan.pos(pos),
        BoundEndpoint::Upper(neg) => scan.neg(neg),
    }
    for var in scan.vars {
        out.entry(var).or_default().insert(instance);
    }
}

fn constraint_vars(types: &TypeArena, key: &SubtypeConstraintKey) -> FxHashSet<TypeVar> {
    let mut scan = ClosureScan::new(types);
    scan_constraint(&mut scan, key);
    scan.vars.into_iter().collect()
}

fn collect_scheme_subtracts<'a>(
    types: &TypeArena,
    root: &SubtypeConstraintKey,
    constraints: impl Iterator<Item = &'a SubtypeConstraintKey>,
) -> Vec<SubtractId> {
    let mut scan = ClosureScan::new(types);
    scan_constraint(&mut scan, root);
    for constraint in constraints {
        scan_constraint(&mut scan, constraint);
    }
    scan.subtracts.into_iter().collect()
}

fn scan_constraint(scan: &mut ClosureScan<'_>, key: &SubtypeConstraintKey) {
    scan.pos(key.lower);
    scan.neg(key.upper);
    scan_constraint_weights(scan, &key.weights);
}

fn scan_constraint_weights(scan: &mut ClosureScan<'_>, weights: &ConstraintWeights) {
    scan_subtractability(scan, weights.left.filter_set());
    for entry in weights.left.entries() {
        scan.subtracts.insert(entry.id);
        if let Some(family) = &entry.family {
            scan_subtractability(scan, family);
        }
    }
    scan.subtracts
        .extend(weights.right.entries().iter().map(|entry| entry.id));
}

fn scan_subtractability(scan: &mut ClosureScan<'_>, item: &Subtractability) {
    match item {
        Subtractability::Empty | Subtractability::All => {}
        Subtractability::AllExcept(_, args) | Subtractability::Set(_, args) => {
            for arg in args {
                scan.neu(*arg);
            }
        }
        Subtractability::AllExceptMany(items) | Subtractability::SetMany(items) => {
            for (_, args) in items {
                for arg in args {
                    scan.neu(*arg);
                }
            }
        }
    }
}
