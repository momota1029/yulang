//! constraint / selection / SCC の間をつなぐ coordinator。
//!
//! constraint machine は型の上下界だけを伝播し、selection や SCC の意味は知らない。
//! `AnalysisSession` は constraint event を見て selection probe を起こし、名前解決や method selection が
//! 確定したら `poly` へ解決結果を書き戻しつつ SCC machine へ dependency を渡す。

use std::collections::VecDeque;

use poly::expr::{Arena as PolyArena, Def, DefId, RefId, SelectId, SelectResolution};
use poly::types::{Neg, NegId, Pos, PosId, Scheme, TypeVar};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::arena::Arena as InferArena;
use crate::casts::CastTable;
use crate::compact::{
    CompactCastApplication, CompactCastKey, CompactRoleArg, compact_reachable_role_constraints,
    compact_type_var, finalize_compact_type_to_neg_constraint,
    finalize_compact_type_to_pos_constraint, find_next_compact_cast, normalize_compact_casts,
};
use crate::constraints::{ConstraintEvent, ConstraintWeights, TypeLevel};
use crate::generalize::{
    GeneralizedCompactRoot, finalize_generalized_compact_root_with_ancestors,
    generalize_prepared_compact_root_with_roles,
};
use crate::instantiate::instantiate_scheme;
use crate::role_solve::{
    RoleResolution, RoleResolutionKey, coalesce_role_constraints, resolve_role_constraints,
};
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleConstraintTable, RoleImplTable,
};
use crate::scc::{SccEvent, SccInput, SccMachine};
use crate::uses::{RefUseTable, SelectionUseTable};

/// 推論中の複数 machine を束ねる session。
///
/// `poly` は最終 IR と解決結果を持つ。`infer` は型制約 machine を持つ。
/// `refs` / `selections` は use-site 型と parent、`scc` は def 間依存を持つ。
/// それぞれの責務を分けたまま、event queue で進行を同期する。
pub struct AnalysisSession {
    pub poly: PolyArena,
    pub infer: InferArena,
    pub refs: RefUseTable,
    pub selections: SelectionUseTable,
    pub roles: RoleConstraintTable,
    pub role_impls: RoleImplTable,
    pub casts: CastTable,
    pub scc: SccMachine,
    schemes: FxHashMap<DefId, GeneralizedCompactRoot>,
    scc_events: Vec<SccEvent>,
    work: VecDeque<AnalysisWork>,
}

impl AnalysisSession {
    pub fn new(poly: PolyArena) -> Self {
        Self {
            poly,
            infer: InferArena::new(),
            refs: RefUseTable::new(),
            selections: SelectionUseTable::new(),
            roles: RoleConstraintTable::new(),
            role_impls: RoleImplTable::new(),
            casts: CastTable::new(),
            scc: SccMachine::new(),
            schemes: FxHashMap::default(),
            scc_events: Vec::new(),
            work: VecDeque::new(),
        }
    }

    pub fn enqueue(&mut self, work: AnalysisWork) {
        self.work.push_back(work);
    }

    pub fn work(&self) -> &VecDeque<AnalysisWork> {
        &self.work
    }

    pub fn has_pending_work(&self) -> bool {
        !self.work.is_empty() || !self.infer.constraints().events().is_empty()
    }

    pub fn route_constraint_events(&mut self) {
        for event in self.infer.constraints_mut().take_events() {
            match event {
                ConstraintEvent::LowerBoundAdded { var, .. } => {
                    for select in self.selections.pending_for_lower_bound(var) {
                        self.enqueue(AnalysisWork::ProbeSelect(select));
                    }
                }
                ConstraintEvent::NominalCastNeeded {
                    lower,
                    upper,
                    source,
                    target,
                    weights,
                } => {
                    self.constrain_nominal_cast(lower, upper, &source, &target, weights);
                }
                ConstraintEvent::UpperBoundAdded { .. }
                | ConstraintEvent::SubtractFactAdded { .. } => {}
            }
        }
    }

    pub fn drain_work(&mut self) {
        while self.step() {}
    }

    pub fn step(&mut self) -> bool {
        self.route_constraint_events();
        let Some(work) = self.work.pop_front() else {
            return false;
        };
        self.apply_work(work);
        true
    }

    pub fn take_scc_events(&mut self) -> Vec<SccEvent> {
        self.route_scc_events();
        std::mem::take(&mut self.scc_events)
    }

    fn apply_work(&mut self, work: AnalysisWork) {
        match work {
            AnalysisWork::ResolveRef(_) | AnalysisWork::ProbeSelect(_) => {}
            AnalysisWork::ApplyRefResolution { ref_id, target } => {
                self.poly.resolve_ref(ref_id, target);
                if let Some(use_site) = self.refs.get(ref_id).copied() {
                    self.scc.use_resolved(SccInput::UseResolved {
                        parent: use_site.parent,
                        target,
                        use_value: use_site.value,
                    });
                }
            }
            AnalysisWork::ApplySelectionResolution { select_id, target } => {
                self.poly.resolve_select(select_id, target.resolution());
                let Some(use_site) = self.selections.get(select_id).copied() else {
                    return;
                };
                match target {
                    SelectionTarget::RecordField => {}
                    SelectionTarget::Method { def } => {
                        self.scc.use_resolved(SccInput::UseResolved {
                            parent: use_site.parent,
                            target: def,
                            use_value: use_site.method_value,
                        });
                    }
                    SelectionTarget::TypeclassMethod { member } => {
                        self.scc.use_resolved(SccInput::UseResolved {
                            parent: use_site.parent,
                            target: member,
                            use_value: use_site.method_value,
                        });
                    }
                }
            }
            AnalysisWork::Scc(input) => self.scc.apply(input),
        }
        self.route_scc_events();
    }

    fn route_scc_events(&mut self) {
        for event in self.scc.take_events() {
            match event {
                SccEvent::OpenUse {
                    target,
                    target_root,
                    use_value,
                } => {
                    self.constrain_open_use(target_root, use_value);
                    self.scc_events.push(SccEvent::OpenUse {
                        target,
                        target_root,
                        use_value,
                    });
                }
                SccEvent::QuantifyComponent { component, roots } => {
                    self.quantify_component(&component, &roots);
                    self.scc_events
                        .push(SccEvent::QuantifyComponent { component, roots });
                }
                SccEvent::InstantiateUse { target, use_value } => {
                    self.instantiate_use(target, use_value);
                    self.scc_events
                        .push(SccEvent::InstantiateUse { target, use_value });
                }
                other => self.scc_events.push(other),
            }
        }
    }

    fn constrain_open_use(&mut self, target_root: TypeVar, use_value: TypeVar) {
        let target_pos = self.infer.alloc_pos(Pos::Var(target_root));
        let use_neg = self.infer.alloc_neg(Neg::Var(use_value));
        self.infer.subtype(target_pos, use_neg);
    }

    fn quantify_component(&mut self, component: &[DefId], roots: &[TypeVar]) {
        let mut generalized = Vec::with_capacity(component.len());
        for (def, root) in component.iter().copied().zip(roots.iter().copied()) {
            let scheme = self.generalize_root_with_prepasses(def, root);
            generalized.push((def, scheme));
        }

        for (def, scheme) in &generalized {
            self.schemes.insert(*def, scheme.clone());
        }

        for (def, scheme) in generalized {
            let ancestors = self.scheme_ancestors(def);
            let ancestors = ancestors.iter().collect::<Vec<_>>();
            let finalized = finalize_generalized_compact_root_with_ancestors(
                &mut self.poly.typ,
                &scheme,
                &ancestors,
            );
            self.set_def_scheme(def, finalized.scheme);
        }
    }

    fn instantiate_use(&mut self, target: DefId, use_value: TypeVar) {
        let Some(scheme) = self.def_scheme(target).cloned() else {
            return;
        };
        let predicate = instantiate_scheme(
            &self.poly.typ,
            &mut self.infer,
            TypeLevel::secondary(),
            &scheme,
        );
        let use_upper = self.infer.alloc_neg(Neg::Var(use_value));
        self.infer.subtype(predicate, use_upper);
    }

    fn generalize_root_with_prepasses(
        &mut self,
        def: DefId,
        root: TypeVar,
    ) -> GeneralizedCompactRoot {
        let mut applied_casts = FxHashSet::<CompactCastKey>::default();
        let mut applied_roles = FxHashSet::<RoleResolutionKey>::default();
        let mut applied_role_demands = FxHashSet::default();
        let mut compact;
        loop {
            compact = compact_type_var(self.infer.constraints(), root);
            normalize_compact_casts(&mut compact, &applied_casts);
            if let Some(batch) = find_next_compact_cast(&compact, &self.casts, &applied_casts) {
                for application in &batch.applications {
                    self.constrain_compact_cast(application);
                }
                applied_casts.insert(batch.key);
                self.route_constraint_events();
                continue;
            }

            let roles = coalesce_role_constraints(compact_reachable_role_constraints(
                self.infer.constraints(),
                &compact,
                self.roles.for_owner(def),
            ));
            let resolutions = resolve_role_constraints(
                self.infer.constraints(),
                &compact,
                &roles,
                &self.role_impls,
                &applied_roles,
            );
            if !resolutions.is_empty() {
                for resolution in resolutions {
                    applied_roles.insert(resolution.key.clone());
                    self.collect_resolved_role_demands(&resolution, &mut applied_role_demands);
                    self.constrain_role_resolution(def, &resolution);
                }
                self.route_constraint_events();
                continue;
            }
            break;
        }

        let role_predicates = coalesce_role_constraints(compact_reachable_role_constraints(
            self.infer.constraints(),
            &compact,
            self.roles.for_owner(def),
        ))
        .into_iter()
        .filter(|role| !applied_role_demands.contains(role))
        .collect();

        generalize_prepared_compact_root_with_roles(
            self.infer.constraints(),
            TypeLevel::root(),
            compact,
            role_predicates,
            &FxHashSet::default(),
        )
    }

    fn collect_resolved_role_demands(
        &self,
        resolution: &RoleResolution,
        out: &mut FxHashSet<crate::compact::CompactRoleConstraint>,
    ) {
        out.insert(resolution.demand.clone());
        for prerequisite in &resolution.solved_prerequisites {
            self.collect_resolved_role_demands(prerequisite, out);
        }
    }

    fn constrain_role_resolution(&mut self, def: DefId, resolution: &RoleResolution) {
        for prerequisite in &resolution.solved_prerequisites {
            self.constrain_role_resolution(def, prerequisite);
        }
        for prerequisite in &resolution.residual_prerequisites {
            self.insert_residual_role_constraint(def, prerequisite);
        }
        for (demand, candidate) in resolution
            .demand
            .inputs
            .iter()
            .zip(&resolution.candidate.inputs)
        {
            self.constrain_role_arg_equal(demand, candidate);
        }
        for demand in &resolution.demand.associated {
            let Some(candidate) = resolution
                .candidate
                .associated
                .iter()
                .find(|candidate| candidate.name == demand.name)
            else {
                continue;
            };
            self.constrain_role_arg_equal(&demand.value, &candidate.value);
        }
    }

    fn insert_residual_role_constraint(
        &mut self,
        def: DefId,
        constraint: &crate::compact::CompactRoleConstraint,
    ) {
        let constraint = self.finalize_compact_role_constraint(constraint);
        if !self.roles.for_owner(def).contains(&constraint) {
            self.roles.insert(def, constraint);
        }
    }

    fn finalize_compact_role_constraint(
        &mut self,
        constraint: &crate::compact::CompactRoleConstraint,
    ) -> RoleConstraint {
        RoleConstraint {
            role: constraint.role.clone(),
            inputs: constraint
                .inputs
                .iter()
                .map(|arg| self.finalize_compact_role_arg(arg))
                .collect(),
            associated: constraint
                .associated
                .iter()
                .map(|associated| RoleAssociatedConstraint {
                    name: associated.name.clone(),
                    value: self.finalize_compact_role_arg(&associated.value),
                })
                .collect(),
        }
    }

    fn finalize_compact_role_arg(&mut self, arg: &CompactRoleArg) -> RoleConstraintArg {
        RoleConstraintArg {
            lower: finalize_compact_type_to_pos_constraint(
                self.infer.constraints_mut(),
                &arg.lower,
            ),
            upper: finalize_compact_type_to_neg_constraint(
                self.infer.constraints_mut(),
                &arg.upper,
            ),
        }
    }

    fn constrain_role_arg_equal(&mut self, demand: &CompactRoleArg, candidate: &CompactRoleArg) {
        let candidate_lower =
            finalize_compact_type_to_pos_constraint(self.infer.constraints_mut(), &candidate.lower);
        let demand_upper =
            finalize_compact_type_to_neg_constraint(self.infer.constraints_mut(), &demand.upper);
        self.infer.subtype(candidate_lower, demand_upper);

        let demand_lower =
            finalize_compact_type_to_pos_constraint(self.infer.constraints_mut(), &demand.lower);
        let candidate_upper =
            finalize_compact_type_to_neg_constraint(self.infer.constraints_mut(), &candidate.upper);
        self.infer.subtype(demand_lower, candidate_upper);
    }

    fn constrain_compact_cast(&mut self, application: &CompactCastApplication) {
        let lower = finalize_compact_type_to_pos_constraint(
            self.infer.constraints_mut(),
            &application.source,
        );
        let upper = finalize_compact_type_to_neg_constraint(
            self.infer.constraints_mut(),
            &application.target,
        );
        self.constrain_nominal_cast(
            lower,
            upper,
            &application.key.source,
            &application.key.target,
            ConstraintWeights::empty(),
        );
    }

    fn constrain_nominal_cast(
        &mut self,
        lower: PosId,
        upper: NegId,
        source: &[String],
        target: &[String],
        weights: crate::constraints::ConstraintWeights,
    ) {
        let candidates = self.casts.candidates(source, target).to_vec();
        if candidates.is_empty() {
            return;
        }
        for candidate in candidates {
            let predicate = instantiate_scheme(
                &self.poly.typ,
                &mut self.infer,
                TypeLevel::secondary(),
                &candidate.scheme,
            );
            let arg_eff = self.infer.alloc_pos(Pos::Bot);
            let ret_eff = self.infer.alloc_neg(Neg::Top);
            let expected_cast = self.infer.alloc_neg(Neg::Fun {
                arg: lower,
                arg_eff,
                ret_eff,
                ret: upper,
            });
            self.infer
                .weighted_subtype(predicate, weights.clone(), expected_cast);
        }
    }

    fn def_scheme(&self, def: DefId) -> Option<&Scheme> {
        let Some(Def::Let { scheme, .. }) = self.poly.defs.get(def) else {
            return None;
        };
        scheme.as_ref()
    }

    fn scheme_ancestors(&self, def: DefId) -> Vec<GeneralizedCompactRoot> {
        let parents = def_parent_map(&self.poly);
        let mut chain = Vec::new();
        let mut current = def;
        while let Some(parent) = parents.get(&current).copied() {
            chain.push(parent);
            current = parent;
        }
        chain.reverse();
        chain
            .into_iter()
            .filter_map(|ancestor| self.schemes.get(&ancestor).cloned())
            .collect()
    }

    fn set_def_scheme(&mut self, def: DefId, scheme: poly::types::Scheme) {
        let Some(Def::Let { scheme: target, .. }) = self.poly.defs.get_mut(def) else {
            return;
        };
        *target = Some(scheme);
    }
}

fn def_parent_map(poly: &PolyArena) -> FxHashMap<DefId, DefId> {
    let mut parents = FxHashMap::default();
    for (parent, def) in poly.defs.iter() {
        match def {
            Def::Mod { children, .. } | Def::Let { children, .. } => {
                for child in children {
                    parents.insert(*child, parent);
                }
            }
            Def::Arg => {}
        }
    }
    parents
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// `AnalysisSession` の work queue に積む作業。
///
/// `ResolveRef` / `ProbeSelect` は実際の解決器がまだ入る前の hook。
/// `Apply*Resolution` は解決結果が分かったあと、`poly` と SCC へ反映する段階。
/// `Scc` は lowering / resolver から SCC machine へ直接渡したい入力を queue に載せるための variant。
pub enum AnalysisWork {
    ResolveRef(RefId),
    ProbeSelect(SelectId),
    ApplyRefResolution {
        ref_id: RefId,
        target: DefId,
    },
    ApplySelectionResolution {
        select_id: SelectId,
        target: SelectionTarget,
    },
    Scc(SccInput),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// selection が何として解けたか。
///
/// `RecordField` は値の projection だけなので SCC edge を作らない。
/// `Method` / `TypeclassMethod` は hidden use なので、method def を parent def からの依存として SCC に渡す。
pub enum SelectionTarget {
    RecordField,
    Method { def: DefId },
    TypeclassMethod { member: DefId },
}

impl SelectionTarget {
    pub fn resolution(self) -> SelectResolution {
        match self {
            Self::RecordField => SelectResolution::RecordField,
            Self::Method { def } => SelectResolution::Method { def },
            Self::TypeclassMethod { member } => SelectResolution::TypeclassMethod { member },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints::{ConstraintWeight, ConstraintWeights};
    use crate::roles::{
        RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate,
    };
    use crate::uses::{RefUse, SelectionUse};
    use poly::expr::{Arena as PolyArena, Expr, Lit, Vis};
    use poly::types::{Neg, Neu, NeuId, Pos, Scheme, SubtractId, TypeVar};

    #[test]
    fn lower_bound_events_route_receiver_and_ref_payload_select_watchers() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let receiver_select = SelectId(0);
        let payload_select = SelectId(1);
        let watched = TypeVar(2);
        session.selections.watch_receiver(watched, receiver_select);
        session
            .selections
            .watch_ref_payload(watched, payload_select);

        let lower = session
            .infer
            .alloc_pos(Pos::Con(vec!["ref".into()], vec![]));
        let upper = session.infer.alloc_neg(Neg::Var(watched));
        session.infer.weighted_subtype(
            lower,
            ConstraintWeights {
                left: ConstraintWeight::from_ids([SubtractId(0)]),
                right: ConstraintWeight::empty(),
            },
            upper,
        );
        session.route_constraint_events();

        assert_eq!(
            session.work().iter().cloned().collect::<Vec<_>>(),
            vec![
                AnalysisWork::ProbeSelect(receiver_select),
                AnalysisWork::ProbeSelect(payload_select)
            ]
        );
    }

    #[test]
    fn nominal_con_mismatch_applies_registered_cast_scheme() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let source = vec!["int".to_string()];
        let target = vec!["user_id".to_string()];
        let result = TypeVar(0);
        let cast_arg = session
            .poly
            .typ
            .alloc_neg(Neg::Con(source.clone(), Vec::new()));
        let cast_arg_eff = session.poly.typ.alloc_neg(Neg::Bot);
        let cast_ret_eff = session.poly.typ.alloc_pos(Pos::Bot);
        let cast_ret = session.poly.typ.alloc_pos(Pos::Var(result));
        let cast_predicate = session.poly.typ.alloc_pos(Pos::Fun {
            arg: cast_arg,
            arg_eff: cast_arg_eff,
            ret_eff: cast_ret_eff,
            ret: cast_ret,
        });
        session.casts.insert(
            source.clone(),
            target.clone(),
            Scheme {
                quantifiers: vec![result],
                role_predicates: Vec::new(),
                predicate: cast_predicate,
                subtracts: Vec::new(),
            },
        );

        let lower = session
            .infer
            .alloc_pos(Pos::Con(source.clone(), Vec::new()));
        let upper = session
            .infer
            .alloc_neg(Neg::Con(target.clone(), Vec::new()));
        session.infer.subtype(lower, upper);
        session.route_constraint_events();

        let events = session.infer.constraints().events();
        assert!(events.iter().any(|event| {
            matches!(
                event,
                ConstraintEvent::UpperBoundAdded { bound, .. }
                    if matches!(session.infer.constraints().types().neg(*bound), Neg::Con(path, _) if path == &target)
            )
        }));
    }

    #[test]
    fn ref_resolution_routes_parent_and_use_value_to_scc_machine() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let reference = session.poly.add_ref();
        let parent = DefId(1);
        let target = DefId(2);
        session.refs.insert(
            reference,
            RefUse {
                parent,
                value: TypeVar(3),
            },
        );

        session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: reference,
            target,
        });
        session.drain_work();

        assert_eq!(session.poly.ref_target(reference), Some(target));
        assert_eq!(
            session.take_scc_events(),
            vec![SccEvent::ComponentEdgeAdded {
                from: vec![parent],
                to: vec![target]
            }]
        );
    }

    #[test]
    fn method_selection_resolution_routes_hidden_method_use_to_scc_machine() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let receiver = session.poly.add_expr(Expr::Lit(Lit::Unit));
        let select = session.poly.add_select("display");
        session.poly.add_expr(Expr::Select(receiver, select));
        let parent = DefId(1);
        let method = DefId(2);
        session.selections.insert(
            select,
            SelectionUse {
                parent,
                receiver_value: TypeVar(3),
                method_value: TypeVar(4),
            },
        );

        session.enqueue(AnalysisWork::ApplySelectionResolution {
            select_id: select,
            target: SelectionTarget::Method { def: method },
        });
        session.drain_work();

        assert_eq!(
            session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
        assert_eq!(
            session.take_scc_events(),
            vec![SccEvent::ComponentEdgeAdded {
                from: vec![parent],
                to: vec![method]
            }]
        );
    }

    #[test]
    fn open_scc_use_adds_target_to_use_constraint() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let a = DefId(1);
        let b = DefId(2);
        let a_root = TypeVar(10);
        let b_root = TypeVar(20);
        let a_to_b_use = TypeVar(12);
        let b_to_a_use = TypeVar(21);
        let a_to_b_ref = session.poly.add_ref();
        let b_to_a_ref = session.poly.add_ref();
        session.refs.insert(
            a_to_b_ref,
            RefUse {
                parent: a,
                value: a_to_b_use,
            },
        );
        session.refs.insert(
            b_to_a_ref,
            RefUse {
                parent: b,
                value: b_to_a_use,
            },
        );

        session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
            def: a,
            root: a_root,
        }));
        session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
            def: b,
            root: b_root,
        }));
        session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: a_to_b_ref,
            target: b,
        });
        session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: b_to_a_ref,
            target: a,
        });
        session.drain_work();

        let b_root_pos = session.infer.alloc_pos(Pos::Var(b_root));
        let a_to_b_neg = session.infer.alloc_neg(Neg::Var(a_to_b_use));
        let bounds = session.infer.constraints().bounds();
        let use_bounds = bounds.of(a_to_b_use).expect("use bounds");
        assert!(use_bounds.lowers().iter().any(|bound| bound.pos == b_root_pos
            && bound.weights == ConstraintWeights::empty()));
        let target_bounds = bounds.of(b_root).expect("target root bounds");
        assert!(target_bounds.uppers().iter().any(|bound| bound.neg == a_to_b_neg
            && bound.weights == ConstraintWeights::empty()));

        assert!(session.take_scc_events().iter().any(|event| {
            matches!(
                event,
                SccEvent::OpenUse {
                    target,
                    target_root,
                    use_value,
                } if *target == b && *target_root == b_root && *use_value == a_to_b_use
            )
        }));
    }

    #[test]
    fn quantify_component_writes_scheme_to_poly_def() {
        let mut poly = PolyArena::new();
        let def = poly.defs.fresh();
        poly.defs.set(
            def,
            Def::Let {
                vis: Vis::My,
                scheme: None,
                body: None,
                children: Vec::new(),
            },
        );
        let mut session = AnalysisSession::new(poly);
        let root = session.infer.fresh_type_var();

        session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef { def, root }));
        session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
        session.drain_work();

        let Some(Def::Let {
            scheme: Some(scheme),
            ..
        }) = session.poly.defs.get(def)
        else {
            panic!("ready SCC should write a scheme to Def::Let");
        };
        assert_eq!(scheme.quantifiers, Vec::new());
        assert!(session.schemes.contains_key(&def));
        assert!(session.take_scc_events().iter().any(|event| {
            matches!(
                event,
                SccEvent::QuantifyComponent {
                    component,
                    roots,
                } if component == &vec![def] && roots == &vec![root]
            )
        }));
    }

    #[test]
    fn instantiate_use_freshens_quantifiers_at_secondary_level() {
        let mut poly = PolyArena::new();
        let def = poly.defs.fresh();
        let quantified = TypeVar(42);
        let predicate = poly.typ.alloc_pos(Pos::Var(quantified));
        poly.defs.set(
            def,
            Def::Let {
                vis: Vis::My,
                scheme: Some(Scheme {
                    quantifiers: vec![quantified],
                    role_predicates: Vec::new(),
                    predicate,
                    subtracts: Vec::new(),
                }),
                body: None,
                children: Vec::new(),
            },
        );
        let mut session = AnalysisSession::new(poly);
        let use_value = TypeVar(10);
        session
            .infer
            .constraints_mut()
            .register_type_var(use_value, TypeLevel::root());

        session.instantiate_use(def, use_value);

        let use_bounds = session
            .infer
            .constraints()
            .bounds()
            .of(use_value)
            .expect("use value should receive instantiated lower bound");
        let fresh = use_bounds
            .lowers()
            .iter()
            .find_map(
                |bound| match session.infer.constraints().types().pos(bound.pos) {
                    Pos::Var(var) if *var != quantified => Some(*var),
                    _ => None,
                },
            )
            .expect("scheme quantifier should be freshened");
        assert_eq!(
            session.infer.constraints().level_of(fresh),
            TypeLevel::root()
        );
    }

    #[test]
    fn compact_cast_prepass_normalizes_bidirectional_constructor_pair_once() {
        let source = vec!["source".to_string()];
        let target = vec!["target".to_string()];
        let mut session = AnalysisSession::new(PolyArena::new());
        let source_to_target =
            monomorphic_cast_scheme(&mut session.poly.typ, source.clone(), target.clone());
        let target_to_source =
            monomorphic_cast_scheme(&mut session.poly.typ, target.clone(), source.clone());
        session
            .casts
            .insert(source.clone(), target.clone(), source_to_target);
        session
            .casts
            .insert(target.clone(), source.clone(), target_to_source);

        let root = session.infer.fresh_type_var();
        let source_lower = session
            .infer
            .alloc_pos(Pos::Con(source.clone(), Vec::new()));
        let target_lower = session
            .infer
            .alloc_pos(Pos::Con(target.clone(), Vec::new()));
        let root_upper = session.infer.alloc_neg(Neg::Var(root));
        session.infer.subtype(source_lower, root_upper);
        session.infer.subtype(target_lower, root_upper);

        let generalized = session.generalize_root_with_prepasses(DefId(0), root);

        assert_eq!(generalized.compact.root.cons.len(), 1);
        assert_eq!(generalized.compact.root.cons[0].path, target);
    }

    #[test]
    fn compact_cast_prepass_adds_cast_scheme_payload_constraints() {
        let source = vec!["source".to_string()];
        let target = vec!["target".to_string()];
        let mut session = AnalysisSession::new(PolyArena::new());
        let cast = generic_unary_cast_scheme(&mut session.poly.typ, source.clone(), target.clone());
        session.casts.insert(source.clone(), target.clone(), cast);

        let root = session.infer.fresh_type_var();
        let source_payload = session.infer.fresh_type_var();
        let target_payload = session.infer.fresh_type_var();
        let source_neu = infer_bounds_neu(&mut session.infer, source_payload);
        let target_neu = infer_bounds_neu(&mut session.infer, target_payload);
        let source_lower = session
            .infer
            .alloc_pos(Pos::Con(source.clone(), vec![source_neu]));
        let target_lower = session
            .infer
            .alloc_pos(Pos::Con(target.clone(), vec![target_neu]));
        let root_upper = session.infer.alloc_neg(Neg::Var(root));
        session.infer.subtype(source_lower, root_upper);
        session.infer.subtype(target_lower, root_upper);

        let generalized = session.generalize_root_with_prepasses(DefId(0), root);

        assert_eq!(generalized.compact.root.cons.len(), 1);
        assert_eq!(generalized.compact.root.cons[0].path, target);
        assert!(
            session
                .infer
                .constraints()
                .bounds()
                .of(source_payload)
                .is_some()
        );
        assert!(
            session
                .infer
                .constraints()
                .bounds()
                .of(target_payload)
                .is_some()
        );
    }

    #[test]
    fn role_prepass_resolves_concrete_impl_and_constrains_associated_type() {
        let role = vec!["Add".to_string()];
        let int_path = vec!["int".to_string()];
        let owner = DefId(0);
        let mut session = AnalysisSession::new(PolyArena::new());
        let root = session.infer.fresh_type_var();
        let output = session.infer.fresh_type_var();
        let int_arg = role_exact_arg(&mut session.infer, int_path.clone());
        session.roles.insert(
            owner,
            RoleConstraint {
                role: role.clone(),
                inputs: vec![
                    role_exact_arg(&mut session.infer, int_path.clone()),
                    role_exact_arg(&mut session.infer, int_path.clone()),
                ],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".into(),
                    value: role_var_arg(&mut session.infer, output),
                }],
            },
        );
        session.role_impls.insert(RoleImplCandidate {
            role,
            inputs: vec![int_arg.clone(), int_arg],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_exact_arg(&mut session.infer, int_path.clone()),
            }],
            prerequisites: Vec::new(),
        });

        let root_lower = session.infer.alloc_pos(Pos::Var(output));
        let root_upper = session.infer.alloc_neg(Neg::Var(root));
        session.infer.subtype(root_lower, root_upper);

        session.generalize_root_with_prepasses(owner, root);

        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(output)
            .expect("role associated output should receive impl bounds");
        assert!(bounds.lowers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().pos(bound.pos),
                Pos::Con(path, _) if path == &int_path
            )
        }));
        assert!(bounds.uppers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().neg(bound.neg),
                Neg::Con(path, _) if path == &int_path
            )
        }));
    }

    #[test]
    fn role_prepass_coalesces_shared_input_roles_before_resolution() {
        let role = vec!["Add".to_string()];
        let int_path = vec!["int".to_string()];
        let owner = DefId(0);
        let mut session = AnalysisSession::new(PolyArena::new());
        let root = session.infer.fresh_type_var();
        let shared = session.infer.fresh_type_var();
        let first_output = session.infer.fresh_type_var();
        let second_output = session.infer.fresh_type_var();
        let int_arg = role_exact_arg(&mut session.infer, int_path.clone());
        session.roles.insert(
            owner,
            RoleConstraint {
                role: role.clone(),
                inputs: vec![
                    role_var_arg(&mut session.infer, shared),
                    role_exact_arg(&mut session.infer, int_path.clone()),
                ],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".into(),
                    value: role_var_arg(&mut session.infer, first_output),
                }],
            },
        );
        session.roles.insert(
            owner,
            RoleConstraint {
                role: role.clone(),
                inputs: vec![
                    role_var_arg(&mut session.infer, shared),
                    role_exact_arg(&mut session.infer, int_path.clone()),
                ],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".into(),
                    value: role_var_arg(&mut session.infer, second_output),
                }],
            },
        );
        session.role_impls.insert(RoleImplCandidate {
            role,
            inputs: vec![int_arg.clone(), int_arg],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_exact_arg(&mut session.infer, int_path.clone()),
            }],
            prerequisites: Vec::new(),
        });

        let shared_lower = session
            .infer
            .alloc_pos(Pos::Con(int_path.clone(), Vec::new()));
        let shared_upper = session.infer.alloc_neg(Neg::Var(shared));
        session.infer.subtype(shared_lower, shared_upper);
        let root_lower = session.infer.alloc_pos(Pos::Var(first_output));
        let root_upper = session.infer.alloc_neg(Neg::Var(root));
        session.infer.subtype(root_lower, root_upper);

        session.generalize_root_with_prepasses(owner, root);

        assert_var_has_exact_bound(&session, first_output, &int_path);
        assert_var_has_exact_bound(&session, second_output, &int_path);
    }

    #[test]
    fn role_prepass_does_not_resolve_left_concrete_when_main_var_is_negative() {
        let role = vec!["Add".to_string()];
        let int_path = vec!["int".to_string()];
        let owner = DefId(0);
        let mut session = AnalysisSession::new(PolyArena::new());
        let root = session.infer.fresh_type_var();
        let arg = session.infer.fresh_type_var();
        let output = session.infer.fresh_type_var();
        let int_arg = role_exact_arg(&mut session.infer, int_path.clone());
        session.roles.insert(
            owner,
            RoleConstraint {
                role: role.clone(),
                inputs: vec![
                    role_exact_arg(&mut session.infer, int_path.clone()),
                    role_left_concrete_var_arg(&mut session.infer, int_path.clone(), arg),
                ],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".into(),
                    value: role_var_arg(&mut session.infer, output),
                }],
            },
        );
        session.role_impls.insert(RoleImplCandidate {
            role,
            inputs: vec![int_arg.clone(), int_arg],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_exact_arg(&mut session.infer, int_path.clone()),
            }],
            prerequisites: Vec::new(),
        });

        let fun_arg = session.infer.alloc_neg(Neg::Var(arg));
        let fun_arg_eff = session.infer.alloc_neg(Neg::Bot);
        let fun_ret_eff = session.infer.alloc_pos(Pos::Bot);
        let fun_ret = session.infer.alloc_pos(Pos::Var(output));
        let fun = session.infer.alloc_pos(Pos::Fun {
            arg: fun_arg,
            arg_eff: fun_arg_eff,
            ret_eff: fun_ret_eff,
            ret: fun_ret,
        });
        let root_upper = session.infer.alloc_neg(Neg::Var(root));
        session.infer.subtype(fun, root_upper);

        session.generalize_root_with_prepasses(owner, root);

        assert_var_lacks_exact_bound(&session, output, &int_path);
    }

    #[test]
    fn role_prepass_selects_parent_and_enqueues_concrete_prerequisite() {
        let wrap_role = vec!["Wrap".to_string()];
        let ready_role = vec!["Ready".to_string()];
        let box_path = vec!["box".to_string()];
        let int_path = vec!["int".to_string()];
        let unit_path = vec!["unit".to_string()];
        let owner = DefId(0);
        let mut session = AnalysisSession::new(PolyArena::new());
        let root = session.infer.fresh_type_var();
        let output = session.infer.fresh_type_var();
        let item = session.infer.fresh_type_var();
        let ready_output = session.infer.fresh_type_var();

        session.roles.insert(
            owner,
            RoleConstraint {
                role: wrap_role.clone(),
                inputs: vec![role_unary_con_exact_arg(
                    &mut session.infer,
                    box_path.clone(),
                    int_path.clone(),
                )],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".into(),
                    value: role_var_arg(&mut session.infer, output),
                }],
            },
        );
        session.role_impls.insert(RoleImplCandidate {
            role: wrap_role,
            inputs: vec![role_unary_con_var_arg(
                &mut session.infer,
                box_path.clone(),
                item,
            )],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_var_arg(&mut session.infer, ready_output),
            }],
            prerequisites: vec![RoleConstraint {
                role: ready_role.clone(),
                inputs: vec![role_var_arg(&mut session.infer, item)],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".into(),
                    value: role_var_arg(&mut session.infer, ready_output),
                }],
            }],
        });
        session.role_impls.insert(RoleImplCandidate {
            role: ready_role.clone(),
            inputs: vec![role_exact_arg(&mut session.infer, int_path.clone())],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_exact_arg(&mut session.infer, unit_path.clone()),
            }],
            prerequisites: Vec::new(),
        });

        let root_lower = session.infer.alloc_pos(Pos::Var(output));
        let root_upper = session.infer.alloc_neg(Neg::Var(root));
        session.infer.subtype(root_lower, root_upper);

        let generalized = session.generalize_root_with_prepasses(owner, root);

        assert_var_has_exact_bound(&session, output, &unit_path);
        assert!(generalized.role_predicates.is_empty());
        assert_concrete_role_residual_missing(&session, owner, &ready_role, &int_path);
    }

    #[test]
    fn role_prepass_selects_parent_even_when_prerequisite_is_missing() {
        let wrap_role = vec!["Wrap".to_string()];
        let ready_role = vec!["Ready".to_string()];
        let box_path = vec!["box".to_string()];
        let int_path = vec!["int".to_string()];
        let owner = DefId(0);
        let mut session = AnalysisSession::new(PolyArena::new());
        let root = session.infer.fresh_type_var();
        let output = session.infer.fresh_type_var();
        let item = session.infer.fresh_type_var();

        session.roles.insert(
            owner,
            RoleConstraint {
                role: wrap_role.clone(),
                inputs: vec![role_unary_con_exact_arg(
                    &mut session.infer,
                    box_path.clone(),
                    int_path.clone(),
                )],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".into(),
                    value: role_var_arg(&mut session.infer, output),
                }],
            },
        );
        session.role_impls.insert(RoleImplCandidate {
            role: wrap_role,
            inputs: vec![role_unary_con_var_arg(&mut session.infer, box_path, item)],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_var_arg(&mut session.infer, item),
            }],
            prerequisites: vec![RoleConstraint {
                role: ready_role.clone(),
                inputs: vec![role_var_arg(&mut session.infer, item)],
                associated: Vec::new(),
            }],
        });

        let root_lower = session.infer.alloc_pos(Pos::Var(output));
        let root_upper = session.infer.alloc_neg(Neg::Var(root));
        session.infer.subtype(root_lower, root_upper);

        let generalized = session.generalize_root_with_prepasses(owner, root);

        assert_var_has_exact_bound(&session, output, &int_path);
        assert!(
            generalized
                .role_predicates
                .iter()
                .any(|predicate| predicate.role == ready_role)
        );
        assert_concrete_role_residual_exists(&session, owner, &ready_role, &int_path);
    }

    #[test]
    fn role_prepass_selects_parent_and_keeps_free_prerequisite_residual() {
        let wrap_role = vec!["Wrap".to_string()];
        let ready_role = vec!["Ready".to_string()];
        let box_path = vec!["box".to_string()];
        let owner = DefId(0);
        let mut session = AnalysisSession::new(PolyArena::new());
        let root = session.infer.fresh_type_var();
        let payload = session.infer.fresh_type_var();
        let output = session.infer.fresh_type_var();
        let item = session.infer.fresh_type_var();

        session.roles.insert(
            owner,
            RoleConstraint {
                role: wrap_role.clone(),
                inputs: vec![role_unary_con_var_arg(
                    &mut session.infer,
                    box_path.clone(),
                    payload,
                )],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".into(),
                    value: role_var_arg(&mut session.infer, output),
                }],
            },
        );
        session.role_impls.insert(RoleImplCandidate {
            role: wrap_role,
            inputs: vec![role_unary_con_var_arg(&mut session.infer, box_path, item)],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_var_arg(&mut session.infer, item),
            }],
            prerequisites: vec![RoleConstraint {
                role: ready_role.clone(),
                inputs: vec![role_var_arg(&mut session.infer, item)],
                associated: Vec::new(),
            }],
        });

        let root_lower = session.infer.alloc_pos(Pos::Var(output));
        let root_upper = session.infer.alloc_neg(Neg::Var(root));
        session.infer.subtype(root_lower, root_upper);

        let generalized = session.generalize_root_with_prepasses(owner, root);

        let residuals = session
            .roles
            .for_owner(owner)
            .iter()
            .filter(|constraint| constraint.role == ready_role)
            .collect::<Vec<_>>();
        assert_eq!(residuals.len(), 1);
        assert!(matches!(
            session
                .infer
                .constraints()
                .types()
                .pos(residuals[0].inputs[0].lower),
            Pos::Var(var) if *var == payload
        ));
        assert!(matches!(
            session
                .infer
                .constraints()
                .types()
                .neg(residuals[0].inputs[0].upper),
            Neg::Var(var) if *var == payload
        ));
        assert!(
            generalized
                .role_predicates
                .iter()
                .any(|predicate| predicate.role == ready_role)
        );
    }

    fn monomorphic_cast_scheme(
        types: &mut poly::types::TypeArena,
        source: Vec<String>,
        target: Vec<String>,
    ) -> Scheme {
        let arg = types.alloc_neg(Neg::Con(source, Vec::new()));
        let arg_eff = types.alloc_neg(Neg::Bot);
        let ret_eff = types.alloc_pos(Pos::Bot);
        let ret = types.alloc_pos(Pos::Con(target, Vec::new()));
        let predicate = types.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        });
        Scheme {
            quantifiers: Vec::new(),
            role_predicates: Vec::new(),
            predicate,
            subtracts: Vec::new(),
        }
    }

    fn generic_unary_cast_scheme(
        types: &mut poly::types::TypeArena,
        source: Vec<String>,
        target: Vec<String>,
    ) -> Scheme {
        let quantified = TypeVar(42);
        let arg_item = poly_bounds_neu(types, quantified);
        let ret_item = poly_bounds_neu(types, quantified);
        let arg = types.alloc_neg(Neg::Con(source, vec![arg_item]));
        let arg_eff = types.alloc_neg(Neg::Bot);
        let ret_eff = types.alloc_pos(Pos::Bot);
        let ret = types.alloc_pos(Pos::Con(target, vec![ret_item]));
        let predicate = types.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        });
        Scheme {
            quantifiers: vec![quantified],
            role_predicates: Vec::new(),
            predicate,
            subtracts: Vec::new(),
        }
    }

    fn poly_bounds_neu(types: &mut poly::types::TypeArena, var: TypeVar) -> NeuId {
        let lower = types.alloc_pos(Pos::Var(var));
        let upper = types.alloc_neg(Neg::Var(var));
        types.alloc_neu(Neu::Bounds(lower, var, upper))
    }

    fn infer_bounds_neu(infer: &mut crate::arena::Arena, var: TypeVar) -> NeuId {
        let lower = infer.alloc_pos(Pos::Var(var));
        let upper = infer.alloc_neg(Neg::Var(var));
        infer.alloc_neu(Neu::Bounds(lower, var, upper))
    }

    fn role_var_arg(infer: &mut crate::arena::Arena, var: TypeVar) -> RoleConstraintArg {
        RoleConstraintArg {
            lower: infer.alloc_pos(Pos::Var(var)),
            upper: infer.alloc_neg(Neg::Var(var)),
        }
    }

    fn role_exact_arg(infer: &mut crate::arena::Arena, path: Vec<String>) -> RoleConstraintArg {
        RoleConstraintArg {
            lower: infer.alloc_pos(Pos::Con(path.clone(), Vec::new())),
            upper: infer.alloc_neg(Neg::Con(path, Vec::new())),
        }
    }

    fn role_unary_con_var_arg(
        infer: &mut crate::arena::Arena,
        path: Vec<String>,
        item: TypeVar,
    ) -> RoleConstraintArg {
        let lower = infer.alloc_pos(Pos::Var(item));
        let upper = infer.alloc_neg(Neg::Var(item));
        let item = infer.alloc_neu(Neu::Bounds(lower, item, upper));
        RoleConstraintArg {
            lower: infer.alloc_pos(Pos::Con(path.clone(), vec![item])),
            upper: infer.alloc_neg(Neg::Con(path, vec![item])),
        }
    }

    fn role_unary_con_exact_arg(
        infer: &mut crate::arena::Arena,
        path: Vec<String>,
        item_path: Vec<String>,
    ) -> RoleConstraintArg {
        let item_var = infer.fresh_type_var();
        let item_lower = infer.alloc_pos(Pos::Con(item_path.clone(), Vec::new()));
        let item_upper = infer.alloc_neg(Neg::Con(item_path, Vec::new()));
        let item = infer.alloc_neu(Neu::Bounds(item_lower, item_var, item_upper));
        RoleConstraintArg {
            lower: infer.alloc_pos(Pos::Con(path.clone(), vec![item])),
            upper: infer.alloc_neg(Neg::Con(path, vec![item])),
        }
    }

    fn role_left_concrete_var_arg(
        infer: &mut crate::arena::Arena,
        path: Vec<String>,
        var: TypeVar,
    ) -> RoleConstraintArg {
        let con = infer.alloc_pos(Pos::Con(path, Vec::new()));
        let var_pos = infer.alloc_pos(Pos::Var(var));
        RoleConstraintArg {
            lower: infer.alloc_pos(Pos::Union(con, var_pos)),
            upper: infer.alloc_neg(Neg::Var(var)),
        }
    }

    fn assert_var_has_exact_bound(session: &AnalysisSession, var: TypeVar, path: &[String]) {
        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(var)
            .expect("role output should receive impl bounds");
        assert!(bounds.lowers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().pos(bound.pos),
                Pos::Con(bound_path, _) if bound_path == path
            )
        }));
        assert!(bounds.uppers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().neg(bound.neg),
                Neg::Con(bound_path, _) if bound_path == path
            )
        }));
    }

    fn assert_var_lacks_exact_bound(session: &AnalysisSession, var: TypeVar, path: &[String]) {
        let Some(bounds) = session.infer.constraints().bounds().of(var) else {
            return;
        };
        assert!(!bounds.lowers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().pos(bound.pos),
                Pos::Con(bound_path, _) if bound_path == path
            )
        }));
        assert!(!bounds.uppers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().neg(bound.neg),
                Neg::Con(bound_path, _) if bound_path == path
            )
        }));
    }

    fn assert_concrete_role_residual_exists(
        session: &AnalysisSession,
        owner: DefId,
        role: &[String],
        path: &[String],
    ) {
        assert!(
            session.roles.for_owner(owner).iter().any(|constraint| {
                constraint.role == role
                    && constraint.inputs.iter().any(|input| {
                        matches!(
                            session.infer.constraints().types().pos(input.lower),
                            Pos::Con(bound_path, _) if bound_path == path
                        ) && matches!(
                            session.infer.constraints().types().neg(input.upper),
                            Neg::Con(bound_path, _) if bound_path == path
                        )
                    })
            }),
            "expected concrete residual role demand"
        );
    }

    fn assert_concrete_role_residual_missing(
        session: &AnalysisSession,
        owner: DefId,
        role: &[String],
        path: &[String],
    ) {
        assert!(
            !session.roles.for_owner(owner).iter().any(|constraint| {
                constraint.role == role
                    && constraint.inputs.iter().any(|input| {
                        matches!(
                            session.infer.constraints().types().pos(input.lower),
                            Pos::Con(bound_path, _) if bound_path == path
                        ) && matches!(
                            session.infer.constraints().types().neg(input.upper),
                            Neg::Con(bound_path, _) if bound_path == path
                        )
                    })
            }),
            "expected concrete residual role demand to be solved"
        );
    }
}
