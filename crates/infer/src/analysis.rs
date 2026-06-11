//! constraint / selection / SCC の間をつなぐ coordinator。
//!
//! constraint machine は型の上下界だけを伝播し、selection や SCC の意味は知らない。
//! `AnalysisSession` は constraint event を見て selection probe を起こし、名前解決や method selection が
//! 確定したら `poly` へ解決結果を書き戻しつつ SCC machine へ dependency を渡す。

use std::collections::VecDeque;

use poly::expr::{Arena as PolyArena, Def, DefId, RefId, SelectId, SelectResolution};
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RolePredicate, Scheme, Subtractability,
    TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::arena::Arena as InferArena;
use crate::casts::CastTable;
use crate::compact::{
    CompactBounds, CompactCastApplication, CompactCastKey, CompactRoleArg, CompactRoleConstraint,
    CompactType, compact_reachable_role_constraints, compact_role_constraint, compact_type_var,
    finalize_compact_type_to_neg_constraint, finalize_compact_type_to_pos_constraint,
    find_next_compact_cast, normalize_compact_casts,
};
use crate::constraints::{ConstraintEvent, ConstraintWeights, TypeLevel};
use crate::generalize::{
    GeneralizedCompactRoot, finalize_generalized_compact_root_with_ancestors,
    generalize_prepared_compact_root_with_roles,
};
use crate::instantiate::{instantiate_scheme, instantiate_scheme_with_roles};
use crate::methods::{
    CompanionMethodTable, EffectMethodCandidate, EffectMethodTable, RoleMethodTable,
    TypeMethodTable,
};
use crate::role_solve::{
    RoleResolution, RoleResolutionKey, coalesce_role_constraints, resolve_role_constraints,
    resolve_role_constraints_with_method_taint,
};
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleConstraintTable, RoleImplTable,
};
use crate::scc::{SccEvent, SccInput, SccMachine};
use crate::uses::{RefUseTable, SelectionUse, SelectionUseTable};

type MethodTaintIndex = FxHashMap<TypeVar, Vec<SelectId>>;

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
    pub methods: TypeMethodTable,
    pub effect_methods: EffectMethodTable,
    pub role_methods: RoleMethodTable,
    pub local_methods: CompanionMethodTable,
    pub scc: SccMachine,
    role_impl_members: FxHashMap<DefId, DefId>,
    role_impl_member_sets: FxHashMap<DefId, Vec<DefId>>,
    applied_method_role_resolutions: FxHashSet<RoleResolutionKey>,
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
            methods: TypeMethodTable::new(),
            effect_methods: EffectMethodTable::new(),
            role_methods: RoleMethodTable::new(),
            local_methods: CompanionMethodTable::new(),
            scc: SccMachine::new(),
            role_impl_members: FxHashMap::default(),
            role_impl_member_sets: FxHashMap::default(),
            applied_method_role_resolutions: FxHashSet::default(),
            schemes: FxHashMap::default(),
            scc_events: Vec::new(),
            work: VecDeque::new(),
        }
    }

    pub fn enqueue(&mut self, work: AnalysisWork) {
        self.work.push_back(work);
    }

    pub fn register_selection_use(&mut self, select_id: SelectId, use_site: SelectionUse) {
        self.selections.insert(select_id, use_site);
        self.enqueue(AnalysisWork::Scc(SccInput::MethodDependencyAdded {
            parent: use_site.parent,
        }));
        self.enqueue(AnalysisWork::ProbeSelect(select_id));
    }

    pub fn register_value_type_method(
        &mut self,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.methods.insert_value(receiver, method, def);
        self.enqueue_unresolved_selection_probes();
    }

    pub fn register_ref_type_method(
        &mut self,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.methods.insert_ref(receiver, method, def);
        self.enqueue_unresolved_selection_probes();
    }

    pub fn register_effect_method(
        &mut self,
        effect: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.effect_methods.insert(effect, method, def);
        self.enqueue_unresolved_selection_probes();
    }

    pub fn register_role_method(
        &mut self,
        role: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.role_methods.insert(role, method, def);
    }

    pub fn register_role_impl_member(&mut self, member: DefId, impl_def: DefId) {
        self.role_impl_members.insert(member, impl_def);
        let members = self.role_impl_member_sets.entry(impl_def).or_default();
        if !members.contains(&member) {
            members.push(member);
            members.sort_by_key(|def| def.0);
        }
    }

    pub fn register_local_value_type_method(
        &mut self,
        scope: crate::ModuleId,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.local_methods
            .insert_value_type_method(scope, receiver, method, def);
    }

    pub fn register_local_ref_type_method(
        &mut self,
        scope: crate::ModuleId,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.local_methods
            .insert_ref_type_method(scope, receiver, method, def);
    }

    pub fn register_local_effect_method(
        &mut self,
        scope: crate::ModuleId,
        effect: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.local_methods
            .insert_effect_method(scope, effect, method, def);
    }

    pub fn register_local_role_method(
        &mut self,
        scope: crate::ModuleId,
        role: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.local_methods
            .insert_role_method(scope, role, method, def);
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
                ConstraintEvent::SubtractFactAdded { effect, .. } => {
                    for select in self.selections.pending_for_effect_fact(effect) {
                        self.enqueue(AnalysisWork::ProbeSelect(select));
                    }
                }
                ConstraintEvent::UpperBoundAdded { .. } => {}
            }
        }
    }

    pub fn drain_work(&mut self) {
        loop {
            while self.step() {}
            if !self.resolve_roles_for_unresolved_methods() {
                break;
            }
        }
    }

    pub fn resolve_unresolved_selections_as_record_fields(&mut self) {
        self.drain_work();
        let unresolved = self
            .selections
            .iter()
            .map(|(select_id, _)| select_id)
            .collect::<Vec<_>>();
        for select_id in unresolved {
            let name = self.poly.select(select_id).name.clone();
            let target = self
                .role_method_for_select(select_id, &name)
                .unwrap_or(SelectionTarget::RecordField);
            self.enqueue(AnalysisWork::ApplySelectionResolution { select_id, target });
        }
        self.drain_work();
    }

    fn enqueue_unresolved_selection_probes(&mut self) {
        let unresolved = self
            .selections
            .iter()
            .map(|(select_id, _)| select_id)
            .collect::<Vec<_>>();
        for select_id in unresolved {
            self.enqueue(AnalysisWork::ProbeSelect(select_id));
        }
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
            AnalysisWork::ResolveRef(_) => {}
            AnalysisWork::ProbeSelect(select_id) => self.probe_select(select_id),
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
                if self.poly.select(select_id).resolution.is_some() {
                    return;
                }
                let name = self.poly.select(select_id).name.clone();
                self.poly.resolve_select(select_id, target.resolution());
                let Some(use_site) = self.selections.remove(select_id) else {
                    return;
                };
                match target {
                    SelectionTarget::RecordField => {
                        self.constrain_record_field_selection(use_site.method_value, &name);
                    }
                    SelectionTarget::Method { def } => {
                        self.scc.use_resolved(SccInput::UseResolved {
                            parent: use_site.parent,
                            target: def,
                            use_value: use_site.method_value,
                        });
                    }
                    SelectionTarget::EffectMethod { def } => {
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
                self.apply_scc_input(SccInput::MethodDependencyResolved {
                    parent: use_site.parent,
                });
            }
            AnalysisWork::Scc(input) => self.apply_scc_input(input),
        }
        self.route_scc_events();
    }

    fn apply_scc_input(&mut self, input: SccInput) {
        match &input {
            SccInput::DefFinished { def } => self.add_unready_role_impl_dependencies(*def),
            SccInput::MethodDependencyResolved { parent } => {
                self.add_unready_role_impl_dependencies(*parent)
            }
            SccInput::UseResolved { .. }
            | SccInput::DependencyAdded { .. }
            | SccInput::RegisterDef { .. }
            | SccInput::MethodDependencyAdded { .. } => {}
        }
        self.scc.apply(input);
    }

    fn add_unready_role_impl_dependencies(&mut self, parent: DefId) {
        let roles = self
            .roles
            .for_owner(parent)
            .iter()
            .map(|role| role.role.clone())
            .collect::<FxHashSet<_>>();
        for role in roles {
            let candidates = self.role_impls.candidates(&role).to_vec();
            for candidate in candidates {
                let Some(impl_def) = candidate.impl_def else {
                    continue;
                };
                for member in self.unready_role_impl_members(impl_def) {
                    self.scc.apply(SccInput::DependencyAdded {
                        parent,
                        target: member,
                    });
                }
            }
        }
    }

    fn unready_role_impl_members(&self, impl_def: DefId) -> Vec<DefId> {
        self.role_impl_member_sets
            .get(&impl_def)
            .into_iter()
            .flat_map(|members| members.iter().copied())
            .filter(|member| !self.schemes.contains_key(member))
            .collect()
    }

    fn probe_select(&mut self, select_id: SelectId) {
        if self.poly.select(select_id).resolution.is_some() {
            return;
        }
        let Some(use_site) = self.selections.get(select_id).copied() else {
            return;
        };
        let name = self.poly.select(select_id).name.clone();
        let target = self.probe_method_value(
            select_id,
            use_site.method_value,
            &name,
            &mut FxHashSet::default(),
        );
        let Some(target) = target else { return };
        self.enqueue(AnalysisWork::ApplySelectionResolution { select_id, target });
    }

    fn method_taint_index(&self) -> MethodTaintIndex {
        let mut index = MethodTaintIndex::default();
        let mut selects = self.selections.unresolved().collect::<Vec<_>>();
        selects.sort_by_key(|select| select.0);
        for select in selects {
            let Some(use_site) = self.selections.get(select) else {
                continue;
            };
            let mut builder = MethodTaintBuilder {
                session: self,
                select,
                index: &mut index,
                visited: FxHashSet::default(),
            };
            builder.visit_var(use_site.method_value, TaintPolarity::Positive);
        }
        index
    }

    fn resolve_roles_for_unresolved_methods(&mut self) -> bool {
        let mut parents = self
            .selections
            .iter()
            .map(|(_, use_site)| use_site.parent)
            .collect::<Vec<_>>();
        parents.sort_by_key(|def| def.0);
        parents.dedup();
        if parents.is_empty() {
            return false;
        }

        let method_taint = self.method_taint_index();
        if method_taint.is_empty() {
            return false;
        }

        let mut progressed = false;
        for def in parents {
            let Some(root) = self.scc.root_of(def) else {
                continue;
            };
            if self.resolve_method_tainted_roles_for_def(def, root, &method_taint) {
                progressed = true;
            }
        }

        if progressed {
            self.route_constraint_events();
            self.enqueue_unresolved_selection_probes();
        }
        progressed
    }

    fn resolve_method_tainted_roles_for_def(
        &mut self,
        def: DefId,
        root: TypeVar,
        method_taint: &MethodTaintIndex,
    ) -> bool {
        let mut progressed = false;
        loop {
            let mut compact = compact_type_var(self.infer.constraints(), root);
            normalize_compact_casts(&mut compact, &FxHashSet::default());
            let roles = self.method_tainted_role_constraints(def, method_taint);
            let resolutions = resolve_role_constraints_with_method_taint(
                self.infer.constraints(),
                &compact,
                &roles,
                &self.role_impls,
                &self.applied_method_role_resolutions,
                method_taint,
            );
            if resolutions.is_empty() {
                break;
            }

            for resolution in resolutions {
                self.applied_method_role_resolutions
                    .insert(resolution.key.clone());
                self.constrain_role_resolution(def, &resolution);
                progressed = true;
            }
            self.route_constraint_events();
        }
        progressed
    }

    fn method_tainted_role_constraints(
        &self,
        def: DefId,
        method_taint: &MethodTaintIndex,
    ) -> Vec<CompactRoleConstraint> {
        coalesce_role_constraints(
            self.roles
                .for_owner(def)
                .iter()
                .map(|constraint| compact_role_constraint(self.infer.constraints(), constraint))
                .filter(|constraint| {
                    compact_role_constraint_has_method_taint(constraint, method_taint)
                })
                .collect(),
        )
    }

    fn probe_method_value(
        &mut self,
        select_id: SelectId,
        method_value: TypeVar,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        if !visited.insert(method_value) {
            return None;
        }
        let bounds = self.infer.constraints().bounds().of(method_value)?;
        let uppers = bounds
            .uppers()
            .iter()
            .map(|bound| bound.neg)
            .collect::<Vec<_>>();
        for upper in uppers {
            if let Some(target) = self.probe_method_upper(select_id, upper, name, visited) {
                return Some(target);
            }
        }
        None
    }

    fn probe_method_upper(
        &mut self,
        select_id: SelectId,
        upper: NegId,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        match self.infer.constraints().types().neg(upper).clone() {
            Neg::Var(var) => self.probe_method_value(select_id, var, name, visited),
            Neg::Fun { arg, arg_eff, .. } => self
                .probe_effect_select_pos(select_id, arg_eff, name, &mut FxHashSet::default())
                .or_else(|| self.probe_select_pos(select_id, arg, name, &mut FxHashSet::default())),
            Neg::Intersection(left, right) => self
                .probe_method_upper(select_id, left, name, visited)
                .or_else(|| self.probe_method_upper(select_id, right, name, visited)),
            Neg::Stack { inner, .. } => self.probe_method_upper(select_id, inner, name, visited),
            Neg::Top
            | Neg::Bot
            | Neg::Con(_, _)
            | Neg::Record(_)
            | Neg::PolyVariant(_)
            | Neg::Tuple(_)
            | Neg::Row(_, _) => None,
        }
    }

    fn probe_effect_select_pos(
        &mut self,
        select_id: SelectId,
        pos: PosId,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        let mut paths = Vec::new();
        self.collect_effect_paths_from_pos(select_id, pos, visited, &mut paths);
        self.effect_method_for_paths(select_id, &paths, name)
    }

    fn collect_effect_paths_from_pos(
        &mut self,
        select_id: SelectId,
        pos: PosId,
        visited: &mut FxHashSet<TypeVar>,
        out: &mut Vec<Vec<String>>,
    ) {
        match self.infer.constraints().types().pos(pos).clone() {
            Pos::Con(path, _) => push_unique_path(out, path),
            Pos::Row(items) => {
                for item in items {
                    self.collect_effect_paths_from_pos(select_id, item, visited, out);
                }
            }
            Pos::Var(var) => {
                self.probe_effect_select_var_collect(select_id, var, visited, out);
            }
            Pos::Union(left, right) => {
                self.collect_effect_paths_from_pos(select_id, left, visited, out);
                self.collect_effect_paths_from_pos(select_id, right, visited, out);
            }
            Pos::NonSubtract(pos, _) => {
                self.collect_effect_paths_from_pos(select_id, pos, visited, out)
            }
            Pos::Stack { inner, .. } => {
                self.collect_effect_paths_from_pos(select_id, inner, visited, out)
            }
            Pos::Bot
            | Pos::Fun { .. }
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_) => {}
        }
    }

    fn probe_effect_select_var_collect(
        &mut self,
        select_id: SelectId,
        effect: TypeVar,
        visited: &mut FxHashSet<TypeVar>,
        out: &mut Vec<Vec<String>>,
    ) {
        if !visited.insert(effect) {
            return;
        }
        self.selections.watch_effect(effect, select_id);
        for fact in self.infer.constraints().subtracts().facts(effect) {
            collect_subtractability_effect_paths(&fact.subtractability, out);
        }
        if let Some(bounds) = self.infer.constraints().bounds().of(effect) {
            let lowers = bounds
                .lowers()
                .iter()
                .map(|bound| bound.pos)
                .collect::<Vec<_>>();
            for lower in lowers {
                self.collect_effect_paths_from_pos(select_id, lower, visited, out);
            }
        }
    }

    fn probe_select_var(
        &mut self,
        select_id: SelectId,
        var: TypeVar,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        if !visited.insert(var) {
            return None;
        }
        self.selections.watch_receiver(var, select_id);
        let lowers = self
            .infer
            .constraints()
            .bounds()
            .of(var)?
            .lowers()
            .iter()
            .map(|bound| bound.pos)
            .collect::<Vec<_>>();
        for lower in lowers {
            if let Some(target) = self.probe_select_pos(select_id, lower, name, visited) {
                return Some(target);
            }
        }
        None
    }

    fn probe_select_pos(
        &mut self,
        select_id: SelectId,
        pos: PosId,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        match self.infer.constraints().types().pos(pos).clone() {
            Pos::Var(var) => self.probe_select_var(select_id, var, name, visited),
            Pos::Con(path, args) if crate::std_paths::is_control_var_ref_type(&path) => {
                if let Some(target) = self.value_method_for_receiver(select_id, &path, name) {
                    return Some(target);
                }
                let payload = self.ref_payload_probe(&args)?;
                self.selections.watch_ref_payload(payload.var, select_id);
                self.probe_ref_select_pos(select_id, payload.lower, name, visited)
                    .or_else(|| self.probe_ref_select_var(select_id, payload.var, name, visited))
            }
            Pos::Con(path, _) => self.value_method_for_receiver(select_id, &path, name),
            Pos::Union(left, right) => self
                .probe_select_pos(select_id, left, name, visited)
                .or_else(|| self.probe_select_pos(select_id, right, name, visited)),
            Pos::NonSubtract(pos, _) => self.probe_select_pos(select_id, pos, name, visited),
            Pos::Stack { inner, .. } => self.probe_select_pos(select_id, inner, name, visited),
            Pos::Bot
            | Pos::Fun { .. }
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_)
            | Pos::Row(_) => None,
        }
    }

    fn probe_ref_select_var(
        &mut self,
        select_id: SelectId,
        var: TypeVar,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        if !visited.insert(var) {
            return None;
        }
        let lowers = self
            .infer
            .constraints()
            .bounds()
            .of(var)?
            .lowers()
            .iter()
            .map(|bound| bound.pos)
            .collect::<Vec<_>>();
        for lower in lowers {
            if let Some(target) = self.probe_ref_select_pos(select_id, lower, name, visited) {
                return Some(target);
            }
        }
        None
    }

    fn probe_ref_select_pos(
        &mut self,
        select_id: SelectId,
        pos: PosId,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        match self.infer.constraints().types().pos(pos).clone() {
            Pos::Var(var) => self.probe_ref_select_var(select_id, var, name, visited),
            Pos::Con(path, _) => self.ref_method_for_receiver(select_id, &path, name),
            Pos::Union(left, right) => self
                .probe_ref_select_pos(select_id, left, name, visited)
                .or_else(|| self.probe_ref_select_pos(select_id, right, name, visited)),
            Pos::NonSubtract(pos, _) => self.probe_ref_select_pos(select_id, pos, name, visited),
            Pos::Stack { inner, .. } => self.probe_ref_select_pos(select_id, inner, name, visited),
            Pos::Bot
            | Pos::Fun { .. }
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_)
            | Pos::Row(_) => None,
        }
    }

    fn value_method_for_receiver(
        &self,
        select_id: SelectId,
        receiver: &[String],
        name: &str,
    ) -> Option<SelectionTarget> {
        if let Some(scope) = self.local_method_scope(select_id) {
            let candidates = self
                .local_methods
                .value_type_candidates(scope, receiver, name);
            if let Some(target) = method_target_from_candidates(candidates) {
                return Some(target);
            }
        }
        let candidates = self.methods.value_candidates(receiver, name);
        method_target_from_candidates(candidates)
    }

    fn ref_method_for_receiver(
        &self,
        select_id: SelectId,
        receiver: &[String],
        name: &str,
    ) -> Option<SelectionTarget> {
        if let Some(scope) = self.local_method_scope(select_id) {
            let candidates = self
                .local_methods
                .ref_type_candidates(scope, receiver, name);
            if let Some(target) = method_target_from_candidates(candidates) {
                return Some(target);
            }
        }
        let candidates = self.methods.ref_candidates(receiver, name);
        method_target_from_candidates(candidates)
    }

    fn effect_method_for_paths(
        &self,
        select_id: SelectId,
        effects: &[Vec<String>],
        name: &str,
    ) -> Option<SelectionTarget> {
        if let Some(scope) = self.local_method_scope(select_id) {
            let candidates = self
                .local_methods
                .effect_candidates(scope, name)
                .iter()
                .filter(|candidate| effects.iter().any(|effect| effect == &candidate.effect))
                .collect::<Vec<_>>();
            if let Some(target) = effect_method_target_from_candidates(&candidates) {
                return Some(target);
            }
        }
        let candidates = self
            .effect_methods
            .candidates(name)
            .iter()
            .filter(|candidate| effects.iter().any(|effect| effect == &candidate.effect))
            .collect::<Vec<_>>();
        effect_method_target_from_candidates(&candidates)
    }

    fn role_method_for_select(&self, select_id: SelectId, name: &str) -> Option<SelectionTarget> {
        if let Some(scope) = self.local_method_scope(select_id) {
            match self.local_methods.role_candidates(scope, name) {
                [candidate] => {
                    return Some(SelectionTarget::TypeclassMethod {
                        member: candidate.def,
                    });
                }
                [] | [_, ..] => {}
            }
        }
        match self.role_methods.candidates(name) {
            [candidate] => Some(SelectionTarget::TypeclassMethod {
                member: candidate.def,
            }),
            [] | [_, ..] => None,
        }
    }

    fn local_method_scope(&self, select_id: SelectId) -> Option<crate::ModuleId> {
        self.selections
            .get(select_id)
            .and_then(|use_site| use_site.local_method_scope)
    }

    fn ref_payload_probe(&self, args: &[poly::types::NeuId]) -> Option<RefPayloadProbe> {
        let payload = args.get(1)?;
        match self.infer.constraints().types().neu(*payload) {
            Neu::Bounds(lower, var, _) => Some(RefPayloadProbe {
                lower: *lower,
                var: *var,
            }),
            Neu::Con(_, _)
            | Neu::Fun { .. }
            | Neu::Record(_)
            | Neu::PolyVariant(_)
            | Neu::Tuple(_) => None,
        }
    }

    fn constrain_record_field_selection(&mut self, method_value: TypeVar, name: &str) {
        let Some(bounds) = self.infer.constraints().bounds().of(method_value) else {
            return;
        };
        let uppers = bounds
            .uppers()
            .iter()
            .map(|bound| bound.neg)
            .collect::<Vec<_>>();
        for upper in uppers {
            self.constrain_record_field_selection_from_method_upper(upper, name);
        }
    }

    fn constrain_record_field_selection_from_method_upper(&mut self, upper: NegId, name: &str) {
        match self.infer.constraints().types().neg(upper).clone() {
            Neg::Var(var) => self.constrain_record_field_selection(var, name),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.constrain_record_field_call(arg, arg_eff, ret_eff, ret, name),
            Neg::Intersection(left, right) => {
                self.constrain_record_field_selection_from_method_upper(left, name);
                self.constrain_record_field_selection_from_method_upper(right, name);
            }
            Neg::Stack { inner, .. } => {
                self.constrain_record_field_selection_from_method_upper(inner, name);
            }
            Neg::Top
            | Neg::Bot
            | Neg::Con(_, _)
            | Neg::Record(_)
            | Neg::PolyVariant(_)
            | Neg::Tuple(_)
            | Neg::Row(_, _) => {}
        }
    }

    fn constrain_record_field_call(
        &mut self,
        receiver: PosId,
        receiver_effect: PosId,
        result_effect: NegId,
        result: NegId,
        name: &str,
    ) {
        let field = RecordField {
            name: name.to_string(),
            value: result,
            optional: false,
        };
        let record = self.infer.alloc_neg(Neg::Record(vec![field]));
        self.infer.subtype(receiver, record);
        self.infer.subtype(receiver_effect, result_effect);
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
                SccEvent::InstantiateUse {
                    parent,
                    target,
                    use_value,
                } => {
                    self.instantiate_use(parent, target, use_value);
                    self.scc_events.push(SccEvent::InstantiateUse {
                        parent,
                        target,
                        use_value,
                    });
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
            self.collect_role_impl_member_prerequisites(def, &scheme);
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
                self.infer.constraints(),
                &scheme,
                &ancestors,
            );
            self.set_def_scheme(def, finalized.scheme);
        }
    }

    fn collect_role_impl_member_prerequisites(
        &mut self,
        def: DefId,
        scheme: &GeneralizedCompactRoot,
    ) {
        let Some(impl_def) = self.role_impl_members.get(&def).copied() else {
            return;
        };
        let quantifiers = scheme.quantifiers.iter().copied().collect::<FxHashSet<_>>();
        let mut prerequisites = Vec::new();
        for role in &scheme.role_predicates {
            let prerequisite = self.finalize_compact_role_constraint(role);
            let vars = prerequisite.raw_vars(self.infer.constraints().types());
            if vars.iter().any(|var| !quantifiers.contains(var)) {
                prerequisites.push(prerequisite);
            }
        }
        self.role_impls
            .extend_prerequisites_for_impl(impl_def, prerequisites);
    }

    fn instantiate_use(&mut self, parent: DefId, target: DefId, use_value: TypeVar) {
        let Some(scheme) = self.def_scheme(target).cloned() else {
            return;
        };
        let instantiated = instantiate_scheme_with_roles(
            &self.poly.typ,
            &mut self.infer,
            TypeLevel::secondary(),
            &scheme,
        );
        let use_upper = self.infer.alloc_neg(Neg::Var(use_value));
        self.infer.subtype(instantiated.predicate, use_upper);
        self.insert_instantiated_role_predicates(parent, &instantiated.role_predicates);
    }

    fn insert_instantiated_role_predicates(&mut self, owner: DefId, predicates: &[RolePredicate]) {
        for predicate in predicates {
            let constraint = self.role_constraint_from_predicate(predicate);
            self.roles.insert(owner, constraint);
        }
    }

    fn role_constraint_from_predicate(&mut self, predicate: &RolePredicate) -> RoleConstraint {
        RoleConstraint {
            role: predicate.role.clone(),
            inputs: predicate
                .inputs
                .iter()
                .map(|input| self.role_arg_from_neu(*input))
                .collect(),
            associated: predicate
                .associated
                .iter()
                .map(|associated| RoleAssociatedConstraint {
                    name: associated.name.clone(),
                    value: self.role_arg_from_neu(associated.value),
                })
                .collect(),
        }
    }

    fn role_arg_from_neu(&mut self, id: NeuId) -> RoleConstraintArg {
        match self.infer.constraints().types().neu(id).clone() {
            Neu::Bounds(lower, _, upper) => RoleConstraintArg { lower, upper },
            neu => RoleConstraintArg {
                lower: self.pos_from_neu(neu.clone()),
                upper: self.neg_from_neu(neu),
            },
        }
    }

    fn pos_from_neu(&mut self, neu: Neu) -> PosId {
        let pos = match neu {
            Neu::Bounds(lower, _, _) => return lower,
            Neu::Con(path, args) => Pos::Con(path, args),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Pos::Fun {
                arg: self.neg_from_neu_id(arg),
                arg_eff: self.neg_from_neu_id(arg_eff),
                ret_eff: self.pos_from_neu_id(ret_eff),
                ret: self.pos_from_neu_id(ret),
            },
            Neu::Record(fields) => Pos::Record(
                fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.pos_from_neu_id(field.value),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Neu::PolyVariant(items) => Pos::PolyVariant(
                items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.pos_from_neu_id(payload))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Neu::Tuple(items) => Pos::Tuple(
                items
                    .into_iter()
                    .map(|item| self.pos_from_neu_id(item))
                    .collect(),
            ),
        };
        self.infer.alloc_pos(pos)
    }

    fn neg_from_neu(&mut self, neu: Neu) -> NegId {
        let neg = match neu {
            Neu::Bounds(_, _, upper) => return upper,
            Neu::Con(path, args) => Neg::Con(path, args),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neg::Fun {
                arg: self.pos_from_neu_id(arg),
                arg_eff: self.pos_from_neu_id(arg_eff),
                ret_eff: self.neg_from_neu_id(ret_eff),
                ret: self.neg_from_neu_id(ret),
            },
            Neu::Record(fields) => Neg::Record(
                fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.neg_from_neu_id(field.value),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Neu::PolyVariant(items) => Neg::PolyVariant(
                items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.neg_from_neu_id(payload))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Neu::Tuple(items) => Neg::Tuple(
                items
                    .into_iter()
                    .map(|item| self.neg_from_neu_id(item))
                    .collect(),
            ),
        };
        self.infer.alloc_neg(neg)
    }

    fn pos_from_neu_id(&mut self, id: NeuId) -> PosId {
        self.pos_from_neu(self.infer.constraints().types().neu(id).clone())
    }

    fn neg_from_neu_id(&mut self, id: NeuId) -> NegId {
        self.neg_from_neu(self.infer.constraints().types().neu(id).clone())
    }

    fn generalize_root_with_prepasses(
        &mut self,
        def: DefId,
        root: TypeVar,
    ) -> GeneralizedCompactRoot {
        let mut applied_casts = FxHashSet::<CompactCastKey>::default();
        let mut applied_roles = self.applied_method_role_resolutions.clone();
        let mut applied_role_demands = self
            .applied_method_role_resolutions
            .iter()
            .map(|key| key.demand.clone())
            .collect::<FxHashSet<_>>();
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

fn method_target_from_candidates(
    candidates: &[crate::methods::TypeMethodCandidate],
) -> Option<SelectionTarget> {
    match candidates {
        [candidate] => Some(SelectionTarget::Method { def: candidate.def }),
        [] | [_, ..] => None,
    }
}

fn effect_method_target_from_candidates(
    candidates: &[&EffectMethodCandidate],
) -> Option<SelectionTarget> {
    match candidates {
        [candidate] => Some(SelectionTarget::EffectMethod { def: candidate.def }),
        [] | [_, ..] => None,
    }
}

fn collect_subtractability_effect_paths(
    subtractability: &Subtractability,
    out: &mut Vec<Vec<String>>,
) {
    match subtractability {
        Subtractability::Set(path, _) => push_unique_path(out, path.clone()),
        Subtractability::SetMany(families) => {
            for (path, _) in families {
                push_unique_path(out, path.clone());
            }
        }
        Subtractability::Empty
        | Subtractability::All
        | Subtractability::AllExcept(_, _)
        | Subtractability::AllExceptMany(_) => {}
    }
}

fn push_unique_path(out: &mut Vec<Vec<String>>, path: Vec<String>) {
    if !out.contains(&path) {
        out.push(path);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RefPayloadProbe {
    lower: PosId,
    var: TypeVar,
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
    EffectMethod { def: DefId },
    TypeclassMethod { member: DefId },
}

impl SelectionTarget {
    pub fn resolution(self) -> SelectResolution {
        match self {
            Self::RecordField => SelectResolution::RecordField,
            Self::Method { def } => SelectResolution::Method { def },
            Self::EffectMethod { def } => SelectResolution::Method { def },
            Self::TypeclassMethod { member } => SelectResolution::TypeclassMethod { member },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TaintPolarity {
    Positive,
    Negative,
}

impl TaintPolarity {
    fn flipped(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

struct MethodTaintBuilder<'a, 'b> {
    session: &'a AnalysisSession,
    select: SelectId,
    index: &'b mut MethodTaintIndex,
    visited: FxHashSet<(TypeVar, TaintPolarity)>,
}

impl<'a, 'b> MethodTaintBuilder<'a, 'b> {
    fn visit_var(&mut self, var: TypeVar, polarity: TaintPolarity) {
        push_unique_select(self.index.entry(var).or_default(), self.select);
        if !self.visited.insert((var, polarity)) {
            return;
        }
        let Some(bounds) = self.session.infer.constraints().bounds().of(var) else {
            return;
        };
        match polarity {
            TaintPolarity::Positive => {
                let uppers = bounds
                    .uppers()
                    .iter()
                    .map(|bound| bound.neg)
                    .collect::<Vec<_>>();
                for upper in uppers {
                    self.visit_neg(upper, polarity);
                }
            }
            TaintPolarity::Negative => {
                let lowers = bounds
                    .lowers()
                    .iter()
                    .map(|bound| bound.pos)
                    .collect::<Vec<_>>();
                for lower in lowers {
                    self.visit_pos(lower, polarity);
                }
            }
        }
    }

    fn visit_pos(&mut self, pos: PosId, polarity: TaintPolarity) {
        match self.session.infer.constraints().types().pos(pos).clone() {
            Pos::Var(var) => self.visit_var(var, polarity),
            Pos::Con(_, args) => {
                for arg in args {
                    self.visit_neu(arg);
                }
            }
            Pos::Tuple(items) => {
                for item in items {
                    self.visit_pos(item, polarity);
                }
            }
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.visit_neg(arg, polarity.flipped());
                self.visit_neg(arg_eff, polarity.flipped());
                self.visit_pos(ret_eff, polarity);
                self.visit_pos(ret, polarity);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.visit_pos(field.value, polarity);
                }
            }
            Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { fields, tail } => {
                for field in fields {
                    self.visit_pos(field.value, polarity);
                }
                self.visit_pos(tail, polarity);
            }
            Pos::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.visit_pos(payload, polarity);
                    }
                }
            }
            Pos::Row(items) => {
                for item in items {
                    self.visit_pos(item, polarity);
                }
            }
            Pos::NonSubtract(pos, _) => self.visit_pos(pos, polarity),
            Pos::Stack { inner, .. } => self.visit_pos(inner, polarity),
            Pos::Union(left, right) => {
                self.visit_pos(left, polarity);
                self.visit_pos(right, polarity);
            }
            Pos::Bot => {}
        }
    }

    fn visit_neg(&mut self, neg: NegId, polarity: TaintPolarity) {
        match self.session.infer.constraints().types().neg(neg).clone() {
            Neg::Var(var) => self.visit_var(var, polarity),
            Neg::Con(_, args) => {
                for arg in args {
                    self.visit_neu(arg);
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.visit_neg(item, polarity);
                }
            }
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.visit_pos(arg, polarity.flipped());
                self.visit_pos(arg_eff, polarity.flipped());
                self.visit_neg(ret_eff, polarity);
                self.visit_neg(ret, polarity);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.visit_neg(field.value, polarity);
                }
            }
            Neg::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.visit_neg(payload, polarity);
                    }
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.visit_neg(item, polarity);
                }
                self.visit_neg(tail, polarity);
            }
            Neg::Intersection(left, right) => {
                self.visit_neg(left, polarity);
                self.visit_neg(right, polarity);
            }
            Neg::Stack { inner, .. } => self.visit_neg(inner, polarity),
            Neg::Top | Neg::Bot => {}
        }
    }

    fn visit_neu(&mut self, neu: NeuId) {
        match self.session.infer.constraints().types().neu(neu).clone() {
            Neu::Bounds(lower, var, upper) => {
                self.visit_var(var, TaintPolarity::Positive);
                self.visit_var(var, TaintPolarity::Negative);
                self.visit_pos(lower, TaintPolarity::Positive);
                self.visit_neg(upper, TaintPolarity::Negative);
            }
            Neu::Con(_, args) | Neu::Tuple(args) => {
                for arg in args {
                    self.visit_neu(arg);
                }
            }
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.visit_neu(arg);
                self.visit_neu(arg_eff);
                self.visit_neu(ret_eff);
                self.visit_neu(ret);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.visit_neu(field.value);
                }
            }
            Neu::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.visit_neu(payload);
                    }
                }
            }
        }
    }
}

fn push_unique_select(items: &mut Vec<SelectId>, select: SelectId) {
    if !items.contains(&select) {
        items.push(select);
    }
}

fn compact_role_constraint_has_method_taint(
    constraint: &CompactRoleConstraint,
    method_taint: &MethodTaintIndex,
) -> bool {
    constraint
        .inputs
        .iter()
        .any(|arg| compact_role_arg_has_method_taint(arg, method_taint))
        || constraint
            .associated
            .iter()
            .any(|associated| compact_role_arg_has_method_taint(&associated.value, method_taint))
}

fn compact_role_arg_has_method_taint(
    arg: &CompactRoleArg,
    method_taint: &MethodTaintIndex,
) -> bool {
    compact_type_has_method_taint(&arg.lower, method_taint)
        || compact_type_has_method_taint(&arg.upper, method_taint)
}

fn compact_type_has_method_taint(ty: &CompactType, method_taint: &MethodTaintIndex) -> bool {
    ty.vars.iter().any(|var| {
        method_taint
            .get(&var.var)
            .is_some_and(|selects| !selects.is_empty())
    }) || ty.cons.iter().any(|con| {
        con.args
            .iter()
            .any(|arg| compact_bounds_has_method_taint(arg, method_taint))
    }) || ty.funs.iter().any(|fun| {
        compact_type_has_method_taint(&fun.arg, method_taint)
            || compact_type_has_method_taint(&fun.arg_eff, method_taint)
            || compact_type_has_method_taint(&fun.ret_eff, method_taint)
            || compact_type_has_method_taint(&fun.ret, method_taint)
    }) || ty.records.iter().any(|record| {
        record
            .fields
            .iter()
            .any(|field| compact_type_has_method_taint(&field.value, method_taint))
    }) || ty.record_spreads.iter().any(|spread| {
        spread
            .fields
            .iter()
            .any(|field| compact_type_has_method_taint(&field.value, method_taint))
            || compact_type_has_method_taint(&spread.tail, method_taint)
    }) || ty.poly_variants.iter().any(|variant| {
        variant.items.iter().any(|(_, payloads)| {
            payloads
                .iter()
                .any(|payload| compact_type_has_method_taint(payload, method_taint))
        })
    }) || ty.tuples.iter().any(|tuple| {
        tuple
            .items
            .iter()
            .any(|item| compact_type_has_method_taint(item, method_taint))
    }) || ty.rows.iter().any(|row| {
        row.items
            .iter()
            .any(|item| compact_type_has_method_taint(item, method_taint))
            || compact_type_has_method_taint(&row.tail, method_taint)
    })
}

fn compact_bounds_has_method_taint(
    bounds: &CompactBounds,
    method_taint: &MethodTaintIndex,
) -> bool {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            method_taint
                .get(self_var)
                .is_some_and(|selects| !selects.is_empty())
                || compact_type_has_method_taint(lower, method_taint)
                || compact_type_has_method_taint(upper, method_taint)
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => args
            .iter()
            .any(|arg| compact_bounds_has_method_taint(arg, method_taint)),
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            compact_bounds_has_method_taint(arg, method_taint)
                || compact_bounds_has_method_taint(arg_eff, method_taint)
                || compact_bounds_has_method_taint(ret_eff, method_taint)
                || compact_bounds_has_method_taint(ret, method_taint)
        }
        CompactBounds::Record { fields } => fields
            .iter()
            .any(|field| compact_bounds_has_method_taint(&field.value, method_taint)),
        CompactBounds::PolyVariant { items } => items.iter().any(|(_, payloads)| {
            payloads
                .iter()
                .any(|payload| compact_bounds_has_method_taint(payload, method_taint))
        }),
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
    use poly::types::{
        Neg, Neu, NeuId, Pos, Scheme, SchemeRecursiveBound, SchemeSubtractFact, SubtractId,
        Subtractability, TypeVar,
    };

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
            .alloc_pos(Pos::Con(crate::std_paths::control_var_ref_type(), vec![]));
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

    fn register_test_selection_use(
        session: &mut AnalysisSession,
        select: SelectId,
        parent: DefId,
        method_value: TypeVar,
        receiver: TypeVar,
        receiver_effect: TypeVar,
        result: TypeVar,
        result_effect: TypeVar,
    ) {
        let method = session.infer.alloc_pos(Pos::Var(method_value));
        let arg = session.infer.alloc_pos(Pos::Var(receiver));
        let arg_eff = session.infer.alloc_pos(Pos::Var(receiver_effect));
        let ret_eff = session.infer.alloc_neg(Neg::Var(result_effect));
        let ret = session.infer.alloc_neg(Neg::Var(result));
        let upper = session.infer.alloc_neg(Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        });
        session.infer.subtype(method, upper);
        let receiver_effect = session.infer.alloc_pos(Pos::Var(receiver_effect));
        let result_effect = session.infer.alloc_neg(Neg::Var(result_effect));
        session.infer.subtype(receiver_effect, result_effect);
        session.register_selection_use(
            select,
            SelectionUse {
                parent,
                method_value,
                local_method_scope: None,
            },
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
                recursive_bounds: Vec::new(),
                stack_quantifiers: Vec::new(),
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
        let method_value = TypeVar(4);
        register_test_selection_use(
            &mut session,
            select,
            parent,
            method_value,
            TypeVar(3),
            TypeVar(5),
            TypeVar(6),
            TypeVar(7),
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
    fn method_selection_resolves_when_receiver_lower_bound_has_method() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let select = session.poly.add_select("display");
        let parent = DefId(1);
        let method = DefId(2);
        let receiver = TypeVar(3);
        let method_value = TypeVar(4);
        let receiver_effect = TypeVar(5);
        let result = TypeVar(6);
        let result_effect = TypeVar(7);
        register_test_selection_use(
            &mut session,
            select,
            parent,
            method_value,
            receiver,
            receiver_effect,
            result,
            result_effect,
        );
        session
            .methods
            .insert_value(vec!["int".to_string()], "display", method);

        let lower = session
            .infer
            .alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
        let upper = session.infer.alloc_neg(Neg::Var(receiver));
        session.infer.subtype(lower, upper);
        session.drain_work();

        assert_eq!(
            session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
        assert!(session.take_scc_events().iter().any(|event| {
            matches!(
                event,
                SccEvent::ComponentEdgeAdded {
                    from,
                    to,
                } if from == &vec![parent] && to == &vec![method]
            )
        }));
    }

    #[test]
    fn method_registration_probes_existing_receiver_lower_bounds() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let select = session.poly.add_select("display");
        let parent = DefId(1);
        let method = DefId(2);
        let receiver = TypeVar(3);
        let method_value = TypeVar(4);
        let receiver_effect = TypeVar(5);
        let result = TypeVar(6);
        let result_effect = TypeVar(7);
        register_test_selection_use(
            &mut session,
            select,
            parent,
            method_value,
            receiver,
            receiver_effect,
            result,
            result_effect,
        );
        let lower = session
            .infer
            .alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
        let upper = session.infer.alloc_neg(Neg::Var(receiver));
        session.infer.subtype(lower, upper);
        session.drain_work();

        assert_eq!(session.poly.select(select).resolution, None);

        session.register_value_type_method(vec!["int".to_string()], "display", method);
        session.drain_work();

        assert_eq!(
            session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
    }

    #[test]
    fn method_selection_probes_ref_payload_lower_bounds() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let select = session.poly.add_select("display");
        let parent = DefId(1);
        let method = DefId(2);
        let receiver = TypeVar(3);
        let method_value = TypeVar(4);
        let payload = TypeVar(5);
        let effect = TypeVar(6);
        let receiver_effect = TypeVar(7);
        let result = TypeVar(8);
        let result_effect = TypeVar(9);
        register_test_selection_use(
            &mut session,
            select,
            parent,
            method_value,
            receiver,
            receiver_effect,
            result,
            result_effect,
        );
        session
            .methods
            .insert_ref(vec!["int".to_string()], "display", method);

        let int = session
            .infer
            .alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
        let payload_upper = session.infer.alloc_neg(Neg::Var(payload));
        session.infer.subtype(int, payload_upper);
        let effect_arg = infer_bounds_neu(&mut session.infer, effect);
        let payload_arg = infer_bounds_neu(&mut session.infer, payload);
        let ref_lower = session.infer.alloc_pos(Pos::Con(
            crate::std_paths::control_var_ref_type(),
            vec![effect_arg, payload_arg],
        ));
        let receiver_upper = session.infer.alloc_neg(Neg::Var(receiver));
        session.infer.subtype(ref_lower, receiver_upper);
        session.drain_work();

        assert_eq!(
            session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
    }

    #[test]
    fn effect_method_selection_resolves_from_receiver_effect_row_lower_bound() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let select = session.poly.add_select("flip");
        let parent = DefId(1);
        let method = DefId(2);
        let receiver = TypeVar(3);
        let receiver_effect = TypeVar(4);
        let result = TypeVar(5);
        let result_effect = TypeVar(6);
        let method_value = TypeVar(7);
        register_test_selection_use(
            &mut session,
            select,
            parent,
            method_value,
            receiver,
            receiver_effect,
            result,
            result_effect,
        );
        session.register_effect_method(vec!["nondet".to_string()], "flip", method);
        let nondet = session
            .infer
            .alloc_pos(Pos::Con(vec!["nondet".into()], Vec::new()));
        let row = session.infer.alloc_pos(Pos::Row(vec![nondet]));
        let upper = session.infer.alloc_neg(Neg::Var(receiver_effect));
        session.infer.subtype(row, upper);
        session.drain_work();

        assert_eq!(
            session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
    }

    #[test]
    fn effect_method_selection_resolves_from_receiver_effect_subtract_fact() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let select = session.poly.add_select("flip");
        let parent = DefId(1);
        let method = DefId(2);
        let receiver = TypeVar(3);
        let receiver_effect = TypeVar(4);
        let result = TypeVar(5);
        let result_effect = TypeVar(6);
        let method_value = TypeVar(7);
        register_test_selection_use(
            &mut session,
            select,
            parent,
            method_value,
            receiver,
            receiver_effect,
            result,
            result_effect,
        );
        session.register_effect_method(vec!["nondet".to_string()], "flip", method);
        session.infer.subtract_fact(
            receiver_effect,
            SubtractId(0),
            Subtractability::Set(vec!["nondet".into()], Vec::new()),
        );
        session.drain_work();

        assert_eq!(
            session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
    }

    #[test]
    fn effect_method_selection_reprobes_when_transitive_effect_fact_is_added() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let select = session.poly.add_select("flip");
        let parent = DefId(1);
        let method = DefId(2);
        let receiver = TypeVar(3);
        let receiver_effect = TypeVar(4);
        let tail_effect = TypeVar(5);
        let result = TypeVar(6);
        let result_effect = TypeVar(7);
        let method_value = TypeVar(8);
        register_test_selection_use(
            &mut session,
            select,
            parent,
            method_value,
            receiver,
            receiver_effect,
            result,
            result_effect,
        );
        session.register_effect_method(vec!["nondet".to_string()], "flip", method);
        let tail = session.infer.alloc_pos(Pos::Var(tail_effect));
        let upper = session.infer.alloc_neg(Neg::Var(receiver_effect));
        session.infer.subtype(tail, upper);
        session.drain_work();

        assert_eq!(session.poly.select(select).resolution, None);

        session.infer.subtract_fact(
            tail_effect,
            SubtractId(0),
            Subtractability::Set(vec!["nondet".into()], Vec::new()),
        );
        session.drain_work();

        assert_eq!(
            session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
    }

    #[test]
    fn unresolved_method_selection_forces_tainted_role_resolution() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let owner = DefId(1);
        let method = DefId(2);
        let root = TypeVar(0);
        let receiver = TypeVar(3);
        let method_value = TypeVar(4);
        let receiver_effect = TypeVar(5);
        let result = TypeVar(6);
        let result_effect = TypeVar(7);
        let select = session.poly.add_select("display");
        let role = vec!["HasDisplay".to_string()];
        let unit = vec!["unit".to_string()];
        let int = vec!["int".to_string()];

        session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
            def: owner,
            root,
        }));
        session.roles.insert(
            owner,
            RoleConstraint {
                role: role.clone(),
                inputs: vec![role_exact_arg(&mut session.infer, unit.clone())],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".to_string(),
                    value: role_var_arg(&mut session.infer, receiver),
                }],
            },
        );
        session.role_impls.insert(RoleImplCandidate {
            impl_def: None,
            role,
            inputs: vec![role_exact_arg(&mut session.infer, unit)],
            associated: vec![RoleAssociatedConstraint {
                name: "out".to_string(),
                value: role_exact_arg(&mut session.infer, int.clone()),
            }],
            prerequisites: Vec::new(),
        });
        register_test_selection_use(
            &mut session,
            select,
            owner,
            method_value,
            receiver,
            receiver_effect,
            result,
            result_effect,
        );
        session.register_value_type_method(int, "display", method);
        session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: owner }));

        session.drain_work();

        assert_eq!(
            session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
        assert!(session.take_scc_events().iter().any(|event| {
            matches!(
                event,
                SccEvent::ComponentEdgeAdded { from, to }
                    if from == &vec![owner] && to == &vec![method]
            )
        }));
    }

    #[test]
    fn unresolved_method_selection_does_not_use_tainted_role_endpoint() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let owner = DefId(1);
        let method = DefId(2);
        let root = TypeVar(0);
        let receiver = TypeVar(3);
        let method_value = TypeVar(4);
        let receiver_effect = TypeVar(5);
        let result = TypeVar(6);
        let result_effect = TypeVar(7);
        let output = TypeVar(8);
        let select = session.poly.add_select("display");
        let role = vec!["Box".to_string()];
        let int = vec!["int".to_string()];
        let unit = vec!["unit".to_string()];

        session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
            def: owner,
            root,
        }));
        session.roles.insert(
            owner,
            RoleConstraint {
                role: role.clone(),
                inputs: vec![role_left_concrete_var_arg(
                    &mut session.infer,
                    int.clone(),
                    receiver,
                )],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".to_string(),
                    value: role_var_arg(&mut session.infer, output),
                }],
            },
        );
        session.role_impls.insert(RoleImplCandidate {
            impl_def: None,
            role,
            inputs: vec![role_exact_arg(&mut session.infer, int.clone())],
            associated: vec![RoleAssociatedConstraint {
                name: "out".to_string(),
                value: role_exact_arg(&mut session.infer, unit.clone()),
            }],
            prerequisites: Vec::new(),
        });
        register_test_selection_use(
            &mut session,
            select,
            owner,
            method_value,
            receiver,
            receiver_effect,
            result,
            result_effect,
        );
        session.register_value_type_method(int, "display", method);
        session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: owner }));

        session.drain_work();

        assert_eq!(session.poly.select(select).resolution, None);
        assert_var_lacks_exact_bound(&session, output, &unit);
    }

    #[test]
    fn unresolved_selection_falls_back_to_record_field_constraint_in_final_phase() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let select = session.poly.add_select("size");
        let parent = DefId(1);
        let receiver = TypeVar(2);
        let result = TypeVar(3);
        let receiver_effect = TypeVar(4);
        let result_effect = TypeVar(5);
        let method_value = TypeVar(6);
        register_test_selection_use(
            &mut session,
            select,
            parent,
            method_value,
            receiver,
            receiver_effect,
            result,
            result_effect,
        );

        session.resolve_unresolved_selections_as_record_fields();

        assert_eq!(
            session.poly.select(select).resolution,
            Some(SelectResolution::RecordField)
        );
        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(receiver)
            .expect("record fallback should constrain receiver");
        assert!(bounds.uppers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().neg(bound.neg),
                Neg::Record(fields)
                    if fields.len() == 1
                        && fields[0].name == "size"
                        && matches!(
                            session.infer.constraints().types().neg(fields[0].value),
                            Neg::Var(var) if *var == result
                )
            )
        }));
        let result_effect_bounds = session
            .infer
            .constraints()
            .bounds()
            .of(result_effect)
            .expect("record fallback should flow receiver effect to result");
        assert!(result_effect_bounds.lowers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().pos(bound.pos),
                Pos::Var(var) if *var == receiver_effect
            )
        }));
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
        assert!(use_bounds
            .lowers()
            .iter()
            .any(|bound| bound.pos == b_root_pos && bound.weights == ConstraintWeights::empty()));
        let target_bounds = bounds.of(b_root).expect("target root bounds");
        assert!(target_bounds
            .uppers()
            .iter()
            .any(|bound| bound.neg == a_to_b_neg && bound.weights == ConstraintWeights::empty()));

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
    fn role_impl_member_residual_roles_become_impl_prerequisites() {
        let mut poly = PolyArena::new();
        let impl_def = poly.defs.fresh();
        poly.defs.set(
            impl_def,
            Def::Mod {
                vis: Vis::My,
                children: Vec::new(),
            },
        );
        let member = poly.defs.fresh();
        poly.defs.set(
            member,
            Def::Let {
                vis: Vis::Our,
                scheme: None,
                body: None,
                children: Vec::new(),
            },
        );
        let mut session = AnalysisSession::new(poly);
        let box_role = vec!["Box".to_string()];
        let eq_role = vec!["Eq".to_string()];
        let list_path = vec!["list".to_string()];
        let item = session.infer.fresh_type_var_at(TypeLevel::root());
        let member_root = session.infer.fresh_type_var_at(TypeLevel::root().child());

        session.role_impls.insert(RoleImplCandidate {
            impl_def: Some(impl_def),
            role: box_role.clone(),
            inputs: vec![role_unary_con_var_arg(&mut session.infer, list_path, item)],
            associated: Vec::new(),
            prerequisites: Vec::new(),
        });
        session.register_role_impl_member(member, impl_def);
        session.roles.insert(
            member,
            RoleConstraint {
                role: eq_role.clone(),
                inputs: vec![role_var_arg(&mut session.infer, item)],
                associated: Vec::new(),
            },
        );
        let root_lower = session.infer.alloc_pos(Pos::Var(item));
        let root_upper = session.infer.alloc_neg(Neg::Var(member_root));
        session.infer.subtype(root_lower, root_upper);

        session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
            def: member,
            root: member_root,
        }));
        session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: member }));
        session.drain_work();

        let candidates = session.role_impls.candidates(&box_role);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].prerequisites.len(), 1);
        assert_eq!(candidates[0].prerequisites[0].role, eq_role);
        assert!(matches!(
            session
                .infer
                .constraints()
                .types()
                .pos(candidates[0].prerequisites[0].inputs[0].lower),
            Pos::Var(var) if *var == item
        ));
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
                    recursive_bounds: Vec::new(),
                    stack_quantifiers: Vec::new(),
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

        session.instantiate_use(DefId(99), def, use_value);

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
    fn instantiate_use_freshens_non_subtract_weight_ids() {
        let mut poly = PolyArena::new();
        let def = poly.defs.fresh();
        let quantified = TypeVar(42);
        let source_subtract = SubtractId(99);
        let inner = poly.typ.alloc_pos(Pos::Var(quantified));
        let predicate = poly.typ.alloc_pos(Pos::NonSubtract(inner, source_subtract));
        poly.defs.set(
            def,
            Def::Let {
                vis: Vis::My,
                scheme: Some(Scheme {
                    quantifiers: vec![quantified],
                    role_predicates: Vec::new(),
                    recursive_bounds: Vec::new(),
                    stack_quantifiers: Vec::new(),
                    predicate,
                    subtracts: vec![SchemeSubtractFact {
                        var: quantified,
                        id: source_subtract,
                        subtractability: Subtractability::Empty,
                    }],
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

        session.instantiate_use(DefId(99), def, use_value);

        let use_bounds = session
            .infer
            .constraints()
            .bounds()
            .of(use_value)
            .expect("use value should receive instantiated lower bound");
        let (fresh_var, fresh_subtract) = use_bounds
            .lowers()
            .iter()
            .find_map(
                |bound| match session.infer.constraints().types().pos(bound.pos) {
                    Pos::Var(var) if !bound.weights.left.is_empty() => {
                        Some((*var, bound.weights.left.iter().next().unwrap()))
                    }
                    _ => None,
                },
            )
            .expect("non-subtract should add a fresh left weight to the instantiated bound");
        assert_ne!(fresh_var, quantified);
        assert_ne!(fresh_subtract, source_subtract);
        assert!(
            session
                .infer
                .constraints()
                .subtracts()
                .facts(fresh_var)
                .iter()
                .any(|fact| fact.id == fresh_subtract
                    && matches!(fact.subtractability, Subtractability::Empty))
        );
    }

    #[test]
    fn instantiate_use_restores_recursive_bounds_for_fresh_quantifier() {
        let mut poly = PolyArena::new();
        let def = poly.defs.fresh();
        let quantified = TypeVar(42);
        let predicate = poly.typ.alloc_pos(Pos::Var(quantified));
        let int = poly.typ.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
        let top = poly.typ.alloc_neg(Neg::Top);
        let bounds = poly.typ.alloc_neu(Neu::Bounds(int, quantified, top));
        poly.defs.set(
            def,
            Def::Let {
                vis: Vis::My,
                scheme: Some(Scheme {
                    quantifiers: vec![quantified],
                    role_predicates: Vec::new(),
                    recursive_bounds: vec![SchemeRecursiveBound {
                        var: quantified,
                        bounds,
                    }],
                    stack_quantifiers: Vec::new(),
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

        session.instantiate_use(DefId(99), def, use_value);

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
        let fresh_bounds = session
            .infer
            .constraints()
            .bounds()
            .of(fresh)
            .expect("recursive bounds should be restored onto the fresh var");
        assert!(fresh_bounds.lowers().iter().any(|bound| matches!(
            session.infer.constraints().types().pos(bound.pos),
            Pos::Con(path, args) if path.len() == 1 && path[0] == "int" && args.is_empty()
        )));
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
            impl_def: None,
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
            impl_def: None,
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
            impl_def: None,
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
            impl_def: None,
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
            impl_def: None,
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
            impl_def: None,
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
            impl_def: None,
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
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
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
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
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
