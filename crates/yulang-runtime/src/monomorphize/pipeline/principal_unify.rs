use super::*;
use crate::types::{
    BoundsChoice, TypeChoice, choose_bounds_type, choose_core_type, contains_non_runtime_type,
    core_type_contains_unknown, core_type_is_imprecise_runtime_slot, core_type_is_never,
    core_types_compatible, effect_compatible, effect_paths, effect_paths_match,
    insert_exact_projected_substitution, needs_runtime_coercion,
    normalize_principal_elaboration_plan_with_role_impls, project_closed_substitutions_from_type,
    project_closed_substitutions_from_type_bounds, project_runtime_hir_type_with_vars,
    project_runtime_type_with_vars, runtime_core_type, runtime_type_contains_unknown,
    substitute_bounds, type_compatible, type_is_effect_like,
};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

mod effect_projection;
mod local_context;
mod type_projection;

use effect_projection::{
    effect_payload_type_for_operation, merge_effects,
    project_effect_payload_substitutions_from_expr,
};
use local_context::{
    LocalUseContextScope, collect_block_local_use_contexts, insert_local_use_context,
    local_use_context_scope_into_contexts, merge_local_use_contexts,
};
use type_projection::{principal_rewrite_apply_type, principal_rewrite_type_from_kind};

pub(super) fn principal_unify_module_profiled(
    module: Module,
) -> (Module, SubstitutionSpecializeProfile) {
    PrincipalUnifier::new(module, true).run()
}

pub(super) fn principal_unify_module(module: Module) -> Module {
    PrincipalUnifier::new(module, false).run().0
}

struct PrincipalUnifier {
    module: Module,
    collect_profile: bool,
    bindings_by_path: HashMap<typed_ir::Path, Binding>,
    generic_bindings: HashSet<typed_ir::Path>,
    required_vars_by_path: HashMap<typed_ir::Path, BTreeSet<typed_ir::TypeVar>>,
    role_impls: HashMap<typed_ir::Name, Vec<Binding>>,
    role_associated_impls: Vec<typed_ir::RoleImplGraphNode>,
    specializations: HashMap<String, typed_ir::Path>,
    root_specializations: HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    module_specializations: HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    role_method_rewrites: HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    emitted: Vec<Binding>,
    emitted_by_path: HashMap<typed_ir::Path, Binding>,
    handler_specialization_paths: HashSet<typed_ir::Path>,
    pending_specializations: VecDeque<PendingPrincipalSpecialization>,
    active_specializations: Vec<ActivePrincipalSpecialization>,
    local_use_contexts: Vec<LocalUseContextScope>,
    local_value_contexts: Vec<BTreeMap<typed_ir::Name, RuntimeType>>,
    next_index: usize,
    stats: HashMap<&'static str, usize>,
    timings: HashMap<&'static str, Duration>,
    target_skips: HashMap<typed_ir::Path, HashMap<&'static str, usize>>,
    target_missing_vars: HashMap<typed_ir::Path, HashMap<typed_ir::TypeVar, usize>>,
    target_rewrites: HashMap<typed_ir::Path, PrincipalRewriteTargetProfile>,
    rewrite_contexts: Vec<&'static str>,
    incomplete_plan_cache: HashMap<IncompletePrincipalPlanKey, CachedIncompletePrincipalPlan>,
    incomplete_plan_targets: HashSet<typed_ir::Path>,
    initial_reachable_bindings: HashSet<typed_ir::Path>,
    rewritten_template_bindings: HashSet<typed_ir::Path>,
    suppress_partial_apply_rewrite_depth: u32,
    never_effect_ops: HashSet<typed_ir::Path>,
}

#[derive(Debug, Clone)]
struct ActivePrincipalSpecialization {
    target: typed_ir::Path,
    substitutions: BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    path: typed_ir::Path,
    handler_plan: Option<HandlerAdapterPlan>,
    input_shapes: Option<Vec<typed_ir::Type>>,
    output_shape: Option<typed_ir::Type>,
}

struct PendingPrincipalSpecialization {
    original: Binding,
    substitutions: BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    handler_plan: Option<HandlerAdapterPlan>,
    input_shapes: Option<Vec<typed_ir::Type>>,
    output_shape: Option<typed_ir::Type>,
    path: typed_ir::Path,
}

struct PrincipalCallSpecialization {
    substitutions: BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    input_shapes: Vec<typed_ir::Type>,
    output_shape: Option<typed_ir::Type>,
    handler_plan: Option<HandlerAdapterPlan>,
    call_callee_ty: typed_ir::Type,
    final_arg_effect: Option<typed_ir::Type>,
}

struct CompletedPrincipalPlan {
    plan: typed_ir::PrincipalElaborationPlan,
    completed_with_internal_missing_substitutions: bool,
}

#[derive(Debug, Clone)]
struct CachedIncompletePrincipalPlan;

#[derive(Debug, Clone, Default)]
struct PrincipalRewriteTargetProfile {
    total_apply_visits: usize,
    rewrites: usize,
    cached_incomplete: usize,
    incomplete: usize,
    max_specialization_depth: usize,
    contexts: HashMap<&'static str, usize>,
    phases: HashMap<&'static str, Duration>,
    expr_kinds: HashMap<&'static str, PrincipalRewriteExprKindProfile>,
}

#[derive(Debug, Clone, Default)]
struct PrincipalRewriteExprKindProfile {
    count: usize,
    duration: Duration,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct IncompletePrincipalPlanKey {
    target: typed_ir::Path,
    arg_types: Vec<RuntimeType>,
    result_type: RuntimeType,
    result_context: Option<typed_ir::TypeBounds>,
    active_context_substitutions: Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
}

impl PrincipalUnifier {
    fn new(module: Module, collect_profile: bool) -> Self {
        let initial_reachable_bindings = root_reachable_binding_paths(&module);
        let required_vars_by_path = module
            .bindings
            .iter()
            .map(|binding| (binding.name.clone(), binding_required_vars(binding)))
            .collect::<HashMap<_, _>>();
        let bindings_by_path = module
            .bindings
            .iter()
            .filter(|binding| {
                initial_reachable_bindings.contains(&binding.name)
                    || required_vars_by_path
                        .get(&binding.name)
                        .is_some_and(|vars| !vars.is_empty())
            })
            .map(|binding| (binding.name.clone(), binding.clone()))
            .collect::<HashMap<_, _>>();
        let generic_bindings = module
            .bindings
            .iter()
            .filter(|binding| {
                required_vars_by_path
                    .get(&binding.name)
                    .is_some_and(|vars| !vars.is_empty())
            })
            .map(|binding| binding.name.clone())
            .collect::<HashSet<_>>();
        let role_impls = principal_unify_role_impls(&module);
        let role_associated_impls = module.role_impls.clone();
        let module_specializations = module_specializations_by_original(&module);
        let never_effect_ops = collect_never_effect_ops(&module);
        let next_index = next_principal_unify_index(&module);
        Self {
            module,
            collect_profile,
            bindings_by_path,
            generic_bindings,
            required_vars_by_path,
            role_impls,
            role_associated_impls,
            specializations: HashMap::new(),
            root_specializations: HashMap::new(),
            module_specializations,
            role_method_rewrites: HashMap::new(),
            emitted: Vec::new(),
            emitted_by_path: HashMap::new(),
            handler_specialization_paths: HashSet::new(),
            pending_specializations: VecDeque::new(),
            active_specializations: Vec::new(),
            local_use_contexts: Vec::new(),
            local_value_contexts: Vec::new(),
            next_index,
            stats: HashMap::new(),
            timings: HashMap::new(),
            target_skips: HashMap::new(),
            target_missing_vars: HashMap::new(),
            target_rewrites: HashMap::new(),
            rewrite_contexts: Vec::new(),
            incomplete_plan_cache: HashMap::new(),
            incomplete_plan_targets: HashSet::new(),
            initial_reachable_bindings,
            rewritten_template_bindings: HashSet::new(),
            suppress_partial_apply_rewrite_depth: 0,
            never_effect_ops,
        }
    }

    fn run(mut self) -> (Module, SubstitutionSpecializeProfile) {
        let mut module = std::mem::replace(&mut self.module, empty_module());
        let root_bindings = module
            .roots
            .iter()
            .filter_map(|root| match root {
                Root::Binding(path) => Some(path.clone()),
                Root::Expr(_) => None,
            })
            .collect::<HashSet<_>>();
        let started = self.profile_timer();
        let mut root_exprs = Vec::with_capacity(module.root_exprs.len());
        for expr in module.root_exprs {
            let step = self.profile_timer();
            let expr = refresh_local_expr_types(expr);
            self.finish_profile_timer("root-refresh-before-rewrite", step);
            let step = self.profile_timer();
            self.push_rewrite_context("root");
            let expr = self.rewrite_expr(expr, None);
            self.pop_rewrite_context();
            self.finish_profile_timer("root-rewrite", step);
            let step = self.profile_timer();
            root_exprs.push(project_runtime_expr_types(expr));
            self.finish_profile_timer("root-project", step);
        }
        module.root_exprs = root_exprs;
        self.finish_profile_timer("rewrite-root-exprs", started);
        let started = self.profile_timer();
        self.settle_pending_specializations();
        self.finish_profile_timer("process-root-specialization-requests", started);
        let started = self.profile_timer();
        let mut bindings = Vec::with_capacity(module.bindings.len());
        for binding in module.bindings {
            if !self.binding_body_should_be_rewritten(&binding, &root_bindings) {
                bindings.push(binding);
                continue;
            }
            let body_context = Self::binding_body_runtime_context(&binding);
            let step = self.profile_timer();
            let body = refresh_local_expr_types(binding.body);
            self.finish_profile_timer("binding-refresh-before-rewrite", step);
            let step = self.profile_timer();
            self.push_rewrite_context("binding");
            let body = self.rewrite_expr(body, body_context);
            self.pop_rewrite_context();
            self.finish_profile_timer("binding-rewrite", step);
            let step = self.profile_timer();
            let body = project_runtime_expr_types(body);
            self.finish_profile_timer("binding-project", step);
            bindings.push(Binding { body, ..binding });
        }
        module.bindings = bindings;
        self.finish_profile_timer("rewrite-bindings", started);
        let started = self.profile_timer();
        self.settle_pending_specializations();
        self.finish_profile_timer("process-binding-specialization-requests", started);
        let started = self.profile_timer();
        self.flush_emitted_specializations(&mut module);
        self.finish_profile_timer("flush-emitted-specializations", started);
        let started = self.profile_timer();
        self.rewrite_surviving_template_bindings(&mut module);
        self.finish_profile_timer("rewrite-surviving-template-bindings", started);
        let started = self.profile_timer();
        self.settle_flushed_specialization_refs(&mut module);
        self.finish_profile_timer("flush-final-specialization-refs", started);
        let started = self.profile_timer();
        normalize_never_effect_join_arms(&mut module, &self.never_effect_ops);
        self.finish_profile_timer("normalize-never-effect-join-arms", started);
        let profile = self.finish_profile();
        (module, profile)
    }

    fn flush_emitted_specializations(&mut self, module: &mut Module) {
        let emitted = std::mem::take(&mut self.emitted);
        if !emitted.is_empty() {
            let emitted_paths = emitted
                .iter()
                .map(|binding| binding.name.clone())
                .collect::<HashSet<_>>();
            module
                .bindings
                .retain(|binding| !emitted_paths.contains(&binding.name));
            module.bindings.extend(emitted);
        }
        add_single_specialization_aliases(module, &self.root_specializations);
        rewrite_contextual_specialization_refs(module, &self.module_specializations);
        rewrite_single_specialization_refs(module, &self.module_specializations);
        remove_specialized_generic_originals(module, &self.root_specializations);
        module.roots = module
            .roots
            .clone()
            .into_iter()
            .map(|root| self.rewrite_root_binding(root))
            .collect();
    }

    fn settle_flushed_specialization_refs(&mut self, module: &mut Module) {
        for _ in 0..8 {
            self.settle_pending_specializations();
            if !self.emitted.is_empty() {
                self.flush_emitted_specializations(module);
            }
            if !self.rewrite_flushed_specialization_bodies(module) {
                return;
            }
        }
    }

    fn rewrite_flushed_specialization_bodies(&mut self, module: &mut Module) -> bool {
        let mut changed = false;
        let candidate_paths = self.flushed_specialization_rewrite_candidate_paths();
        for binding in &mut module.bindings {
            if !binding.type_params.is_empty() {
                continue;
            }
            if !binding_body_has_principal_rewrite_candidate(&binding.body, &candidate_paths) {
                continue;
            }
            let original_body = binding.body.clone();
            let original_ty = original_body.ty.clone();
            let body_context = Self::binding_body_runtime_context(binding);
            let body = refresh_local_expr_types(original_body.clone());
            self.push_rewrite_context("flushed-specialization");
            let body = self.rewrite_expr(body, body_context);
            self.pop_rewrite_context();
            let body = retag_runtime_expr_spine_type(project_runtime_expr_types(body), original_ty);
            if body == original_body {
                continue;
            }
            self.bump("principal-unify-rewrite-flushed-specialization");
            binding.body = body;
            self.emitted_by_path
                .insert(binding.name.clone(), binding.clone());
            changed = true;
        }
        changed
    }

    fn flushed_specialization_rewrite_candidate_paths(&self) -> HashSet<typed_ir::Path> {
        let mut paths = self
            .generic_bindings
            .iter()
            .cloned()
            .collect::<HashSet<_>>();
        extend_specialization_rewrite_candidate_paths(&mut paths, &self.root_specializations);
        extend_specialization_rewrite_candidate_paths(&mut paths, &self.role_method_rewrites);
        extend_specialization_rewrite_candidate_paths(&mut paths, &self.module_specializations);
        paths.extend(self.emitted_by_path.keys().cloned());
        paths
    }

    fn register_module_specialization(&mut self, path: &typed_ir::Path) {
        let Some(original) = unspecialized_path(path) else {
            return;
        };
        let entry = self.module_specializations.entry(original).or_default();
        if !entry.contains(path) {
            entry.push(path.clone());
        }
    }

    fn rewrite_surviving_template_bindings(&mut self, module: &mut Module) {
        loop {
            let reachable = root_reachable_binding_paths(module);
            let templates = module
                .bindings
                .iter()
                .filter(|binding| reachable.contains(&binding.name))
                .filter(|binding| {
                    self.required_vars_by_path
                        .get(&binding.name)
                        .is_some_and(|vars| !vars.is_empty())
                })
                .filter(|binding| !self.rewritten_template_bindings.contains(&binding.name))
                .map(|binding| binding.name.clone())
                .collect::<Vec<_>>();
            if templates.is_empty() {
                return;
            }
            for name in templates {
                let Some(index) = module
                    .bindings
                    .iter()
                    .position(|binding| binding.name == name)
                else {
                    continue;
                };
                self.bump("principal-unify-rewrite-surviving-template-binding");
                self.rewritten_template_bindings.insert(name);
                let body_context = Self::binding_body_runtime_context(&module.bindings[index]);
                let body = module.bindings[index].body.clone();
                let body = refresh_local_expr_types(body);
                self.push_rewrite_context("surviving-template");
                let body = self.rewrite_expr(body, body_context);
                self.pop_rewrite_context();
                module.bindings[index].body = project_runtime_expr_types(body);
            }
            self.process_pending_specializations();
            self.flush_emitted_specializations(module);
        }
    }

    fn binding_body_should_be_rewritten(
        &mut self,
        binding: &Binding,
        root_bindings: &HashSet<typed_ir::Path>,
    ) -> bool {
        if !self.initial_reachable_bindings.contains(&binding.name) {
            return false;
        }
        if root_bindings.contains(&binding.name) {
            return true;
        }
        if self
            .required_vars_by_path
            .get(&binding.name)
            .is_some_and(|vars| vars.is_empty())
        {
            return true;
        }
        self.bump("principal-unify-skip-template-binding");
        false
    }

    fn bump(&mut self, key: &'static str) {
        if !self.collect_profile {
            return;
        }
        *self.stats.entry(key).or_default() += 1;
    }

    fn add_timing(&mut self, key: &'static str, duration: Duration) {
        if !self.collect_profile {
            return;
        }
        *self.timings.entry(key).or_default() += duration;
    }

    fn profile_timer(&self) -> Option<Instant> {
        self.collect_profile.then(Instant::now)
    }

    fn finish_profile_timer(&mut self, key: &'static str, started: Option<Instant>) {
        if let Some(started) = started {
            self.add_timing(key, started.elapsed());
        }
    }

    fn bump_skip(&mut self, target: &typed_ir::Path, reason: &'static str) {
        debug_principal_unify_skip(target, reason);
        if !self.collect_profile {
            return;
        }
        self.bump(reason);
        *self
            .target_skips
            .entry(target.clone())
            .or_default()
            .entry(reason)
            .or_default() += 1;
    }

    fn generic_binding(&self, path: &typed_ir::Path) -> Option<&Binding> {
        self.generic_bindings
            .contains(path)
            .then(|| self.bindings_by_path.get(path))
            .flatten()
    }

    fn emitted_binding(&self, path: &typed_ir::Path) -> Option<&Binding> {
        self.emitted_by_path.get(path)
    }

    fn binding_by_path_or_emitted(&self, path: &typed_ir::Path) -> Option<&Binding> {
        self.emitted_binding(path)
            .or_else(|| self.bindings_by_path.get(path))
    }

    fn required_vars_for_binding(&self, binding: &Binding) -> BTreeSet<typed_ir::TypeVar> {
        self.required_vars_by_path
            .get(&binding.name)
            .cloned()
            .unwrap_or_else(|| binding_required_vars(binding))
    }

    fn bump_missing_vars(
        &mut self,
        target: &typed_ir::Path,
        binding: &Binding,
        substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ) {
        if !self.collect_profile {
            return;
        }
        let entry = self.target_missing_vars.entry(target.clone()).or_default();
        for var in missing_required_vars(binding, substitutions) {
            *entry.entry(var).or_default() += 1;
        }
    }

    fn bump_missing_var_list(&mut self, target: &typed_ir::Path, vars: &[typed_ir::TypeVar]) {
        if !self.collect_profile || vars.is_empty() {
            return;
        }
        let entry = self.target_missing_vars.entry(target.clone()).or_default();
        for var in vars {
            *entry.entry(var.clone()).or_default() += 1;
        }
    }

    fn push_rewrite_context(&mut self, context: &'static str) {
        self.rewrite_contexts.push(context);
    }

    fn pop_rewrite_context(&mut self) {
        self.rewrite_contexts.pop();
    }

    fn current_rewrite_context(&self) -> &'static str {
        self.rewrite_contexts.last().copied().unwrap_or("unknown")
    }

    fn record_target_apply_visit(&mut self, target: &typed_ir::Path) {
        if !self.collect_profile {
            return;
        }
        let context = self.current_rewrite_context();
        let depth = self.active_specializations.len();
        let target = self.target_rewrites.entry(target.clone()).or_default();
        target.total_apply_visits += 1;
        target.max_specialization_depth = target.max_specialization_depth.max(depth);
        *target.contexts.entry(context).or_default() += 1;
    }

    fn record_target_rewrite(&mut self, target: &typed_ir::Path) {
        if !self.collect_profile {
            return;
        }
        self.target_rewrites
            .entry(target.clone())
            .or_default()
            .rewrites += 1;
    }

    fn record_target_cached_incomplete(&mut self, target: &typed_ir::Path) {
        if !self.collect_profile {
            return;
        }
        self.target_rewrites
            .entry(target.clone())
            .or_default()
            .cached_incomplete += 1;
    }

    fn record_target_incomplete(&mut self, target: &typed_ir::Path) {
        if !self.collect_profile {
            return;
        }
        self.target_rewrites
            .entry(target.clone())
            .or_default()
            .incomplete += 1;
    }

    fn record_target_phase_timing(
        &mut self,
        target: &typed_ir::Path,
        phase: &'static str,
        started: Option<Instant>,
    ) {
        let Some(started) = started else {
            return;
        };
        if !self.collect_profile {
            return;
        }
        *self
            .target_rewrites
            .entry(target.clone())
            .or_default()
            .phases
            .entry(phase)
            .or_default() += started.elapsed();
    }

    fn record_target_expr_kind_timing(
        &mut self,
        target: &typed_ir::Path,
        kind: &'static str,
        duration: Duration,
    ) {
        if !self.collect_profile {
            return;
        }
        let entry = self
            .target_rewrites
            .entry(target.clone())
            .or_default()
            .expr_kinds
            .entry(kind)
            .or_default();
        entry.count += 1;
        entry.duration += duration;
    }

    fn enter_callee_rewrite(&mut self) {
        self.suppress_partial_apply_rewrite_depth += 1;
    }

    fn leave_callee_rewrite(&mut self) {
        self.suppress_partial_apply_rewrite_depth =
            self.suppress_partial_apply_rewrite_depth.saturating_sub(1);
    }

    fn rewrite_expr_with_visible_partial_applications(
        &mut self,
        expr: Expr,
        result_context: Option<typed_ir::TypeBounds>,
    ) -> Expr {
        let saved = self.suppress_partial_apply_rewrite_depth;
        self.suppress_partial_apply_rewrite_depth = 0;
        let rewritten = self.rewrite_expr(expr, result_context);
        self.suppress_partial_apply_rewrite_depth = saved;
        rewritten
    }

    fn should_skip_partial_callee_rewrite(
        &mut self,
        target: &typed_ir::Path,
        args_len: usize,
    ) -> bool {
        if self.suppress_partial_apply_rewrite_depth == 0 || !self.generic_bindings.contains(target)
        {
            return false;
        }
        let Some(binding) = self.bindings_by_path.get(target) else {
            return false;
        };
        if args_len >= core_fun_arity(&binding.scheme.body) {
            return false;
        }
        self.bump("principal-unify-skip-partial-callee-rewrite");
        true
    }

    fn rewrite_root_binding(&self, root: Root) -> Root {
        let Root::Binding(path) = root else {
            return root;
        };
        let Some(specialized) = self.root_specializations.get(&path) else {
            return Root::Binding(path);
        };
        if specialized.len() != 1 {
            return Root::Binding(path);
        }
        Root::Binding(specialized.first().cloned().unwrap_or(path))
    }

    fn finish_profile(self) -> SubstitutionSpecializeProfile {
        let mut target_missing_vars = self.target_missing_vars;
        let mut target_skips = self
            .target_skips
            .into_iter()
            .map(|(target, reasons)| {
                let mut reasons = reasons
                    .into_iter()
                    .map(|(reason, count)| SubstitutionSpecializeSkipCount { reason, count })
                    .collect::<Vec<_>>();
                reasons.sort_by(|left, right| {
                    right
                        .count
                        .cmp(&left.count)
                        .then_with(|| left.reason.cmp(right.reason))
                });
                let mut missing_vars = target_missing_vars
                    .remove(&target)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|(var, count)| SubstitutionSpecializeMissingVarCount { var, count })
                    .collect::<Vec<_>>();
                missing_vars.sort_by(|left, right| {
                    right
                        .count
                        .cmp(&left.count)
                        .then_with(|| left.var.0.cmp(&right.var.0))
                });
                SubstitutionSpecializeTargetSkips {
                    target,
                    survives_final_prune: None,
                    actionable: reasons
                        .iter()
                        .any(|reason| !principal_unify_skip_reason_benign(reason.reason)),
                    reasons,
                    missing_vars,
                    no_complete_causes: Vec::new(),
                }
            })
            .collect::<Vec<_>>();
        target_skips.sort_by(|left, right| {
            let left_total = left
                .reasons
                .iter()
                .map(|reason| reason.count)
                .sum::<usize>();
            let right_total = right
                .reasons
                .iter()
                .map(|reason| reason.count)
                .sum::<usize>();
            right_total
                .cmp(&left_total)
                .then_with(|| canonical_path(&left.target).cmp(&canonical_path(&right.target)))
        });
        let mut target_rewrites = self
            .target_rewrites
            .into_iter()
            .map(|(target, profile)| {
                let mut contexts = profile
                    .contexts
                    .into_iter()
                    .map(
                        |(context, count)| SubstitutionSpecializeRewriteContextCount {
                            context,
                            count,
                        },
                    )
                    .collect::<Vec<_>>();
                contexts.sort_by(|left, right| {
                    right
                        .count
                        .cmp(&left.count)
                        .then_with(|| left.context.cmp(right.context))
                });
                let mut phases = profile
                    .phases
                    .into_iter()
                    .map(
                        |(phase, duration)| SubstitutionSpecializeRewritePhaseTiming {
                            phase,
                            duration,
                        },
                    )
                    .collect::<Vec<_>>();
                phases.sort_by(|left, right| {
                    right
                        .duration
                        .cmp(&left.duration)
                        .then_with(|| left.phase.cmp(right.phase))
                });
                let mut expr_kinds = profile
                    .expr_kinds
                    .into_iter()
                    .map(
                        |(kind, profile)| SubstitutionSpecializeRewriteExprKindTiming {
                            kind,
                            count: profile.count,
                            duration: profile.duration,
                        },
                    )
                    .collect::<Vec<_>>();
                expr_kinds.sort_by(|left, right| {
                    right
                        .duration
                        .cmp(&left.duration)
                        .then_with(|| right.count.cmp(&left.count))
                        .then_with(|| left.kind.cmp(right.kind))
                });
                SubstitutionSpecializeTargetRewrites {
                    target,
                    total_apply_visits: profile.total_apply_visits,
                    rewrites: profile.rewrites,
                    cached_incomplete: profile.cached_incomplete,
                    incomplete: profile.incomplete,
                    max_specialization_depth: profile.max_specialization_depth,
                    contexts,
                    phases,
                    expr_kinds,
                }
            })
            .collect::<Vec<_>>();
        target_rewrites.sort_by(|left, right| {
            right
                .total_apply_visits
                .cmp(&left.total_apply_visits)
                .then_with(|| canonical_path(&left.target).cmp(&canonical_path(&right.target)))
        });
        SubstitutionSpecializeProfile {
            stats: self.stats,
            timings: self.timings,
            target_skips,
            target_inferences: Vec::new(),
            target_rewrites,
        }
    }

    fn rewrite_expr(&mut self, expr: Expr, result_context: Option<typed_ir::TypeBounds>) -> Expr {
        if !self.collect_profile || !principal_rewrite_expr_kind_profile_enabled() {
            return self.rewrite_expr_inner(expr, result_context);
        }
        let kind = principal_rewrite_expr_kind_name(&expr.kind);
        let active_target = self
            .active_specializations
            .last()
            .map(|active| active.target.clone());
        self.bump(principal_rewrite_expr_kind_count_key(kind));
        let started = Instant::now();
        let rewritten = self.rewrite_expr_inner(expr, result_context);
        let duration = started.elapsed();
        self.add_timing(principal_rewrite_expr_kind_timing_key(kind), duration);
        if let Some(target) = active_target {
            self.record_target_expr_kind_timing(&target, kind, duration);
        }
        rewritten
    }

    fn rewrite_expr_inner(
        &mut self,
        expr: Expr,
        result_context: Option<typed_ir::TypeBounds>,
    ) -> Expr {
        let mut ty = expr.ty;
        let kind = match expr.kind {
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            } => {
                return self.rewrite_apply_expr(
                    ty,
                    *callee,
                    *arg,
                    evidence,
                    instantiation,
                    result_context.as_ref(),
                );
            }
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            } => {
                let context_ty = runtime_context_function_type(result_context.as_ref());
                let had_context = context_ty.is_some();
                if let Some(context_ty) = context_ty {
                    ty = context_ty;
                }
                let body = if had_context {
                    refresh_lambda_body_local_types(
                        ty.clone(),
                        param.clone(),
                        param_effect_annotation.clone(),
                        param_function_allowed_effects.clone(),
                        *body,
                    )
                } else {
                    *body
                };
                let body_context = runtime_lambda_return_value_context(&ty);
                self.local_use_contexts
                    .push(LocalUseContextScope::default());
                self.push_local_value_type(param.clone(), lambda_param_runtime_type(&ty));
                let mut body = self.rewrite_expr(body, body_context);
                self.local_value_contexts.pop();
                let local_use_contexts = self
                    .local_use_contexts
                    .pop()
                    .map(local_use_context_scope_into_contexts)
                    .unwrap_or_default();
                if let Some(param_context) = local_use_contexts.get(&param)
                    && let Some(param_ty) = closed_type_from_bounds(Some(param_context))
                    && closed_slot_type_usable(&param_ty, false)
                    && let Some(updated_ty) = runtime_function_type_with_param(ty.clone(), param_ty)
                    && updated_ty != ty
                {
                    ty = updated_ty;
                    body = refresh_lambda_body_local_types(
                        ty.clone(),
                        param.clone(),
                        param_effect_annotation.clone(),
                        param_function_allowed_effects.clone(),
                        body,
                    );
                    let body_context = runtime_lambda_return_value_context(&ty);
                    self.push_local_value_type(param.clone(), lambda_param_runtime_type(&ty));
                    body = self.rewrite_expr(body, body_context);
                    self.local_value_contexts.pop();
                }
                ExprKind::Lambda {
                    param,
                    param_effect_annotation,
                    param_function_allowed_effects,
                    body: Box::new(body),
                }
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                evidence,
            } => {
                let branch_context = evidence
                    .as_ref()
                    .map(|evidence| {
                        typed_ir::TypeBounds::exact(contextual_join_result_type(
                            evidence.result.clone(),
                            result_context.as_ref(),
                        ))
                    })
                    .or(result_context.clone());
                ExprKind::If {
                    cond: Box::new(self.rewrite_expr(*cond, None)),
                    then_branch: Box::new(self.rewrite_expr(*then_branch, branch_context.clone())),
                    else_branch: Box::new(self.rewrite_expr(*else_branch, branch_context)),
                    evidence,
                }
            }
            ExprKind::Tuple(items) => {
                let item_contexts =
                    tuple_item_result_contexts(result_context.as_ref(), items.len());
                ExprKind::Tuple(
                    items
                        .into_iter()
                        .zip(item_contexts)
                        .map(|(item, item_context)| self.rewrite_expr(item, item_context))
                        .collect(),
                )
            }
            ExprKind::Record { fields, spread } => ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|field| RecordExprField {
                        name: field.name,
                        value: self.rewrite_expr(field.value, None),
                    })
                    .collect(),
                spread: spread.map(|spread| match spread {
                    RecordSpreadExpr::Head(expr) => {
                        RecordSpreadExpr::Head(Box::new(self.rewrite_expr(*expr, None)))
                    }
                    RecordSpreadExpr::Tail(expr) => {
                        RecordSpreadExpr::Tail(Box::new(self.rewrite_expr(*expr, None)))
                    }
                }),
            },
            ExprKind::Variant { tag, value } => ExprKind::Variant {
                tag,
                value: value.map(|value| Box::new(self.rewrite_expr(*value, None))),
            },
            ExprKind::Select { base, field } => ExprKind::Select {
                base: Box::new(self.rewrite_expr(*base, None)),
                field,
            },
            ExprKind::Match {
                scrutinee,
                arms,
                evidence,
            } => {
                let scrutinee_context = Some(typed_ir::TypeBounds::exact(runtime_core_type(
                    &scrutinee.ty,
                )));
                let result = contextual_join_result_type_with_arm_result(
                    evidence.result,
                    result_context.as_ref(),
                    visible_match_arm_result_type(&arms).as_ref(),
                );
                ty = RuntimeType::core(result.clone());
                let arm_context = Some(typed_ir::TypeBounds::exact(result.clone()));
                let scrutinee = self.rewrite_expr(*scrutinee, scrutinee_context);
                let scrutinee_ty = scrutinee.ty.clone();
                ExprKind::Match {
                    scrutinee: Box::new(scrutinee),
                    arms: arms
                        .into_iter()
                        .map(|arm| {
                            let pattern = self.rewrite_pattern_defaults(arm.pattern);
                            self.local_value_contexts.push(BTreeMap::new());
                            self.record_local_value_type_with_expected(&pattern, &scrutinee_ty);
                            let guard = arm.guard.map(|guard| self.rewrite_expr(guard, None));
                            let body = {
                                let body_context = self
                                    .expr_is_nullary_generic_var(&arm.body)
                                    .then(|| arm_context.clone())
                                    .flatten();
                                self.rewrite_expr(arm.body, body_context)
                            };
                            let body = self.adapt_join_body_never_effect(body, &result);
                            self.local_value_contexts.pop();
                            MatchArm {
                                pattern,
                                guard,
                                body,
                            }
                        })
                        .collect(),
                    evidence: JoinEvidence { result },
                }
            }
            ExprKind::Block { stmts, tail } => {
                let refreshed = project_runtime_expr_types(refresh_local_expr_types(Expr {
                    ty,
                    kind: ExprKind::Block { stmts, tail },
                }));
                return self.rewrite_refreshed_block_once(refreshed, result_context.as_ref());
            }
            ExprKind::Handle {
                body,
                arms,
                evidence,
                handler,
            } => {
                let result = contextual_join_result_type_with_arm_result(
                    evidence.result,
                    result_context.as_ref(),
                    visible_handle_arm_result_type(&arms).as_ref(),
                );
                ty = RuntimeType::core(result.clone());
                let arm_context = Some(typed_ir::TypeBounds::exact(result.clone()));
                let body = self.rewrite_expr(*body, None);
                let body = unwrap_handler_body_bind_here(body, &handler);
                let body = ensure_effectful_handler_body_thunk(body, &handler);
                ExprKind::Handle {
                    body: Box::new(body),
                    arms: arms
                        .into_iter()
                        .map(|arm| {
                            let payload = self.rewrite_pattern_defaults(arm.payload);
                            let payload_context = handle_arm_payload_runtime_type(
                                &handler,
                                &arm.effect,
                            )
                            .or_else(|| {
                                wildcard_payload_unit_context(&payload).map(RuntimeType::core)
                            });
                            let payload = match &payload_context {
                                Some(payload_context) => {
                                    refresh_pattern_value_local_types(payload, payload_context)
                                }
                                None => payload,
                            };
                            self.local_value_contexts.push(BTreeMap::new());
                            if let Some(payload_context) = &payload_context {
                                self.record_local_value_type_with_expected(
                                    &payload,
                                    payload_context,
                                );
                            } else {
                                self.record_local_value_type(&payload);
                            }
                            let resume = arm.resume.map(|resume| {
                                refresh_resume_binding_return_from_context(
                                    resume,
                                    arm_context.as_ref(),
                                )
                            });
                            if let Some(resume) = &resume {
                                self.insert_local_value_type(
                                    resume.name.clone(),
                                    resume.ty.clone(),
                                );
                            }
                            let guard = arm.guard.map(|guard| self.rewrite_expr(guard, None));
                            let body = self.rewrite_expr(arm.body, arm_context.clone());
                            let body = self.adapt_join_body_never_effect(body, &result);
                            self.local_value_contexts.pop();
                            HandleArm {
                                effect: arm.effect,
                                payload,
                                resume,
                                guard,
                                body,
                            }
                        })
                        .collect(),
                    evidence: JoinEvidence { result },
                    handler,
                }
            }
            ExprKind::BindHere { expr } => {
                if runtime_type_contains_unknown(&ty)
                    && let Some(context) = closed_type_from_bounds(result_context.as_ref())
                {
                    ty = RuntimeType::core(context);
                }
                let expr = self.rewrite_expr(*expr, result_context.clone());
                let expr =
                    self.adapt_never_effect_thunk_from_context(expr, result_context.as_ref());
                let expr = refine_bind_here_inner_thunk_value_from_context(expr, result_context);
                if !matches!(expr.ty, RuntimeType::Thunk { .. }) {
                    return expr;
                }
                ExprKind::BindHere {
                    expr: Box::new(expr),
                }
            }
            ExprKind::Thunk {
                effect,
                value,
                expr,
            } => {
                let initial_value =
                    if let Some(context) = closed_type_from_bounds(result_context.as_ref()) {
                        RuntimeType::core(context)
                    } else {
                        match &ty {
                            RuntimeType::Thunk {
                                value: ty_value, ..
                            } => ty_value.as_ref().clone(),
                            _ => value,
                        }
                    };
                let value_context = typed_ir::TypeBounds::exact(runtime_core_type(&initial_value));
                let expr = self.rewrite_expr(*expr, Some(value_context));
                let value = if runtime_type_shape_usable(&expr.ty) {
                    expr.ty.clone()
                } else {
                    initial_value
                };
                ty = RuntimeType::thunk(effect.clone(), value.clone());
                ExprKind::Thunk {
                    effect,
                    value,
                    expr: Box::new(expr),
                }
            }
            ExprKind::LocalPushId { id, body } => {
                let body = self.rewrite_expr(*body, result_context);
                ty = body.ty.clone();
                ExprKind::LocalPushId {
                    id,
                    body: Box::new(body),
                }
            }
            ExprKind::AddId {
                id,
                allowed,
                active,
                thunk,
            } => {
                let thunk =
                    self.rewrite_expr_with_visible_partial_applications(*thunk, result_context);
                ty = thunk.ty.clone();
                ExprKind::AddId {
                    id,
                    allowed,
                    active,
                    thunk: Box::new(thunk),
                }
            }
            ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
                from,
                to,
                expr: Box::new(self.rewrite_expr(*expr, None)),
            },
            ExprKind::Pack { var, expr } => ExprKind::Pack {
                var,
                expr: Box::new(self.rewrite_expr(*expr, None)),
            },
            ExprKind::Var(path) => {
                let is_local = if let Some(local_ty) = self.local_value_type(&path) {
                    ty = local_ty;
                    true
                } else if let Some(binding_ty) = self.known_binding_runtime_type(&path) {
                    ty = binding_ty;
                    false
                } else {
                    // Plain monomorphic bindings never go through
                    // `emitted_by_path`, so a Var pointing at one used
                    // to keep its pre-monomorphize `Expr.ty`. If that
                    // type still carries TypeVar slots after
                    // substitution, fall back to the binding's own
                    // scheme body so the residual walker sees no var.
                    // Skip the fallback when the existing `ty` is
                    // already concrete because the scheme body is a
                    // plain core type and would strip any runtime-layer
                    // info (thunk shape, function arrow) the call site
                    // carries.
                    if hir_type_has_vars(&ty)
                        && let Some(binding_ty) = self.monomorphic_binding_type(&path)
                    {
                        ty = binding_ty;
                    }
                    false
                };
                self.record_local_var_context(&path, result_context.as_ref());
                if is_local {
                    return Expr {
                        ty,
                        kind: ExprKind::Var(path),
                    };
                }
                if self
                    .generic_binding(&path)
                    .is_some_and(|binding| core_fun_spine_exact(&binding.scheme.body, 1).is_none())
                    && let Some((specialized, ty)) = self.single_local_emitted_specialization(&path)
                {
                    return Expr::typed(ExprKind::Var(specialized), ty);
                }
                let inferred_context =
                    closed_runtime_value_type(&ty).map(typed_ir::TypeBounds::exact);
                let nullary_context = result_context.as_ref().or(inferred_context.as_ref());
                if let Some(rewritten) =
                    self.rewrite_nullary_generic_from_context(&path, nullary_context)
                {
                    return rewritten;
                }
                ExprKind::Var(path)
            }
            ExprKind::EffectOp(path) => {
                if let Some(binding_ty) = self.known_binding_runtime_type(&path) {
                    ty = binding_ty;
                } else if hir_type_has_vars(&ty)
                    && let Some(binding_ty) = self.monomorphic_binding_type(&path)
                {
                    ty = binding_ty;
                }
                ExprKind::EffectOp(path)
            }
            ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => expr.kind,
        };
        ty = principal_rewrite_type_from_kind(ty, &kind);
        Expr { ty, kind }
    }

    fn rewrite_apply_expr(
        &mut self,
        ty: RuntimeType,
        callee: Expr,
        arg: Expr,
        evidence: Option<typed_ir::ApplyEvidence>,
        instantiation: Option<TypeInstantiation>,
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> Expr {
        let callee_context = evidence
            .as_ref()
            .and_then(|evidence| evidence.expected_callee.clone());
        self.enter_callee_rewrite();
        let callee = self.rewrite_expr(callee, callee_context);
        self.leave_callee_rewrite();
        let callee = force_rebuilt_thunked_function_callee(callee);
        let arg_context = apply_argument_rewrite_context(&callee, evidence.as_ref());
        let arg = self.rewrite_expr(arg, arg_context);
        let instantiation = instantiation.and_then(|instantiation| {
            self.single_local_emitted_specialization(&instantiation.target)
                .is_none()
                .then_some(instantiation)
        });
        let expr = Expr {
            ty,
            kind: ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(arg),
                evidence,
                instantiation,
            },
        };
        let expr = refresh_apply_expr_type_from_callee(adapt_apply_argument_from_callee(expr));
        let expr = self
            .rewrite_apply_from_principal_plan(&expr, result_context)
            .unwrap_or(expr);
        let expr = refine_apply_expr_callee_input(expr);
        let expr = adapt_apply_result_from_evidence(expr, result_context);
        self.adapt_never_effect_op_result(expr, result_context)
    }

    fn adapt_never_effect_op_result(
        &self,
        expr: Expr,
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> Expr {
        let Some(expected) = closed_type_from_bounds(result_context) else {
            return expr;
        };
        if !closed_slot_type_usable(&expected, false) {
            return expr;
        }
        let Expr {
            ty,
            kind:
                ExprKind::Apply {
                    callee,
                    arg,
                    evidence,
                    instantiation,
                },
        } = expr
        else {
            return expr;
        };
        let ExprKind::EffectOp(path) = &callee.kind else {
            return Expr::typed(
                ExprKind::Apply {
                    callee,
                    arg,
                    evidence,
                    instantiation,
                },
                ty,
            );
        };
        if !self.never_effect_ops.contains(path) {
            return Expr::typed(
                ExprKind::Apply {
                    callee,
                    arg,
                    evidence,
                    instantiation,
                },
                ty,
            );
        }
        match ty {
            RuntimeType::Thunk { effect, .. } => Expr::typed(
                ExprKind::Apply {
                    callee,
                    arg,
                    evidence,
                    instantiation,
                },
                RuntimeType::thunk(effect, RuntimeType::core(expected)),
            ),
            other => Expr::typed(
                ExprKind::Apply {
                    callee,
                    arg,
                    evidence,
                    instantiation,
                },
                other,
            ),
        }
    }

    fn adapt_never_effect_thunk_from_context(
        &self,
        expr: Expr,
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> Expr {
        let Some(expected) = closed_type_from_bounds(result_context) else {
            return expr;
        };
        if !closed_slot_type_usable(&expected, false) {
            return expr;
        }
        let Expr { ty, kind } = expr;
        let RuntimeType::Thunk { effect, value } = ty else {
            return Expr::typed(kind, ty);
        };
        let ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } = kind
        else {
            return Expr::typed(kind, RuntimeType::thunk(effect, *value));
        };
        let is_never_effect = matches!(
            callee.kind,
            ExprKind::EffectOp(ref path) if self.never_effect_ops.contains(path)
        );
        let ty = if is_never_effect {
            RuntimeType::thunk(effect, RuntimeType::core(expected))
        } else {
            RuntimeType::thunk(effect, *value)
        };
        Expr::typed(
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            },
            ty,
        )
    }

    fn adapt_join_body_never_effect(&self, expr: Expr, result: &typed_ir::Type) -> Expr {
        self.adapt_expr_never_effect_to_type(expr, &RuntimeType::core(result.clone()))
    }

    fn adapt_expr_never_effect_to_type(&self, expr: Expr, expected: &RuntimeType) -> Expr {
        let Expr { ty, kind } = expr;
        match kind {
            ExprKind::BindHere { expr: inner } => {
                let inner = self.adapt_expr_never_effect_to_type(*inner, expected);
                let ty = match &inner.ty {
                    RuntimeType::Thunk { .. } if expr_is_never_effect_op_apply(&inner, self) => {
                        expected.clone()
                    }
                    RuntimeType::Thunk { value, .. } => value.as_ref().clone(),
                    _ => inner.ty.clone(),
                };
                Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(inner),
                    },
                    ty,
                )
            }
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            } => {
                let is_never_effect = matches!(
                    callee.kind,
                    ExprKind::EffectOp(ref path) if self.never_effect_ops.contains(path)
                );
                let ty = match (is_never_effect, ty) {
                    (true, RuntimeType::Thunk { effect, .. }) => {
                        RuntimeType::thunk(effect, expected.clone())
                    }
                    (_, ty) => ty,
                };
                Expr::typed(
                    ExprKind::Apply {
                        callee,
                        arg,
                        evidence,
                        instantiation,
                    },
                    ty,
                )
            }
            ExprKind::Block { stmts, tail } => {
                let tail = tail
                    .map(|tail| Box::new(self.adapt_expr_never_effect_to_type(*tail, expected)));
                let ty = tail.as_ref().map(|tail| tail.ty.clone()).unwrap_or(ty);
                Expr::typed(ExprKind::Block { stmts, tail }, ty)
            }
            kind => Expr::typed(kind, ty),
        }
    }

    fn record_local_var_context(
        &mut self,
        path: &typed_ir::Path,
        result_context: Option<&typed_ir::TypeBounds>,
    ) {
        let [name] = path.segments.as_slice() else {
            return;
        };
        let Some(context) = closed_type_from_bounds(result_context) else {
            return;
        };
        let Some(scope) = self.local_use_contexts.last_mut() else {
            return;
        };
        insert_local_use_context(&mut scope.uses, &mut scope.conflicts, name.clone(), context);
    }

    fn local_value_type(&self, path: &typed_ir::Path) -> Option<RuntimeType> {
        let [name] = path.segments.as_slice() else {
            return None;
        };
        self.local_value_contexts
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn record_local_value_type(&mut self, pattern: &Pattern) {
        let expected = pattern_runtime_type(pattern).clone();
        self.record_local_value_type_with_expected(pattern, &expected);
    }

    fn record_local_value_type_with_expected(&mut self, pattern: &Pattern, expected: &RuntimeType) {
        match pattern {
            Pattern::Bind { name, ty } => {
                self.insert_local_value_type(
                    name.clone(),
                    pattern_local_runtime_type(ty, expected),
                );
            }
            Pattern::Tuple { items, ty } => {
                for (index, item) in items.iter().enumerate() {
                    let item_expected = tuple_pattern_item_runtime_type(expected, ty, index)
                        .unwrap_or_else(|| pattern_runtime_type(item).clone());
                    self.record_local_value_type_with_expected(item, &item_expected);
                }
            }
            Pattern::List {
                prefix,
                spread,
                suffix,
                ty,
            } => {
                let item_expected = list_pattern_item_runtime_type(expected, ty);
                for item in prefix {
                    let expected = item_expected
                        .as_ref()
                        .unwrap_or_else(|| pattern_runtime_type(item));
                    self.record_local_value_type_with_expected(item, expected);
                }
                if let Some(spread) = spread {
                    self.record_local_value_type_with_expected(spread, expected);
                }
                for item in suffix {
                    let expected = item_expected
                        .as_ref()
                        .unwrap_or_else(|| pattern_runtime_type(item));
                    self.record_local_value_type_with_expected(item, expected);
                }
            }
            Pattern::Record { fields, spread, ty } => {
                for field in fields {
                    let field_expected =
                        record_pattern_field_runtime_type(expected, ty, &field.name)
                            .unwrap_or_else(|| pattern_runtime_type(&field.pattern).clone());
                    self.record_local_value_type_with_expected(&field.pattern, &field_expected);
                }
                match spread {
                    Some(RecordSpreadPattern::Head(pattern))
                    | Some(RecordSpreadPattern::Tail(pattern)) => {
                        self.record_local_value_type_with_expected(pattern, expected);
                    }
                    None => {}
                }
            }
            Pattern::Variant { tag, value, ty } => {
                if let Some(value) = value {
                    let value_expected = variant_pattern_payload_runtime_type(expected, ty, tag)
                        .unwrap_or_else(|| pattern_runtime_type(value).clone());
                    self.record_local_value_type_with_expected(value, &value_expected);
                }
            }
            Pattern::Or { left, right, .. } => {
                self.record_local_value_type_with_expected(left, expected);
                self.record_local_value_type_with_expected(right, expected);
            }
            Pattern::As { pattern, name, ty } => {
                self.record_local_value_type_with_expected(pattern, expected);
                self.insert_local_value_type(
                    name.clone(),
                    pattern_local_runtime_type(ty, expected),
                );
            }
            Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
        }
    }

    fn insert_local_value_type(&mut self, name: typed_ir::Name, ty: RuntimeType) {
        let Some(scope) = self.local_value_contexts.last_mut() else {
            return;
        };
        debug_principal_unify_local_value(&name, &ty);
        scope.insert(name, ty);
    }

    fn push_local_value_type(&mut self, name: typed_ir::Name, ty: Option<RuntimeType>) {
        let mut scope = BTreeMap::new();
        if let Some(ty) = ty {
            debug_principal_unify_local_value(&name, &ty);
            scope.insert(name, ty);
        }
        self.local_value_contexts.push(scope);
    }

    fn rewrite_stmt(&mut self, stmt: Stmt) -> Stmt {
        match stmt {
            Stmt::Let { pattern, value } => {
                let value_context = pattern_value_context(&pattern);
                let value = self.rewrite_expr(value, value_context);
                let pattern = self.rewrite_pattern_defaults(pattern);
                self.record_local_value_type(&pattern);
                Stmt::Let { pattern, value }
            }
            Stmt::Expr(expr) => Stmt::Expr(self.rewrite_expr(expr, None)),
            Stmt::Module { def, body } => {
                if let Some((specialized, ty)) = self.single_local_emitted_specialization(&def) {
                    return Stmt::Module {
                        def,
                        body: Expr::typed(ExprKind::Var(specialized), ty),
                    };
                }
                let body_context = self
                    .monomorphic_binding_type(&def)
                    .map(|ty| typed_ir::TypeBounds::exact(runtime_core_type(&ty)));
                let body = self.rewrite_expr(body, body_context);
                Stmt::Module { def, body }
            }
        }
    }

    fn rewrite_pattern_defaults(&mut self, pattern: Pattern) -> Pattern {
        match pattern {
            Pattern::Tuple { items, ty } => Pattern::Tuple {
                items: items
                    .into_iter()
                    .map(|item| self.rewrite_pattern_defaults(item))
                    .collect(),
                ty,
            },
            Pattern::List {
                prefix,
                spread,
                suffix,
                ty,
            } => Pattern::List {
                prefix: prefix
                    .into_iter()
                    .map(|item| self.rewrite_pattern_defaults(item))
                    .collect(),
                spread: spread.map(|item| Box::new(self.rewrite_pattern_defaults(*item))),
                suffix: suffix
                    .into_iter()
                    .map(|item| self.rewrite_pattern_defaults(item))
                    .collect(),
                ty,
            },
            Pattern::Record { fields, spread, ty } => Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| {
                        let pattern = self.rewrite_pattern_defaults(field.pattern);
                        let default_context = pattern_value_context(&pattern);
                        let default = field
                            .default
                            .map(|default| self.rewrite_expr(default, default_context));
                        RecordPatternField {
                            name: field.name,
                            pattern,
                            default,
                        }
                    })
                    .collect(),
                spread: spread.map(|spread| match spread {
                    RecordSpreadPattern::Head(pattern) => {
                        RecordSpreadPattern::Head(Box::new(self.rewrite_pattern_defaults(*pattern)))
                    }
                    RecordSpreadPattern::Tail(pattern) => {
                        RecordSpreadPattern::Tail(Box::new(self.rewrite_pattern_defaults(*pattern)))
                    }
                }),
                ty,
            },
            Pattern::Variant { tag, value, ty } => Pattern::Variant {
                tag,
                value: value.map(|value| Box::new(self.rewrite_pattern_defaults(*value))),
                ty,
            },
            Pattern::Or { left, right, ty } => Pattern::Or {
                left: Box::new(self.rewrite_pattern_defaults(*left)),
                right: Box::new(self.rewrite_pattern_defaults(*right)),
                ty,
            },
            Pattern::As { pattern, name, ty } => Pattern::As {
                pattern: Box::new(self.rewrite_pattern_defaults(*pattern)),
                name,
                ty,
            },
            Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => pattern,
        }
    }

    fn rewrite_refreshed_block_once(
        &mut self,
        expr: Expr,
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> Expr {
        let Expr {
            ty,
            kind: ExprKind::Block { stmts, tail },
        } = expr
        else {
            return expr;
        };
        self.local_use_contexts
            .push(LocalUseContextScope::default());
        self.local_value_contexts.push(BTreeMap::new());
        let stmts = stmts
            .into_iter()
            .map(|stmt| self.rewrite_stmt(stmt))
            .collect();
        let stmts = self.rewrite_block_module_stmt_types(stmts);
        let kind = ExprKind::Block {
            stmts,
            tail: tail.map(|tail| Box::new(self.rewrite_expr(*tail, result_context.cloned()))),
        };
        let local_use_contexts = self
            .local_use_contexts
            .pop()
            .map(local_use_context_scope_into_contexts)
            .unwrap_or_default();
        self.local_value_contexts.pop();
        let refreshed = refresh_local_expr_types(Expr { ty, kind });
        let refreshed =
            self.rewrite_refreshed_block_let_initializers(refreshed, local_use_contexts);
        let refreshed = refresh_local_expr_types(refreshed);
        let refreshed = self.rewrite_refreshed_block_let_initializers(refreshed, BTreeMap::new());
        project_runtime_expr_types(refresh_local_expr_types(refreshed))
    }

    fn rewrite_refreshed_block_let_initializers(
        &mut self,
        expr: Expr,
        mut local_use_contexts: BTreeMap<typed_ir::Name, typed_ir::TypeBounds>,
    ) -> Expr {
        let Expr {
            ty,
            kind: ExprKind::Block { stmts, tail },
        } = expr
        else {
            return expr;
        };
        merge_local_use_contexts(
            &mut local_use_contexts,
            collect_block_local_use_contexts(&stmts, tail.as_deref()),
        );
        self.local_value_contexts.push(BTreeMap::new());
        let stmts = stmts
            .into_iter()
            .map(|stmt| match stmt {
                Stmt::Let { pattern, value } => {
                    let value_context = pattern_value_context(&pattern)
                        .or_else(|| {
                            pattern_bind_name(&pattern)
                                .and_then(|name| local_use_contexts.get(name))
                                .cloned()
                        })
                        .or_else(|| self.local_var_ref_binding_context(&pattern));
                    let value = self.rewrite_expr(value, value_context);
                    let pattern = self.rewrite_pattern_defaults(pattern);
                    self.record_local_value_type(&pattern);
                    Stmt::Let { pattern, value }
                }
                Stmt::Expr(expr) => Stmt::Expr(self.rewrite_expr(expr, None)),
                Stmt::Module { def, body } => {
                    let body_context = self.module_stmt_body_context(&def, &local_use_contexts);
                    let body = self.rewrite_expr(body, body_context);
                    Stmt::Module { def, body }
                }
            })
            .collect();
        let tail = tail.map(|tail| Box::new(self.rewrite_expr(*tail, None)));
        self.local_value_contexts.pop();
        Expr {
            ty,
            kind: ExprKind::Block { stmts, tail },
        }
    }

    fn local_var_ref_binding_context(&self, pattern: &Pattern) -> Option<typed_ir::TypeBounds> {
        let Pattern::Bind { name, ty } = pattern else {
            return None;
        };
        let raw = name.0.strip_prefix('&')?;
        let init_name = typed_ir::Name(format!("#{raw}"));
        let init_ty = self.local_value_type(&typed_ir::Path::from_name(init_name))?;
        let init_ty = runtime_core_type(&init_ty);
        if !closed_slot_type_usable(&init_ty, false) {
            return None;
        }
        let RuntimeType::Core(typed_ir::Type::Named { path, args }) = ty else {
            return None;
        };
        if !is_std_var_ref_path(path) || args.len() != 2 {
            return None;
        }
        let mut args = args.clone();
        args[1] = typed_ir::TypeArg::Type(init_ty);
        Some(typed_ir::TypeBounds::exact(typed_ir::Type::Named {
            path: path.clone(),
            args,
        }))
    }

    fn module_stmt_body_context(
        &self,
        def: &typed_ir::Path,
        local_use_contexts: &BTreeMap<typed_ir::Name, typed_ir::TypeBounds>,
    ) -> Option<typed_ir::TypeBounds> {
        self.monomorphic_binding_type(def)
            .map(|ty| typed_ir::TypeBounds::exact(runtime_core_type(&ty)))
            .or_else(|| {
                let [name] = def.segments.as_slice() else {
                    return None;
                };
                local_use_contexts.get(name).cloned()
            })
    }

    fn binding_body_runtime_context(binding: &Binding) -> Option<typed_ir::TypeBounds> {
        (!core_type_has_vars(&binding.scheme.body))
            .then(|| typed_ir::TypeBounds::exact(binding.scheme.body.clone()))
    }

    fn rewrite_block_module_stmt_types(&self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        stmts
            .into_iter()
            .map(|stmt| match stmt {
                Stmt::Module { def, mut body } => {
                    if let Some(ty) = self.monomorphic_binding_type(&def) {
                        body.ty = ty;
                    }
                    Stmt::Module { def, body }
                }
                stmt => stmt,
            })
            .collect()
    }

    fn rewrite_apply_from_principal_plan(
        &mut self,
        expr: &Expr,
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> Option<Expr> {
        self.bump("principal-unify-apply");
        let started = self.profile_timer();
        let Some(spine) = principal_unify_apply_spine(expr) else {
            self.finish_profile_timer("apply-spine", started);
            return None;
        };
        self.finish_profile_timer("apply-spine", started);
        if self.should_skip_partial_callee_rewrite(spine.target, spine.args.len()) {
            return None;
        }
        self.record_target_apply_visit(spine.target);
        if self.local_value_type(spine.target).is_some() || is_specialized_path(spine.target) {
            return None;
        }
        if let Some(expr) = self.rewrite_role_method_from_receiver(expr, &spine, result_context) {
            return Some(expr);
        }
        if !self.generic_bindings.contains(spine.target) {
            if let Some(expr) =
                self.rewrite_impl_method_call_from_args(expr, &spine, result_context)
            {
                return Some(expr);
            }
            if let Some(original) = self.bindings_by_path.get(spine.target).cloned()
                && let Some(expr) =
                    self.rewrite_non_generic_effect_context_call(original, &spine, &expr.ty)
            {
                return Some(expr);
            }
            return None;
        }
        let active_context_substitutions = self.active_context_substitutions();
        let mut incomplete_cache_key = None;
        if self.incomplete_plan_targets.contains(spine.target) {
            let key = incomplete_plan_cache_key(
                &spine,
                expr,
                result_context,
                active_context_substitutions.as_ref(),
            );
            if self.incomplete_plan_cache.contains_key(&key) {
                if let Some(expr) = self.rewrite_single_emitted_specialized_call(&spine, &expr.ty) {
                    return Some(expr);
                }
                self.record_target_cached_incomplete(spine.target);
                self.bump("principal-unify-cached-incomplete-plan");
                return None;
            }
            incomplete_cache_key = Some(key);
        }
        self.bump("principal-unify-clone-generic-binding");
        let Some(original) = self.bindings_by_path.get(spine.target).cloned() else {
            return None;
        };
        let original_arity = core_fun_arity(&original.scheme.body);
        if spine.args.len() > original_arity {
            return None;
        }
        if let Some(active) = self.active_specialization_for(spine.target).cloned()
            && let Some(expr) =
                self.rewrite_active_recursive_call(original.clone(), active, &spine, &expr.ty)
        {
            return Some(expr);
        }
        if handler_binding_info(&original).is_some()
            && spine.args.len() < original_arity
            && runtime_type_contains_unknown(&expr.ty)
        {
            self.bump_skip(spine.target, "defer-partial-handler-application");
            return None;
        }
        let started = self.profile_timer();
        let Some(mut plan) = principal_elaboration_plan_for_expr(expr, &original, result_context)
        else {
            self.finish_profile_timer("plan-for-expr", started);
            self.bump_skip(spine.target, "missing-principal-elaboration-plan");
            return None;
        };
        self.finish_profile_timer("plan-for-expr", started);
        let started = self.profile_timer();
        if let Some(active_substitutions) = active_context_substitutions.as_ref()
            && let Some(scoped_substitutions) =
                scoped_active_context_substitutions(&original, active_substitutions)
        {
            debug_principal_unify_active(spine.target, &scoped_substitutions);
            plan = substitute_principal_plan_context_slots(plan, &scoped_substitutions);
        }
        if let Some(active) = self.active_specialization_for(spine.target).cloned() {
            debug_principal_unify_active(spine.target, &active.substitutions);
            merge_plan_substitutions(&mut plan, active.substitutions);
            plan = normalize_principal_elaboration_plan_with_role_impls(
                plan,
                &[],
                &original.scheme.requirements,
                &self.role_associated_impls,
            );
        }
        let completed = self.complete_principal_plan(
            plan,
            &original,
            &spine.args,
            &spine.evidences,
            &expr.ty,
            result_context,
        );
        plan = completed.plan;
        let completed_with_internal_missing_substitutions =
            completed.completed_with_internal_missing_substitutions;
        self.finish_profile_timer("complete-plan", started);
        if !plan.complete {
            if let Some(expr) = self.rewrite_single_emitted_specialized_call(&spine, &expr.ty) {
                return Some(expr);
            }
            self.bump_skip(spine.target, "incomplete-principal-elaboration-plan");
            self.record_target_incomplete(spine.target);
            let substitutions = plan_substitution_map(&plan);
            let missing_vars = missing_required_vars(&original, &substitutions);
            self.bump_missing_var_list(spine.target, &missing_vars);
            let key = incomplete_cache_key.unwrap_or_else(|| {
                incomplete_plan_cache_key(
                    &spine,
                    expr,
                    result_context,
                    self.active_context_substitutions().as_ref(),
                )
            });
            self.incomplete_plan_targets.insert(spine.target.clone());
            self.incomplete_plan_cache
                .insert(key, CachedIncompletePrincipalPlan);
            return None;
        }
        if plan_has_imprecise_choice_slot_substitutions(&plan, &original) {
            self.bump_skip(spine.target, "imprecise-choice-slot-substitution");
            return None;
        }
        if !plan.adapters.is_empty() {
            self.bump_skip(spine.target, "missing-adapter-hole-execution");
            return None;
        }
        let mut substitutions = plan_substitution_map(&plan);
        let binding_substitutions = complete_required_substitutions(&original, &substitutions)
            .or_else(|| complete_binding_signature_substitutions(&original, &substitutions))
            .or_else(|| {
                completed_with_internal_missing_substitutions
                    .then(|| complete_binding_type_param_substitutions(&original, &substitutions))
                    .flatten()
            })
            .or_else(|| {
                (!missing_required_vars(&original, &substitutions).is_empty()
                    && missing_binding_type_params(&original, &substitutions).is_empty())
                .then(|| complete_binding_type_param_substitutions(&original, &substitutions))
                .flatten()
            });
        let Some(mut binding_substitutions) = binding_substitutions else {
            self.bump_skip(spine.target, "incomplete-binding-substitution");
            self.bump_missing_vars(spine.target, &original, &substitutions);
            return None;
        };
        if original.name.segments.len() == 1
            && binding_substitutions_are_only_top(&original, &binding_substitutions)
        {
            self.bump_skip(spine.target, "imprecise-principal-specialization");
            return None;
        }
        let handler_info = handler_binding_info(&original);
        let mut callee_ty = substitute_type(&original.scheme.body, &binding_substitutions);
        let Some((mut params, mut ret, _ret_effect)) =
            core_fun_spine_parts_exact(&callee_ty, spine.args.len())
        else {
            self.bump_skip(spine.target, "non-function-principal");
            return None;
        };
        if handler_info.is_none()
            && !borrowed_args_accept_specialization_inputs(&spine.args, &params)
        {
            let Some(adjusted) =
                self.complete_plan_from_argument_runtime_types(&original, &plan, &spine.args)
            else {
                self.bump_skip(spine.target, "conflicting-specialization-inputs");
                return None;
            };
            plan = adjusted;
            substitutions = plan_substitution_map(&plan);
            let Some(adjusted_binding_substitutions) =
                complete_required_substitutions(&original, &substitutions)
            else {
                self.bump_skip(spine.target, "incomplete-argument-runtime-substitution");
                self.bump_missing_vars(spine.target, &original, &substitutions);
                return None;
            };
            binding_substitutions = adjusted_binding_substitutions;
            callee_ty = substitute_type(&original.scheme.body, &binding_substitutions);
            let Some((adjusted_params, adjusted_ret, _adjusted_ret_effect)) =
                core_fun_spine_parts_exact(&callee_ty, spine.args.len())
            else {
                self.bump_skip(spine.target, "non-function-argument-runtime-substitution");
                return None;
            };
            params = adjusted_params;
            ret = adjusted_ret;
            if !borrowed_args_accept_specialization_inputs(&spine.args, &params) {
                self.bump_skip(spine.target, "conflicting-specialization-inputs");
                return None;
            }
        }
        let is_handler_binding = handler_info.is_some();
        let rewritten_args = spine
            .args
            .iter()
            .zip(&params)
            .map(|(arg, (param, _param_effect))| {
                self.rewrite_expr(
                    (*arg).clone(),
                    Some(typed_ir::TypeBounds::exact(param.clone())),
                )
            })
            .collect::<Vec<_>>();
        let rewritten_args = refresh_rewritten_args(rewritten_args);
        if handler_info.is_none() && !owned_args_fit_without_adapter(&rewritten_args, &params) {
            self.bump_skip(spine.target, "missing-adapter-hole");
            return None;
        }
        let handler_plan = handler_info.map(|info| {
            let boundary = handler_call_boundary_refs(&info, &rewritten_args, &expr.ty);
            let plan = handler_adapter_plan(&info, &boundary);
            let plan = substitute_handler_adapter_plan(&plan, &substitutions);
            let plan =
                refine_handler_adapter_plan_from_signature(plan, &params, &ret, &info.consumes);
            (boundary, plan)
        });
        if let Some((boundary, plan)) = handler_plan.as_ref() {
            debug_principal_unify_handler_plan(spine.target, boundary, plan);
        }
        if let Some((boundary, plan)) = handler_plan.as_ref()
            && !handler_plan_is_supported(boundary, plan)
        {
            self.bump_skip(spine.target, "missing-handler-adapter-hole");
            return None;
        }
        let result_context_ty = result_context
            .and_then(|bounds| closed_type_from_bounds(Some(bounds)))
            .map(RuntimeType::core);
        let final_context_ty = if is_handler_binding && !runtime_type_contains_unknown(&expr.ty) {
            expr.ty.clone()
        } else {
            result_context_ty.unwrap_or_else(|| expr.ty.clone())
        };
        let specialization = self.principal_call_specialization(
            &original,
            &binding_substitutions,
            is_handler_binding,
            handler_plan.as_ref(),
            &spine.args,
            &spine.evidences,
            &rewritten_args,
            &params,
            result_context,
        )?;
        let final_context_ty = contextual_final_call_type(
            final_context_ty,
            &specialization.call_callee_ty,
            rewritten_args.len(),
            is_handler_binding,
        );
        let path = self.intern_specialization(
            original,
            specialization.substitutions,
            specialization.handler_plan,
            Some(specialization.input_shapes),
            specialization.output_shape,
        )?;
        self.record_target_rewrite(spine.target);
        self.bump("principal-unify-rewrite");
        debug_principal_unify_rewrite(spine.target, &path);
        Some(rebuild_apply_call_owned_with_final_arg_effect(
            path,
            specialization.call_callee_ty,
            rewritten_args,
            &final_context_ty,
            specialization.final_arg_effect.as_ref(),
        )?)
    }

    fn principal_call_specialization(
        &mut self,
        original: &Binding,
        binding_substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
        is_handler_binding: bool,
        handler_plan: Option<&(HandlerCallBoundary, HandlerAdapterPlan)>,
        borrowed_args: &[&Expr],
        evidences: &[Option<&typed_ir::ApplyEvidence>],
        rewritten_args: &[Expr],
        params: &[(typed_ir::Type, typed_ir::Type)],
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> Option<PrincipalCallSpecialization> {
        let mut input_shapes =
            specialization_input_shapes_from_call(borrowed_args, rewritten_args, evidences, params);
        if is_handler_binding {
            preserve_handler_choice_input_shapes(&mut input_shapes, params);
        }

        let mut output_shape =
            result_context.and_then(|bounds| closed_type_from_bounds(Some(bounds)));
        let mut output_shape_from_consumed_payload = false;
        if is_handler_binding {
            let has_action_arg = rewritten_args.len() >= core_fun_arity(&original.scheme.body);
            if has_action_arg {
                if let Some(action_output) = handler_action_output_shape(rewritten_args)
                    && (output_shape.is_none()
                        || output_shape
                            .as_ref()
                            .is_some_and(|output| type_choice_contains(output, &action_output)))
                {
                    output_shape = Some(action_output);
                }
            }
            if has_action_arg {
                let consumed_payload = handler_plan
                    .and_then(|(boundary, _)| handler_consumed_payload_output_shape(boundary));
                let preferred = prefer_handler_consumed_payload_output_shape(
                    output_shape,
                    consumed_payload.as_ref(),
                );
                output_shape_from_consumed_payload = preferred.from_consumed_payload;
                output_shape = preferred.output_shape;
            }
        }
        let mut substitutions = binding_substitutions.clone();
        if is_handler_binding && let Some(output_shape) = output_shape.as_ref() {
            align_handler_action_input_shape_with_output(
                &original.scheme.body,
                &mut input_shapes,
                output_shape,
            );
            narrow_handler_output_substitution(
                &original.scheme.body,
                rewritten_args.len(),
                &mut substitutions,
                output_shape,
            );
            if output_shape_from_consumed_payload {
                narrow_handler_choice_substitutions_to_output(&mut substitutions, output_shape);
            }
        }
        output_shape = self.refine_contextual_specialization(
            original,
            &mut substitutions,
            Some(&input_shapes),
            output_shape.as_ref(),
        )?;
        if is_handler_binding && let Some(output_shape) = output_shape.as_ref() {
            narrow_handler_output_substitution(
                &original.scheme.body,
                rewritten_args.len(),
                &mut substitutions,
                output_shape,
            );
            if output_shape_from_consumed_payload {
                narrow_handler_choice_substitutions_to_output(&mut substitutions, output_shape);
            }
        }
        output_shape = preferred_specialization_output_shape(
            &original.scheme.body,
            rewritten_args.len(),
            &substitutions,
            output_shape,
            is_handler_binding,
        );

        let mut handler_plan =
            handler_plan.map(|(_, plan)| substitute_handler_adapter_plan(plan, &substitutions));
        if let (Some(plan), Some(output_shape)) = (handler_plan.as_mut(), output_shape.as_ref())
            && plan.return_wrapper_effect.is_some()
        {
            plan.return_value = Some(output_shape.clone());
        }

        let call_callee_ty = call_specialization_callee_type(
            original,
            &substitutions,
            handler_plan.as_ref(),
            input_shapes.as_slice(),
            output_shape.as_ref(),
            rewritten_args.len(),
        );
        let final_arg_effect = handler_plan
            .as_ref()
            .and_then(|plan| plan.residual_before.as_ref())
            .filter(|effect| !effect_is_empty(effect))
            .cloned();

        Some(PrincipalCallSpecialization {
            substitutions,
            input_shapes,
            output_shape,
            handler_plan,
            call_callee_ty,
            final_arg_effect,
        })
    }

    fn complete_plan_from_principal_callee(
        &mut self,
        original: &Binding,
        plan: &typed_ir::PrincipalElaborationPlan,
    ) -> Option<typed_ir::PrincipalElaborationPlan> {
        let required_vars = self.required_vars_for_binding(original);
        if required_vars.is_empty() {
            return None;
        }
        let before = plan_substitution_map(plan);
        if missing_required_vars(original, &before).is_empty() && plan.complete {
            return None;
        }
        let mut substitutions = before.clone();
        let mut conflicts = BTreeSet::new();
        let plan_principal = substitute_type(&plan.principal_callee, &before);
        project_closed_substitutions_from_type(
            &original.scheme.body,
            &plan_principal,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            false,
            64,
        );
        if substitutions == before
            && let Some(suffix) =
                principal_callee_scheme_suffix(&original.scheme.body, &plan_principal)
        {
            project_closed_substitutions_from_type(
                &suffix,
                &plan_principal,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
        }
        if !conflicts.is_empty() || substitutions == before {
            return None;
        }
        let projected_substitutions = substitutions.clone();
        let mut plan = plan.clone();
        plan.substitutions = substitutions
            .into_iter()
            .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
            .collect();
        let mut normalized = normalize_principal_elaboration_plan_with_role_impls(
            plan,
            &[],
            &original.scheme.requirements,
            &self.role_associated_impls,
        );
        preserve_projected_substitutions_if_normalized_empty(
            &mut normalized,
            projected_substitutions,
        );
        debug_principal_unify_normalized_plan(&normalized);
        Some(normalized)
    }

    fn complete_principal_plan(
        &mut self,
        mut plan: typed_ir::PrincipalElaborationPlan,
        original: &Binding,
        args: &[&Expr],
        evidences: &[Option<&typed_ir::ApplyEvidence>],
        expr_ty: &RuntimeType,
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> CompletedPrincipalPlan {
        if let Some(completed) = self.complete_plan_from_principal_callee(original, &plan) {
            self.bump("principal-unify-principal-callee-completed-plan");
            plan = completed;
        }
        if let Some(completed) = self.complete_plan_from_binding_scheme_slots(original, &plan) {
            self.bump("principal-unify-binding-scheme-slots-completed-plan");
            plan = completed;
        }
        if let Some(completed) =
            self.complete_plan_from_argument_runtime_types(original, &plan, args)
        {
            self.bump("principal-unify-argument-runtime-completed-plan");
            plan = completed;
        }
        if let Some(completed) = self.complete_plan_from_role_associated_outputs(original, &plan) {
            self.bump("principal-unify-role-associated-completed-plan");
            plan = completed;
        }
        if let Some(completed) = self.complete_plan_from_result_constructor_payload(original, &plan)
        {
            self.bump("principal-unify-result-constructor-payload-completed-plan");
            plan = completed;
        }
        if let Some(completed) = self.complete_plan_from_constructor_phantom_slots(original, &plan)
        {
            self.bump("principal-unify-constructor-phantom-completed-plan");
            plan = completed;
        }
        if principal_plan_needs_runtime_effect_slots(original, &plan) {
            let projection_result_ty = result_context
                .and_then(|bounds| closed_type_from_bounds(Some(bounds)))
                .map(RuntimeType::core)
                .unwrap_or_else(|| expr_ty.clone());
            let binding_signature_vars = binding_signature_vars(original);
            if let Some(completed) = self.complete_plan_from_runtime_effect_slots(
                &plan,
                original,
                args,
                evidences,
                &projection_result_ty,
                &binding_signature_vars,
                &original.scheme.requirements,
            ) {
                self.bump("principal-unify-runtime-effect-completed-plan");
                plan = completed;
            }
        }
        if !plan.complete
            && let Some(completed) = self.complete_plan_from_substituted_body(original, &plan)
        {
            self.bump("principal-unify-body-result-completed-plan");
            plan = completed;
        }
        plan = self.complete_handler_boundary_plan(original, plan);
        if !plan.complete
            && missing_required_vars(original, &plan_substitution_map(&plan)).is_empty()
            && plan_only_lacks_open_slot_precision(&plan)
        {
            self.bump("principal-unify-open-slot-plan-completed");
            plan.complete = true;
            plan.incomplete_reasons.clear();
        }

        let mut completed_with_internal_missing_substitutions = false;
        if !plan.complete
            && plan_only_lacks_effect_only_missing_substitutions(&plan, original)
            && missing_required_vars(original, &plan_substitution_map(&plan)).is_empty()
        {
            self.bump("principal-unify-effect-only-missing-plan-completed");
            plan.complete = true;
            plan.incomplete_reasons.clear();
        }
        if !plan.complete
            && plan_only_lacks_internal_missing_substitutions(&plan, original)
            && missing_binding_type_params(original, &plan_substitution_map(&plan)).is_empty()
        {
            self.bump("principal-unify-internal-missing-plan-completed");
            completed_with_internal_missing_substitutions = true;
            plan.complete = true;
            plan.incomplete_reasons.clear();
        }

        CompletedPrincipalPlan {
            plan,
            completed_with_internal_missing_substitutions,
        }
    }

    fn complete_plan_from_role_associated_outputs(
        &mut self,
        original: &Binding,
        plan: &typed_ir::PrincipalElaborationPlan,
    ) -> Option<typed_ir::PrincipalElaborationPlan> {
        if original.scheme.requirements.is_empty() || self.role_associated_impls.is_empty() {
            return None;
        }
        let associated_vars = role_associated_requirement_vars(&original.scheme.requirements);
        if associated_vars.is_empty() {
            return None;
        }
        let before = plan_substitution_map(plan);
        let before_missing = missing_required_vars(original, &before).len();
        let mut plan = plan.clone();
        plan.substitutions
            .retain(|substitution| !associated_vars.contains(&substitution.var));
        let normalized = normalize_principal_elaboration_plan_with_role_impls(
            plan,
            &[],
            &original.scheme.requirements,
            &self.role_associated_impls,
        );
        let after = plan_substitution_map(&normalized);
        let changed = associated_vars
            .iter()
            .any(|var| before.get(var) != after.get(var));
        if !changed {
            return None;
        }
        if !normalized.complete && missing_required_vars(original, &after).len() > before_missing {
            return None;
        }
        debug_principal_unify_normalized_plan(&normalized);
        Some(normalized)
    }

    fn complete_handler_boundary_plan(
        &mut self,
        original: &Binding,
        mut plan: typed_ir::PrincipalElaborationPlan,
    ) -> typed_ir::PrincipalElaborationPlan {
        if !plan.complete
            && handler_binding_info(original).is_some()
            && plan_only_lacks_handler_boundary(&plan)
        {
            for var in missing_required_vars(original, &plan_substitution_map(&plan)) {
                plan.substitutions.push(typed_ir::TypeSubstitution {
                    var,
                    ty: typed_ir::Type::Never,
                });
            }
            plan = normalize_principal_elaboration_plan_with_role_impls(
                plan,
                &[],
                &original.scheme.requirements,
                &self.role_associated_impls,
            );
        }
        if !plan.complete
            && handler_binding_info(original).is_some()
            && plan_only_lacks_handler_boundary(&plan)
            && missing_required_vars(original, &plan_substitution_map(&plan)).is_empty()
        {
            self.bump("principal-unify-handler-boundary-plan-completed");
            plan.complete = true;
            plan.incomplete_reasons.clear();
        }
        plan
    }

    fn complete_plan_from_argument_runtime_types(
        &mut self,
        original: &Binding,
        plan: &typed_ir::PrincipalElaborationPlan,
        args: &[&Expr],
    ) -> Option<typed_ir::PrincipalElaborationPlan> {
        let required_vars = self.required_vars_for_binding(original);
        if required_vars.is_empty() {
            return None;
        }
        let Some((params, _ret, _ret_effect)) =
            core_fun_spine_parts_exact(&original.scheme.body, args.len())
        else {
            return None;
        };
        let mut projected = BTreeMap::new();
        let mut conflicts = BTreeSet::new();
        for (arg, (param, param_effect)) in args.iter().zip(&params) {
            let (actual_value, actual_effect) = runtime_value_and_effect(&arg.ty);
            let actual_value = project_runtime_type_with_vars(&actual_value, &BTreeSet::new());
            if !core_type_contains_unknown(&actual_value) && !core_type_has_vars(&actual_value) {
                let allow_never_value = matches!(actual_value, typed_ir::Type::Never);
                project_closed_substitutions_from_type(
                    param,
                    &actual_value,
                    &required_vars,
                    &mut projected,
                    &mut conflicts,
                    allow_never_value,
                    64,
                );
            }
            if !core_type_contains_unknown(&actual_effect) && !core_type_has_vars(&actual_effect) {
                project_closed_substitutions_from_type(
                    param_effect,
                    &actual_effect,
                    &required_vars,
                    &mut projected,
                    &mut conflicts,
                    false,
                    64,
                );
            }
        }
        if projected.is_empty() || !conflicts.is_empty() {
            return None;
        }
        let mut substitutions = plan_substitution_map(plan);
        let before = substitutions.clone();
        for (var, ty) in projected {
            if substitutions
                .get(&var)
                .is_some_and(principal_runtime_substitution_is_unit_default)
                && !principal_runtime_substitution_is_unit_default(&ty)
                && !core_type_contains_unknown(&ty)
                && !core_type_has_vars(&ty)
            {
                substitutions.remove(&var);
            }
            insert_exact_projected_substitution(&mut substitutions, &mut conflicts, var, ty);
        }
        if !conflicts.is_empty() {
            return None;
        }
        if substitutions == before {
            return None;
        }
        let projected_substitutions = substitutions.clone();
        let mut plan = plan.clone();
        plan.substitutions = substitutions
            .into_iter()
            .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
            .collect();
        mark_never_runtime_arg_slots(&mut plan, args);
        let mut normalized = normalize_principal_elaboration_plan_with_role_impls(
            plan,
            &[],
            &original.scheme.requirements,
            &self.role_associated_impls,
        );
        preserve_projected_substitutions_if_normalized_empty(
            &mut normalized,
            projected_substitutions,
        );
        debug_principal_unify_normalized_plan(&normalized);
        normalized.complete.then_some(normalized)
    }

    fn complete_plan_from_binding_scheme_slots(
        &mut self,
        original: &Binding,
        plan: &typed_ir::PrincipalElaborationPlan,
    ) -> Option<typed_ir::PrincipalElaborationPlan> {
        let required_vars = self.required_vars_for_binding(original);
        if required_vars.is_empty() {
            return None;
        }
        let before = plan_substitution_map(plan);
        if missing_required_vars(original, &before).is_empty() {
            return None;
        }
        let mut substitutions = before.clone();
        let mut conflicts = BTreeSet::new();
        let template = substitute_type(&original.scheme.body, &substitutions);
        let Some((params, ret, _ret_effect)) =
            core_fun_spine_parts_exact(&template, plan.args.len())
        else {
            return None;
        };
        for arg in &plan.args {
            let Some((param, _effect)) = params.get(arg.index) else {
                continue;
            };
            project_principal_arg_slot_substitutions(
                param,
                arg,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
            );
            if let Some(actual) = principal_plan_arg_closed_type(arg, &substitutions) {
                project_closed_substitutions_from_type(
                    param,
                    &actual,
                    &required_vars,
                    &mut substitutions,
                    &mut conflicts,
                    false,
                    64,
                );
            }
        }
        if let Some(actual) =
            principal_plan_result_closed_type_with_substitutions(&plan.result, &substitutions)
        {
            project_closed_substitutions_from_type(
                &ret,
                &actual,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
        }
        project_principal_result_slot_substitutions(
            &ret,
            &plan.result,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
        );
        if !conflicts.is_empty() || substitutions == before {
            return None;
        }
        let projected_substitutions = substitutions.clone();
        let mut plan = plan.clone();
        plan.substitutions = substitutions
            .into_iter()
            .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
            .collect();
        let mut normalized = normalize_principal_elaboration_plan_with_role_impls(
            plan,
            &[],
            &original.scheme.requirements,
            &self.role_associated_impls,
        );
        preserve_projected_substitutions_if_normalized_empty(
            &mut normalized,
            projected_substitutions,
        );
        debug_principal_unify_normalized_plan(&normalized);
        Some(normalized)
    }

    fn complete_plan_from_result_constructor_payload(
        &mut self,
        original: &Binding,
        plan: &typed_ir::PrincipalElaborationPlan,
    ) -> Option<typed_ir::PrincipalElaborationPlan> {
        let required_vars = self.required_vars_for_binding(original);
        if required_vars.is_empty() {
            return None;
        }
        let before = plan_substitution_map(plan);
        if missing_required_vars(original, &before).is_empty() && plan.complete {
            return None;
        }
        let mut substitutions = before.clone();
        let mut conflicts = BTreeSet::new();
        let payload = unique_closed_callback_param_candidate(plan, &substitutions)?;
        project_result_constructor_payload_substitutions(
            &plan.result,
            &payload,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
        );
        if !conflicts.is_empty() || substitutions == before {
            return None;
        }
        let projected_substitutions = substitutions.clone();
        let mut plan = plan.clone();
        plan.substitutions = substitutions
            .into_iter()
            .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
            .collect();
        let mut normalized = normalize_principal_elaboration_plan_with_role_impls(
            plan,
            &[],
            &original.scheme.requirements,
            &self.role_associated_impls,
        );
        preserve_projected_substitutions_if_normalized_empty(
            &mut normalized,
            projected_substitutions,
        );
        debug_principal_unify_normalized_plan(&normalized);
        Some(normalized)
    }

    fn complete_plan_from_constructor_phantom_slots(
        &mut self,
        original: &Binding,
        plan: &typed_ir::PrincipalElaborationPlan,
    ) -> Option<typed_ir::PrincipalElaborationPlan> {
        let payload_vars = variant_constructor_payload_type_vars(&original.body)?;
        let before = plan_substitution_map(plan);
        let missing = missing_required_vars(original, &before);
        if missing.is_empty() {
            return None;
        }
        let effect_only_vars = binding_effect_only_vars(original);
        let mut substitutions = before.clone();
        for var in missing {
            if payload_vars.contains(&var) {
                continue;
            }
            let ty = if effect_only_vars.contains(&var) {
                typed_ir::Type::Never
            } else {
                typed_ir::Type::Tuple(Vec::new())
            };
            substitutions.insert(var, ty);
        }
        if substitutions == before {
            return None;
        }
        if debug_principal_unify_enabled() {
            eprintln!(
                "principal-unify constructor-phantom {} payload_vars={payload_vars:?} substitutions={substitutions:?}",
                canonical_path(&original.name)
            );
        }
        let projected_substitutions = substitutions.clone();
        let mut plan = plan.clone();
        plan.substitutions = substitutions
            .into_iter()
            .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
            .collect();
        let mut normalized = normalize_principal_elaboration_plan_with_role_impls(
            plan,
            &[],
            &original.scheme.requirements,
            &self.role_associated_impls,
        );
        preserve_projected_substitutions_if_normalized_empty(
            &mut normalized,
            projected_substitutions,
        );
        debug_principal_unify_normalized_plan(&normalized);
        Some(normalized)
    }

    fn rewrite_role_method_from_receiver(
        &mut self,
        expr: &Expr,
        spine: &PrincipalUnifyApplySpine<'_>,
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> Option<Expr> {
        if !is_role_method_path(spine.target) || spine.args.is_empty() {
            return None;
        }
        let active_substitutions = self.active_context_substitutions();
        let receiver_ty = active_substitutions
            .as_ref()
            .map(|substitutions| {
                substitute_type(&runtime_core_type(&spine.args[0].ty), substitutions)
            })
            .unwrap_or_else(|| runtime_core_type(&spine.args[0].ty));
        if matches!(receiver_ty, typed_ir::Type::Unknown | typed_ir::Type::Any)
            && !role_spine_has_local_imprecise_receiver(spine)
        {
            self.bump_skip(spine.target, "skip-imprecise-role-receiver");
            return None;
        }
        let method = spine.target.segments.last()?;
        let candidates = self.role_impls.get(method)?.clone();
        if runtime_type_value_is_function(&expr.ty) && !closed_slot_type_usable(&receiver_ty, false)
        {
            if debug_principal_unify_enabled() {
                eprintln!(
                    "principal-unify partial-role-skip {:?} receiver={receiver_ty:?} active={active_substitutions:?}",
                    spine.target
                );
            }
            self.bump_skip(spine.target, "skip-partial-role-call");
            return None;
        }
        debug_principal_unify_role_candidates(
            spine.target,
            &receiver_ty,
            candidates.iter().map(|candidate| &candidate.name),
        );
        let role_result_ty = result_context
            .and_then(|bounds| closed_type_from_bounds(Some(bounds)))
            .map(|value| runtime_type_with_context_value_and_actual_effect(&expr.ty, value))
            .unwrap_or_else(|| expr.ty.clone());
        let mut matches = candidates
            .iter()
            .filter_map(|candidate| {
                let substitutions = role_impl_closed_substitutions(
                    candidate,
                    spine,
                    &role_result_ty,
                    active_substitutions.as_ref(),
                )?;
                let score = role_impl_match_score(
                    candidate,
                    spine,
                    &role_result_ty,
                    &substitutions,
                    active_substitutions.as_ref(),
                );
                Some((candidate.clone(), substitutions, score))
            })
            .collect::<Vec<_>>();
        if let Some(best) = matches.iter().map(|(_, _, score)| *score).max() {
            matches.retain(|(_, _, score)| *score == best);
        }
        if matches.len() != 1 {
            if runtime_type_value_is_function(&expr.ty)
                && closed_slot_type_usable(&receiver_ty, false)
                && let Some(expr) = self.rewrite_role_method_head_from_receiver(
                    spine.target,
                    &candidates,
                    spine,
                    active_substitutions.as_ref(),
                    &role_result_ty,
                )
            {
                return Some(expr);
            }
            if let Some(expr) = self.rewrite_single_emitted_role_specialization(
                spine.target,
                &candidates,
                &spine.args,
                &role_result_ty,
            ) {
                self.bump("principal-unify-role-single-emitted-rewrite");
                return Some(expr);
            }
            if matches.len() > 1 {
                debug_principal_unify_role_ambiguous(
                    spine.target,
                    &receiver_ty,
                    matches
                        .iter()
                        .map(|(binding, substitutions, _score)| (&binding.name, substitutions)),
                );
                self.bump_skip(spine.target, "skip-ambiguous-role-impl");
            }
            return None;
        }
        let (original, substitutions, _score) = matches.pop()?;
        let impl_ty = substitute_type(&original.scheme.body, &substitutions);
        let Some((params, _ret, _ret_effect)) =
            core_fun_spine_parts_exact(&impl_ty, spine.args.len())
        else {
            debug_principal_unify_role_candidate_rejected(
                &original.name,
                "non-function-role-impl",
                &substitutions,
                &missing_required_vars(&original, &substitutions),
            );
            self.bump_skip(spine.target, "non-function-role-impl");
            return None;
        };
        let rewritten_args = spine
            .args
            .iter()
            .zip(&params)
            .map(|(arg, (param, _param_effect))| {
                self.rewrite_expr(
                    (*arg).clone(),
                    Some(typed_ir::TypeBounds::exact(param.clone())),
                )
            })
            .collect::<Vec<_>>();
        let rewritten_args = refresh_rewritten_args(rewritten_args);
        if !owned_args_fit_without_adapter(&rewritten_args, &params) {
            debug_principal_unify_role_candidate_rejected(
                &original.name,
                "missing-role-adapter-hole",
                &substitutions,
                &missing_required_vars(&original, &substitutions),
            );
            self.bump_skip(spine.target, "missing-role-adapter-hole");
            return None;
        }
        let call_effect = final_ty_effect_context(&role_result_ty).or_else(|| {
            (!runtime_type_value_is_function(&role_result_ty))
                .then(|| {
                    combined_forced_argument_effect(&rewritten_args)
                        .or_else(|| combined_forced_argument_effect_refs(&spine.args))
                })
                .flatten()
        });
        let effect_context = call_effect.and_then(|effect| {
            let substituted = substitute_binding(original.clone(), &substitutions);
            let wrapped = match wrap_non_generic_binding_return_effect(
                substituted,
                spine.args.len(),
                effect.clone(),
            ) {
                Some(wrapped) => wrapped,
                None => {
                    self.bump_skip(spine.target, "missing-role-effect-wrapper");
                    return None;
                }
            };
            let impl_ty = wrapped.scheme.body.clone();
            let path = match self.intern_effect_context_specialization(
                wrapped,
                spine.args.len(),
                &effect,
                &substitutions,
                None,
            ) {
                Some(path) => path,
                None => {
                    self.bump_skip(spine.target, "missing-role-effect-specialization");
                    return None;
                }
            };
            let (_params, ret) = match core_fun_spine_exact(&impl_ty, spine.args.len()) {
                Some(parts) => parts,
                None => {
                    self.bump_skip(spine.target, "missing-role-effect-return");
                    return None;
                }
            };
            let final_ty = RuntimeType::thunk(effect, RuntimeType::core(ret));
            Some((path, impl_ty, final_ty))
        });
        let (path, impl_ty, final_ty) = if let Some(effect_context) = effect_context {
            effect_context
        } else {
            let path = self.intern_specialization(original, substitutions, None, None, None)?;
            (path, impl_ty, role_result_ty)
        };
        self.bump("principal-unify-role-rewrite");
        debug_principal_unify_rewrite(spine.target, &path);
        let role_rewrites = self
            .role_method_rewrites
            .entry(spine.target.clone())
            .or_default();
        if !role_rewrites.iter().any(|existing| existing == &path) {
            role_rewrites.push(path.clone());
        }
        Some(rebuild_apply_call_owned(
            path,
            impl_ty,
            rewritten_args,
            &final_ty,
        )?)
    }

    fn rewrite_role_method_head_from_receiver(
        &mut self,
        role_method: &typed_ir::Path,
        candidates: &[Binding],
        spine: &PrincipalUnifyApplySpine<'_>,
        ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
        final_ty: &RuntimeType,
    ) -> Option<Expr> {
        let mut matches = candidates
            .iter()
            .filter_map(|candidate| {
                let substitutions = role_impl_receiver_dispatch_substitutions(
                    candidate,
                    spine,
                    ambient_substitutions,
                )?;
                let impl_ty = substitute_type(&candidate.scheme.body, &substitutions);
                let _ = core_fun_spine_exact(&impl_ty, spine.args.len())?;
                Some((candidate, substitutions, impl_ty))
            })
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return None;
        }
        let (candidate, substitutions, impl_ty) = matches.pop()?;
        self.bump("principal-unify-role-head-dispatch");
        debug_principal_unify_rewrite(role_method, &candidate.name);
        let (target, impl_ty) = if substitutions.is_empty() {
            (candidate.name.clone(), impl_ty)
        } else {
            let path = self.intern_specialization(
                candidate.clone(),
                substitutions.clone(),
                None,
                None,
                None,
            )?;
            let impl_ty = self
                .binding_by_path_or_emitted(&path)
                .map(|binding| binding.scheme.body.clone())
                .unwrap_or_else(|| substitute_type(&candidate.scheme.body, &substitutions));
            let role_rewrites = self
                .role_method_rewrites
                .entry(role_method.clone())
                .or_default();
            if !role_rewrites.iter().any(|existing| existing == &path) {
                role_rewrites.push(path.clone());
            }
            (path, impl_ty)
        };
        let rewritten = rebuild_apply_call(target, impl_ty, &spine.args, final_ty)?;
        if !runtime_type_value_is_function(final_ty)
            && let Some(rewritten_spine) = principal_unify_apply_spine(&rewritten)
            && self.generic_bindings.contains(rewritten_spine.target)
            && let Some(specialized) = self.rewrite_apply_from_principal_plan(&rewritten, None)
        {
            return Some(specialized);
        }
        if !candidate.type_params.is_empty()
            || !missing_required_vars(candidate, &substitutions).is_empty()
        {
            self.bump_skip(role_method, "skip-generic-role-head-without-specialization");
            return None;
        }
        Some(rewritten)
    }

    fn rewrite_single_emitted_role_specialization(
        &self,
        role_method: &typed_ir::Path,
        candidates: &[Binding],
        args: &[&Expr],
        final_ty: &RuntimeType,
    ) -> Option<Expr> {
        let mut matches = Vec::new();
        if let Some(paths) = self.role_method_rewrites.get(role_method) {
            for path in paths {
                let Some(binding) = self.binding_by_path_or_emitted(path) else {
                    continue;
                };
                let Some(params) = role_rewrite_candidate_params(&binding.scheme.body, args.len())
                else {
                    continue;
                };
                if role_rewrite_candidate_fits(&params, args, final_ty, &binding.scheme.body) {
                    matches.push((path.clone(), binding.scheme.body.clone()));
                }
            }
        }
        for candidate in candidates {
            let Some(paths) = self.root_specializations.get(&candidate.name) else {
                continue;
            };
            for path in paths {
                let Some(binding) = self.emitted_binding(path) else {
                    continue;
                };
                let Some(params) = role_rewrite_candidate_params(&binding.scheme.body, args.len())
                else {
                    continue;
                };
                if role_rewrite_candidate_fits(&params, args, final_ty, &binding.scheme.body) {
                    matches.push((path.clone(), binding.scheme.body.clone()));
                }
            }
        }
        let [(path, callee_ty)] = matches.as_slice() else {
            return None;
        };
        rebuild_apply_call(path.clone(), callee_ty.clone(), args, final_ty)
    }

    fn rewrite_impl_method_call_from_args(
        &mut self,
        expr: &Expr,
        spine: &PrincipalUnifyApplySpine<'_>,
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> Option<Expr> {
        if !is_impl_method_path(spine.target) || spine.args.is_empty() {
            return None;
        }
        let method = spine.target.segments.last()?;
        let candidates = self.role_impls.get(method)?.clone();
        let active_substitutions = self.active_context_substitutions();
        let result_ty = result_context
            .and_then(|bounds| closed_type_from_bounds(Some(bounds)))
            .map(RuntimeType::core)
            .unwrap_or_else(|| expr.ty.clone());
        let mut matches = candidates
            .iter()
            .filter_map(|candidate| {
                let substitutions = role_impl_closed_substitutions(
                    candidate,
                    spine,
                    &result_ty,
                    active_substitutions.as_ref(),
                )?;
                let impl_ty = substitute_type(&candidate.scheme.body, &substitutions);
                let params = role_rewrite_candidate_params(&impl_ty, spine.args.len())?;
                if !role_rewrite_candidate_fits(&params, &spine.args, &result_ty, &impl_ty) {
                    return None;
                }
                let score = role_impl_match_score(
                    candidate,
                    spine,
                    &result_ty,
                    &substitutions,
                    active_substitutions.as_ref(),
                );
                Some((candidate.clone(), substitutions, impl_ty, score))
            })
            .collect::<Vec<_>>();
        if let Some(best) = matches.iter().map(|(_, _, _, score)| *score).max() {
            matches.retain(|(_, _, _, score)| *score == best);
        }
        if matches.len() != 1 {
            return None;
        }
        let (candidate, substitutions, impl_ty, _score) = matches.pop()?;
        if candidate.name == *spine.target && substitutions.is_empty() {
            return None;
        }
        let Some((params, _ret, _ret_effect)) =
            core_fun_spine_parts_exact(&impl_ty, spine.args.len())
        else {
            return None;
        };
        let rewritten_args = spine
            .args
            .iter()
            .zip(&params)
            .map(|(arg, (param, _param_effect))| {
                self.rewrite_expr(
                    (*arg).clone(),
                    Some(typed_ir::TypeBounds::exact(param.clone())),
                )
            })
            .collect::<Vec<_>>();
        let rewritten_args = refresh_rewritten_args(rewritten_args);
        if !owned_args_fit_without_adapter(&rewritten_args, &params) {
            return None;
        }
        let path = if substitutions.is_empty() {
            candidate.name
        } else {
            self.intern_specialization(candidate, substitutions, None, None, None)?
        };
        self.bump("principal-unify-impl-method-corrected");
        debug_principal_unify_rewrite(spine.target, &path);
        rebuild_apply_call_owned(path, impl_ty, rewritten_args, &result_ty)
    }

    fn rewrite_active_recursive_call(
        &mut self,
        original: Binding,
        active: ActivePrincipalSpecialization,
        spine: &PrincipalUnifyApplySpine<'_>,
        final_ty: &RuntimeType,
    ) -> Option<Expr> {
        let substitutions = active.substitutions;
        let callee_ty = if let Some(plan) = active.handler_plan.as_ref() {
            let substituted = substitute_binding(original.clone(), &substitutions);
            apply_handler_adapter_plan_to_binding(substituted, plan)
                .scheme
                .body
        } else {
            substitute_type(&original.scheme.body, &substitutions)
        };
        let callee_ty = active
            .input_shapes
            .as_deref()
            .and_then(|input_shapes| core_fun_spine_with_input_shapes(&callee_ty, input_shapes))
            .unwrap_or(callee_ty);
        let callee_ty = active
            .output_shape
            .as_ref()
            .and_then(|output_shape| {
                core_fun_spine_with_output_shape(
                    &callee_ty,
                    active.input_shapes.as_ref().map_or(0, Vec::len),
                    output_shape,
                )
            })
            .unwrap_or(callee_ty);
        let Some((params, _ret, _ret_effect)) =
            core_fun_spine_parts_exact(&callee_ty, spine.args.len())
        else {
            return None;
        };
        let rewritten_args = spine
            .args
            .iter()
            .zip(&params)
            .map(|(arg, (param, _param_effect))| {
                self.rewrite_expr(
                    (*arg).clone(),
                    Some(typed_ir::TypeBounds::exact(param.clone())),
                )
            })
            .collect::<Vec<_>>();
        let rewritten_args = refresh_rewritten_args(rewritten_args);
        if !owned_args_fit_without_adapter(&rewritten_args, &params) {
            return None;
        }
        self.bump("principal-unify-recursive-rewrite");
        debug_principal_unify_rewrite(spine.target, &active.path);
        rebuild_apply_call_owned(active.path, callee_ty, rewritten_args, final_ty)
    }

    fn rewrite_single_emitted_specialized_call(
        &mut self,
        spine: &PrincipalUnifyApplySpine<'_>,
        final_ty: &RuntimeType,
    ) -> Option<Expr> {
        let original = self.generic_binding(spine.target)?;
        if spine.args.len() != core_fun_arity(&original.scheme.body) {
            return None;
        }
        let (specialized, _ty) = self.single_emitted_specialization(spine.target)?;
        let binding = self.emitted_binding(&specialized).cloned()?;
        let callee_ty = binding.scheme.body.clone();
        let Some((params, ret, ret_effect)) =
            core_fun_spine_parts_exact(&callee_ty, spine.args.len())
        else {
            return None;
        };
        let rewritten_args = spine
            .args
            .iter()
            .zip(&params)
            .map(|(arg, (param, _param_effect))| {
                self.rewrite_expr(
                    (*arg).clone(),
                    Some(typed_ir::TypeBounds::exact(param.clone())),
                )
            })
            .collect::<Vec<_>>();
        let rewritten_args = refresh_rewritten_args(rewritten_args);
        if !owned_args_fit_without_adapter(&rewritten_args, &params) {
            return None;
        }
        if !runtime_type_has_vars(final_ty) {
            let (actual_ret, actual_ret_effect) = runtime_value_and_effect(final_ty);
            if !type_compatible(&actual_ret, &ret)
                || !type_compatible(&actual_ret_effect, &ret_effect)
            {
                return None;
            }
        }
        self.bump("principal-unify-single-specialization-rewrite");
        debug_principal_unify_rewrite(spine.target, &specialized);
        rebuild_apply_call_owned(specialized, callee_ty, rewritten_args, final_ty)
    }

    fn rewrite_non_generic_effect_context_call(
        &mut self,
        original: Binding,
        spine: &PrincipalUnifyApplySpine<'_>,
        final_ty: &RuntimeType,
    ) -> Option<Expr> {
        if !self.required_vars_for_binding(&original).is_empty() {
            return None;
        }
        let RuntimeType::Thunk { effect, value } = final_ty else {
            return None;
        };
        if effect_is_empty(effect) || matches!(value.as_ref(), RuntimeType::Fun { .. }) {
            return None;
        }
        let (params, ret, _ret_effect) =
            core_fun_spine_parts_exact(&original.scheme.body, spine.args.len())?;
        let expected = runtime_core_type(value);
        if ret != expected && !type_compatible(&expected, &ret) {
            return None;
        }
        let input_shapes =
            specialization_input_shapes_from_borrowed_call(&spine.args, &spine.evidences, &params);
        let wrapped =
            wrap_non_generic_binding_return_effect(original, spine.args.len(), effect.clone())?;
        let callee_ty = wrapped.scheme.body.clone();
        let path = self.intern_effect_context_specialization(
            wrapped,
            spine.args.len(),
            &effect,
            &BTreeMap::new(),
            Some(input_shapes),
        )?;
        self.bump("principal-unify-effect-context-rewrite");
        debug_principal_unify_rewrite(spine.target, &path);
        rebuild_apply_call(path, callee_ty, &spine.args, final_ty)
    }

    fn complete_plan_from_runtime_effect_slots(
        &mut self,
        plan: &typed_ir::PrincipalElaborationPlan,
        original: &Binding,
        args: &[&Expr],
        evidences: &[Option<&typed_ir::ApplyEvidence>],
        result_ty: &RuntimeType,
        extra_required_vars: &BTreeSet<typed_ir::TypeVar>,
        requirements: &[typed_ir::RoleRequirement],
    ) -> Option<typed_ir::PrincipalElaborationPlan> {
        if !plan.adapters.is_empty() {
            self.bump("principal-unify-runtime-effect-skip-adapter");
            return None;
        }
        let mut substitutions = plan_substitution_map(plan);
        let mut required_vars = BTreeSet::new();
        collect_core_type_vars(&plan.principal_callee, &mut required_vars);
        required_vars.extend(binding_required_vars(original));
        required_vars.extend(role_associated_requirement_vars(
            &original.scheme.requirements,
        ));
        required_vars.extend(extra_required_vars.iter().cloned());
        let effect_only_vars = binding_effect_only_vars(original);
        substitutions.retain(|var, _| !effect_only_vars.contains(var));
        remove_effectful_erased_arg_value_substitutions(
            &original.scheme.body,
            args,
            &required_vars,
            &mut substitutions,
        );
        if let Some((_, _, original_ret_effect)) =
            core_fun_spine_parts_exact(&original.scheme.body, args.len())
        {
            let mut original_ret_effect_vars = BTreeSet::new();
            collect_core_type_vars(&original_ret_effect, &mut original_ret_effect_vars);
            substitutions.retain(|var, _| !original_ret_effect_vars.contains(var));
        }
        if debug_principal_unify_enabled() {
            eprintln!(
                "principal-unify runtime-required {} vars={:?}",
                plan.target
                    .as_ref()
                    .map(canonical_path)
                    .unwrap_or_else(|| "<unknown>".to_string()),
                required_vars
            );
        }
        if required_vars.is_empty() {
            self.bump("principal-unify-runtime-effect-skip-no-vars");
            return None;
        }
        let before = substitutions.len();
        let mut conflicts = BTreeSet::new();
        self.project_unary_container_item_from_first_arg(
            &original.scheme.body,
            args,
            &required_vars,
            &mut substitutions,
        );
        project_container_callback_item_from_args(
            &original.scheme.body,
            args,
            &required_vars,
            &mut substitutions,
        );
        if let Some((params, _ret, _ret_effect)) =
            core_fun_spine_parts_exact(&original.scheme.body, args.len())
        {
            clear_erased_function_arg_effect_vars(
                &params,
                args,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
            );
        }
        let runtime_arg_projected_vars = project_direct_runtime_arg_substitutions(
            &original.scheme.body,
            args,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
        );
        let projection_substitutions = substitutions
            .iter()
            .filter(|(_, ty)| !matches!(ty, typed_ir::Type::Unknown | typed_ir::Type::Any))
            .map(|(var, ty)| (var.clone(), ty.clone()))
            .collect::<BTreeMap<_, _>>();
        let substituted_principal =
            substitute_type(&original.scheme.body, &projection_substitutions);
        let (params, ret, ret_effect) =
            match core_fun_spine_parts_exact(&substituted_principal, args.len()) {
                Some(parts) => parts,
                None => {
                    self.bump("principal-unify-runtime-effect-skip-non-function");
                    return None;
                }
            };
        let mut ret_effect_vars = BTreeSet::new();
        collect_core_type_vars(&ret_effect, &mut ret_effect_vars);
        substitutions.retain(|var, _| !ret_effect_vars.contains(var));
        clear_erased_function_arg_effect_vars(
            &params,
            args,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
        );
        project_predicate_result_container_item_from_args(
            &ret,
            args,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
        );
        for (index, (arg, (param, param_effect))) in args.iter().zip(&params).enumerate() {
            let (actual, actual_effect) = runtime_value_and_effect(&arg.ty);
            let wait_for_role_completion =
                effectful_erased_arg_should_wait_for_role_completion(&actual, &actual_effect);
            debug_principal_unify_runtime_projection(
                "arg",
                plan.target.as_ref(),
                param,
                &actual,
                param_effect,
                &actual_effect,
            );
            if !wait_for_role_completion {
                project_unary_container_item_from_param_actual(
                    param,
                    &actual,
                    &required_vars,
                    &mut substitutions,
                );
            }
            if !wait_for_role_completion
                && let Some(plan_arg) = plan.args.iter().find(|plan_arg| plan_arg.index == index)
            {
                project_principal_arg_slot_substitutions(
                    param,
                    plan_arg,
                    &required_vars,
                    &mut substitutions,
                    &mut conflicts,
                );
            }
            if !wait_for_role_completion
                && let Some(evidence) = evidences.get(index).copied().flatten()
                && let Some(expected_arg) = evidence.expected_arg.as_ref()
            {
                let retained_ret_effect_substitutions = ret_effect_vars
                    .iter()
                    .filter_map(|var| substitutions.get(var).map(|ty| (var.clone(), ty.clone())))
                    .collect::<BTreeMap<_, _>>();
                project_closed_substitutions_from_type_bounds(
                    param,
                    expected_arg,
                    &required_vars,
                    &mut substitutions,
                    &mut conflicts,
                    false,
                    64,
                );
                substitutions.retain(|var, _| !ret_effect_vars.contains(var));
                substitutions.extend(retained_ret_effect_substitutions);
            }
            if !wait_for_role_completion {
                project_closed_substitutions_from_type(
                    param,
                    &actual,
                    &required_vars,
                    &mut substitutions,
                    &mut conflicts,
                    false,
                    64,
                );
            } else {
                project_effectful_erased_role_arg_value_from_effect(
                    param,
                    &actual_effect,
                    requirements,
                    &required_vars,
                    &mut substitutions,
                    &mut conflicts,
                );
            }
            project_closed_substitutions_from_type(
                param_effect,
                &actual_effect,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                true,
                64,
            );
            project_effect_payload_substitutions_from_expr(
                param_effect,
                arg,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
            );
            if !wait_for_role_completion
                && let Some(plan_arg) = plan.args.iter().find(|plan_arg| plan_arg.index == index)
                && let Some(contextual_actual) =
                    principal_plan_arg_closed_type(plan_arg, &substitutions)
            {
                project_closed_substitutions_from_type(
                    param,
                    &contextual_actual,
                    &required_vars,
                    &mut substitutions,
                    &mut conflicts,
                    false,
                    64,
                );
            }
        }
        let handler_payload_projected_vars = handler_binding_info(original)
            .and_then(|info| {
                let boundary = handler_call_boundary(&info, args, result_ty);
                boundary
                    .input_effect
                    .as_ref()
                    .map(|input_effect| (info, input_effect.clone()))
            })
            .map(|(info, input_effect)| {
                project_handler_consumed_payload_substitutions(
                    &params,
                    &input_effect,
                    &info.consumes,
                    &required_vars,
                    &mut substitutions,
                    &mut conflicts,
                )
            })
            .unwrap_or_default();
        let (actual_ret, actual_ret_effect) = runtime_value_and_effect(result_ty);
        let active_handler_residual_effect = handler_binding_info(original)
            .and_then(|info| self.active_handler_residual_effect(&info));
        let projected_ret_effect = active_handler_residual_effect
            .clone()
            .map(|residual| merge_effects(actual_ret_effect.clone(), residual))
            .unwrap_or_else(|| actual_ret_effect.clone());
        if let Some(info) = handler_binding_info(original) {
            project_handler_payload_result_container_items(
                &ret,
                &actual_ret_effect,
                &info.consumes,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
            );
        }
        if let Some(payload) = single_precise_effect_payload_type(&actual_ret_effect) {
            project_payload_result_container_items(
                &ret,
                &payload,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
            );
        }
        project_result_constructor_payload_substitutions(
            &plan.result,
            &actual_ret,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
        );
        project_principal_result_slot_substitutions(
            &ret,
            &plan.result,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
        );
        if let Some(contextual_ret) =
            principal_plan_result_closed_type_with_substitutions(&plan.result, &substitutions)
        {
            project_slot_lower_template_against_closed_actual(
                &actual_ret,
                &contextual_ret,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
        }
        debug_principal_unify_runtime_projection(
            "result",
            plan.target.as_ref(),
            &ret,
            &actual_ret,
            &ret_effect,
            &projected_ret_effect,
        );
        project_slot_lower_template_against_closed_actual(
            &ret,
            &actual_ret,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            false,
            64,
        );
        project_closed_substitutions_from_type(
            &ret,
            &actual_ret,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            false,
            64,
        );
        project_closed_substitutions_from_type(
            &ret_effect,
            &projected_ret_effect,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            true,
            64,
        );
        project_ref_effect_arg_vars_from_value_arg(
            &ret,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
        );
        if ret_effect_has_unfilled_required_var(&ret_effect, &required_vars, &substitutions)
            && let Some(active_residual_effect) = active_handler_residual_effect
        {
            debug_principal_unify_runtime_projection(
                "active-handler-residual",
                plan.target.as_ref(),
                &ret,
                &actual_ret,
                &ret_effect,
                &active_residual_effect,
            );
            project_closed_substitutions_from_type(
                &ret_effect,
                &active_residual_effect,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                true,
                64,
            );
        }
        if let Some(contextual_ret) =
            principal_plan_result_closed_type_with_substitutions(&plan.result, &substitutions)
        {
            project_closed_substitutions_from_type(
                &ret,
                &contextual_ret,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
        }
        fill_effectful_erased_arg_never_substitutions(
            &original.scheme.body,
            args,
            &required_vars,
            &mut substitutions,
        );
        conflicts.retain(|var| {
            !runtime_arg_projected_vars.contains(var)
                && !handler_payload_projected_vars.contains(var)
        });
        if !conflicts.is_empty() && conflicts.iter().all(|var| effect_only_vars.contains(var)) {
            self.bump("principal-unify-runtime-effect-effect-conflict-kept");
            debug_principal_unify_projection_outcome(
                "effect-conflict-kept",
                plan.target.as_ref(),
                &substitutions,
                &conflicts,
            );
            conflicts.clear();
        }
        let required_vars_closed = required_vars
            .iter()
            .all(|var| substitutions.contains_key(var) || effect_only_vars.contains(var));
        if !conflicts.is_empty() || (substitutions.len() == before && !required_vars_closed) {
            if conflicts.is_empty()
                && let Some(completed) = self.complete_runtime_effect_plan_from_role_impls(
                    plan,
                    args.len(),
                    requirements,
                    &substitutions,
                )
            {
                return Some(completed);
            }
            if !conflicts.is_empty() {
                self.bump("principal-unify-runtime-effect-conflict");
                debug_principal_unify_projection_outcome(
                    "conflict",
                    plan.target.as_ref(),
                    &substitutions,
                    &conflicts,
                );
            } else {
                self.bump("principal-unify-runtime-effect-no-new-substitution");
                debug_principal_unify_projection_outcome(
                    "no-new-substitution",
                    plan.target.as_ref(),
                    &substitutions,
                    &conflicts,
                );
            }
            return None;
        }
        if substitutions.len() == before {
            self.bump("principal-unify-runtime-effect-filled-slots");
        }
        debug_principal_unify_projection_outcome(
            "projected",
            plan.target.as_ref(),
            &substitutions,
            &conflicts,
        );
        let normalized_substitutions = substitutions.clone();
        let mut plan = plan.clone();
        plan.substitutions = substitutions
            .into_iter()
            .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
            .collect();
        mark_never_runtime_arg_slots(&mut plan, args);
        fill_plan_runtime_slots_from_principal(&mut plan, args.len());
        fill_effectful_input_runtime_slot_from_result(&mut plan, args.len());
        let mut normalized =
            self.normalize_runtime_slot_plan_with_role_impls(plan, args.len(), requirements);
        if normalized.complete && normalized.substitutions.is_empty() {
            normalized.substitutions = normalized_substitutions
                .into_iter()
                .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
                .collect();
        }
        debug_principal_unify_normalized_plan(&normalized);
        Some(normalized)
    }

    fn project_unary_container_item_from_first_arg(
        &self,
        principal: &typed_ir::Type,
        args: &[&Expr],
        _required_vars: &BTreeSet<typed_ir::TypeVar>,
        substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ) {
        let Some(first_arg) = args.first() else {
            return;
        };
        let Some((params, _ret, _ret_effect)) = core_fun_spine_parts_exact(principal, args.len())
        else {
            return;
        };
        let Some((container_param, _container_effect)) = params.first() else {
            return;
        };
        let Some(var) = unary_container_item_var(container_param) else {
            return;
        };
        let item = self
            .local_container_item_type(first_arg)
            .or_else(|| unary_container_item_type(&first_arg.ty));
        let Some(item) = item else {
            return;
        };
        insert_projected_container_item_substitution(substitutions, var, item);
    }

    fn local_container_item_type(&self, expr: &Expr) -> Option<typed_ir::Type> {
        match &expr.kind {
            ExprKind::Var(path) => self
                .local_value_type(path)
                .as_ref()
                .and_then(unary_container_item_type),
            ExprKind::Coerce { expr, .. } | ExprKind::BindHere { expr } => {
                self.local_container_item_type(expr)
            }
            _ => None,
        }
    }

    fn complete_runtime_effect_plan_from_role_impls(
        &self,
        plan: &typed_ir::PrincipalElaborationPlan,
        arg_count: usize,
        requirements: &[typed_ir::RoleRequirement],
        substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ) -> Option<typed_ir::PrincipalElaborationPlan> {
        let mut plan = plan.clone();
        plan.substitutions = substitutions
            .iter()
            .map(|(var, ty)| typed_ir::TypeSubstitution {
                var: var.clone(),
                ty: ty.clone(),
            })
            .collect();
        fill_plan_runtime_slots_from_principal(&mut plan, arg_count);
        fill_effectful_input_runtime_slot_from_result(&mut plan, arg_count);
        let projected_substitutions = substitutions.clone();
        let mut normalized =
            self.normalize_runtime_slot_plan_with_role_impls(plan, arg_count, requirements);
        preserve_projected_substitutions_if_normalized_empty(
            &mut normalized,
            projected_substitutions,
        );
        normalized.complete.then_some(normalized)
    }

    fn normalize_runtime_slot_plan_with_role_impls(
        &self,
        mut plan: typed_ir::PrincipalElaborationPlan,
        arg_count: usize,
        requirements: &[typed_ir::RoleRequirement],
    ) -> typed_ir::PrincipalElaborationPlan {
        fill_plan_runtime_slots_from_principal(&mut plan, arg_count);
        fill_effectful_input_runtime_slot_from_result(&mut plan, arg_count);
        let mut normalized = normalize_principal_elaboration_plan_with_role_impls(
            plan,
            &[],
            requirements,
            &self.role_associated_impls,
        );
        let projected_substitutions = plan_substitution_map(&normalized);
        fill_plan_runtime_slots_from_principal(&mut normalized, arg_count);
        fill_effectful_input_runtime_slot_from_result(&mut normalized, arg_count);
        let mut normalized = normalize_principal_elaboration_plan_with_role_impls(
            normalized,
            &[],
            requirements,
            &self.role_associated_impls,
        );
        preserve_projected_substitutions_if_normalized_empty(
            &mut normalized,
            projected_substitutions,
        );
        normalized
    }

    fn active_handler_residual_effect(&self, info: &HandlerBindingInfo) -> Option<typed_ir::Type> {
        let mut residual = None::<typed_ir::Type>;
        for active in self.active_specializations.iter().rev() {
            for effect in active
                .substitutions
                .values()
                .filter_map(runtime_effect_row_candidate)
            {
                let Some(preserved) = handler_preserved_residual_effect(effect, &info.consumes)
                else {
                    continue;
                };
                residual = Some(match residual {
                    Some(existing) => merge_handler_residual_effects(existing, preserved),
                    None => preserved,
                });
            }
            if let Some(plan) = &active.handler_plan
                && let Some(after) = plan.residual_after.as_ref()
                && let Some(preserved) = handler_preserved_residual_effect(after, &info.consumes)
            {
                residual = Some(match residual {
                    Some(existing) => merge_handler_residual_effects(existing, preserved),
                    None => preserved,
                });
            }
        }
        residual
    }

    fn complete_plan_from_substituted_body(
        &mut self,
        original: &Binding,
        plan: &typed_ir::PrincipalElaborationPlan,
    ) -> Option<typed_ir::PrincipalElaborationPlan> {
        if !plan.adapters.is_empty() {
            self.bump("principal-unify-body-result-skip-adapter");
            return None;
        }
        let substitutions = plan_substitution_map(plan);
        let substituted = substitute_binding(original.clone(), &substitutions);
        let Some(body) = binding_body_after_applied_args(&substituted.body, plan.args.len()) else {
            self.bump("principal-unify-body-result-skip-no-body");
            return None;
        };
        let Some(body_spine) = principal_unify_apply_spine(body) else {
            self.bump("principal-unify-body-result-skip-no-spine");
            return None;
        };
        let Some(inner) = self.generic_binding(body_spine.target).cloned() else {
            self.bump("principal-unify-body-result-skip-non-generic-inner");
            return None;
        };
        let Some(inner_plan) = principal_elaboration_plan_for_expr(body, &inner, None) else {
            self.bump("principal-unify-body-result-skip-no-inner-plan");
            return None;
        };
        if !inner_plan.adapters.is_empty() {
            self.bump("principal-unify-body-result-skip-inner-adapter");
            return None;
        }
        let body_ret = if inner_plan.complete {
            let inner_substitutions = plan_substitution_map(&inner_plan);
            let inner_callee = substitute_type(&inner_plan.principal_callee, &inner_substitutions);
            let (_, body_ret) = core_fun_spine_exact(&inner_callee, body_spine.args.len())?;
            body_ret
        } else {
            let Some(body_ret) = principal_plan_result_closed_type(&inner_plan.result) else {
                self.bump("principal-unify-body-result-skip-open-inner-result");
                return None;
            };
            body_ret
        };

        let mut plan = plan.clone();
        plan.result.expected_runtime = Some(body_ret);
        let normalized = normalize_principal_elaboration_plan_with_role_impls(
            plan,
            &[],
            &original.scheme.requirements,
            &self.role_associated_impls,
        );
        if normalized.complete {
            Some(normalized)
        } else {
            self.bump("principal-unify-body-result-still-incomplete");
            None
        }
    }

    fn intern_specialization(
        &mut self,
        original: Binding,
        mut substitutions: BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
        handler_plan: Option<HandlerAdapterPlan>,
        input_shapes: Option<Vec<typed_ir::Type>>,
        mut output_shape: Option<typed_ir::Type>,
    ) -> Option<typed_ir::Path> {
        let requested_output_shape = output_shape.clone();
        output_shape = self.refine_contextual_specialization(
            &original,
            &mut substitutions,
            input_shapes.as_deref(),
            output_shape.as_ref(),
        )?;
        if handler_plan.is_some()
            && let Some(output) = output_shape.clone().or(requested_output_shape)
        {
            narrow_handler_output_substitution(
                &original.scheme.body,
                input_shapes.as_ref().map_or(0, Vec::len),
                &mut substitutions,
                &output,
            );
            output_shape = Some(output);
        }
        if substitutions.is_empty()
            && handler_plan.is_none()
            && input_shapes.is_none()
            && output_shape.is_none()
        {
            return Some(original.name);
        }
        let key = principal_unify_key(
            &original.name,
            &substitutions,
            handler_plan.as_ref(),
            input_shapes.as_deref(),
            output_shape.as_ref(),
        );
        if let Some(path) = self.specializations.get(&key) {
            return Some(path.clone());
        }
        let path = principal_unified_path(&original.name, self.next_index);
        self.next_index += 1;
        self.specializations.insert(key, path.clone());
        self.root_specializations
            .entry(original.name.clone())
            .or_default()
            .push(path.clone());
        self.register_module_specialization(&path);
        debug_principal_unify_emit(&original.name, &path, &substitutions);
        self.pending_specializations
            .push_back(PendingPrincipalSpecialization {
                original,
                substitutions,
                handler_plan,
                input_shapes,
                output_shape,
                path: path.clone(),
            });
        Some(path)
    }

    fn refine_contextual_specialization(
        &mut self,
        original: &Binding,
        substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
        input_shapes: Option<&[typed_ir::Type]>,
        output_shape: Option<&typed_ir::Type>,
    ) -> Option<Option<typed_ir::Type>> {
        let arity = input_shapes.map_or(0, <[typed_ir::Type]>::len);
        if arity == 0 && output_shape.is_none() {
            return Some(None);
        }
        let required_vars = binding_required_vars(original);
        let mut ret_template = None;
        if let Some(input_shapes) = input_shapes {
            let Some((params, ret, _ret_effect)) =
                core_fun_spine_parts_exact(&original.scheme.body, input_shapes.len())
            else {
                return Some(output_shape.cloned());
            };
            let before_input_refinement = substitutions.clone();
            let mut conflicts = BTreeSet::new();
            for ((param, _param_effect), input_shape) in params.iter().zip(input_shapes) {
                project_contextual_input_value_substitutions_from_type(
                    param,
                    input_shape,
                    &required_vars,
                    substitutions,
                    &mut conflicts,
                    64,
                );
            }
            if !conflicts.is_empty() {
                if required_vars_are_closed(&required_vars, &before_input_refinement) {
                    *substitutions = before_input_refinement;
                    self.bump("principal-unify-context-input-conflict-ignored");
                    ret_template = Some(ret);
                    if output_shape.is_none() {
                        return Some(None);
                    }
                } else {
                    self.bump("principal-unify-context-input-conflict");
                    return None;
                }
            } else {
                ret_template = Some(ret);
            }
        } else if output_shape.is_some()
            && let Some((_params, ret, _ret_effect)) =
                core_fun_spine_parts_exact(&original.scheme.body, arity)
        {
            ret_template = Some(ret);
        }
        let Some(output_shape) = output_shape else {
            return Some(None);
        };
        let Some(ret_template) = ret_template else {
            return Some(Some(output_shape.clone()));
        };
        let mut output_substitutions = substitutions.clone();
        let mut conflicts = BTreeSet::new();
        project_closed_value_substitutions_from_type(
            &ret_template,
            output_shape,
            &required_vars,
            &mut output_substitutions,
            &mut conflicts,
            64,
        );
        if !conflicts.is_empty() {
            if input_shapes.is_some() {
                self.bump("principal-unify-context-output-conflict-ignored");
                return Some(None);
            }
            self.bump("principal-unify-context-output-conflict");
            return None;
        }
        let specialized_ret = substitute_type(&ret_template, &output_substitutions);
        if !contextual_output_shape_matches(&specialized_ret, output_shape) {
            if input_shapes.is_some() {
                self.bump("principal-unify-context-output-mismatch-ignored");
                return Some(None);
            }
            self.bump("principal-unify-context-output-mismatch");
            return None;
        }
        *substitutions = output_substitutions;
        Some(Some(output_shape.clone()))
    }

    fn process_pending_specializations(&mut self) {
        while let Some(request) = self.pending_specializations.pop_front() {
            self.emit_pending_specialization(request);
        }
    }

    fn settle_pending_specializations(&mut self) {
        loop {
            self.process_pending_specializations();
            self.rewrite_emitted_specialization_bodies();
            if self.pending_specializations.is_empty() {
                return;
            }
        }
    }

    fn rewrite_emitted_specialization_bodies(&mut self) {
        let emitted = std::mem::take(&mut self.emitted);
        let mut rewritten = Vec::with_capacity(emitted.len());
        for mut binding in emitted {
            let original_ty = binding.body.ty.clone();
            let original_scheme = binding.scheme.body.clone();
            let body_context = Self::binding_body_runtime_context(&binding);
            let body = refresh_local_expr_types(binding.body);
            self.push_rewrite_context("emitted-specialization");
            let body = self.rewrite_expr(body, body_context);
            self.pop_rewrite_context();
            binding.body =
                retag_runtime_expr_spine_type(project_runtime_expr_types(body), original_ty);
            binding.scheme.body = original_scheme;
            self.emitted_by_path
                .insert(binding.name.clone(), binding.clone());
            rewritten.push(binding);
        }
        self.emitted = rewritten;
    }

    fn emit_pending_specialization(&mut self, request: PendingPrincipalSpecialization) {
        if self.emitted_by_path.contains_key(&request.path) {
            return;
        }
        let PendingPrincipalSpecialization {
            original,
            substitutions,
            mut handler_plan,
            input_shapes,
            output_shape,
            path,
        } = request;
        let original_name = original.name.clone();
        let started = self.profile_timer();
        let mut binding = substitute_binding(original, &substitutions);
        self.finish_profile_timer("intern-substitute-binding", started);
        self.record_target_phase_timing(&original_name, "intern-substitute-binding", started);
        let active_handler_plan = handler_plan.clone();
        binding.name = path.clone();
        binding.type_params.clear();
        self.active_specializations
            .push(ActivePrincipalSpecialization {
                target: original_name.clone(),
                substitutions: substitutions.clone(),
                path: path.clone(),
                handler_plan: active_handler_plan,
                input_shapes: input_shapes.clone(),
                output_shape: output_shape.clone(),
            });
        let preplanned_handler = handler_plan.is_some();
        if let Some(plan) = handler_plan.as_ref() {
            binding = self.apply_intern_handler_plan(binding, &original_name, &path, plan);
        }
        let binding_body_context = specialization_binding_body_context(
            &binding.scheme.body,
            input_shapes.as_deref(),
            output_shape.as_ref(),
        );
        binding =
            self.rewrite_intern_specialization_body(binding, binding_body_context, &original_name);
        if handler_plan.is_none() {
            handler_plan = rewritten_binding_handler_adapter_plan(&binding);
        }
        self.active_specializations.pop();
        if let Some(plan) = handler_plan
            && !preplanned_handler
        {
            binding = self.apply_intern_handler_plan(binding, &original_name, &path, &plan);
        }
        if let Some(output_shape) = &output_shape
            && let Some(contextual_scheme) = core_fun_spine_with_output_shape(
                &binding.scheme.body,
                input_shapes.as_ref().map_or(0, Vec::len),
                output_shape,
            )
        {
            binding.scheme.body = contextual_scheme.clone();
            binding.body.ty = normalize_hir_function_type(RuntimeType::core(contextual_scheme));
        }
        let started = self.profile_timer();
        binding.body = refresh_local_expr_types(binding.body);
        binding.body = project_runtime_expr_types(binding.body);
        binding.scheme.body =
            project_runtime_type_with_vars(&runtime_core_type(&binding.body.ty), &BTreeSet::new());
        if let Some(contextual_scheme) = contextual_specialization_scheme(
            &binding.scheme.body,
            input_shapes.as_deref(),
            output_shape.as_ref(),
        )
        .filter(|contextual_scheme| {
            Self::contextual_specialization_scheme_preserves_precision(
                contextual_scheme,
                &binding.body.ty,
            )
        }) {
            binding.scheme.body = contextual_scheme.clone();
            binding.body = retag_runtime_expr_spine_type(
                binding.body,
                normalize_hir_function_type(RuntimeType::core(contextual_scheme)),
            );
        }
        self.finish_profile_timer("intern-final-refresh-project", started);
        self.record_target_phase_timing(&original_name, "intern-final-refresh-project", started);
        self.emitted_by_path.insert(path.clone(), binding.clone());
        self.emitted.push(binding);
    }

    fn apply_intern_handler_plan(
        &mut self,
        mut binding: Binding,
        original_name: &typed_ir::Path,
        path: &typed_ir::Path,
        plan: &HandlerAdapterPlan,
    ) -> Binding {
        let started = self.profile_timer();
        self.handler_specialization_paths.insert(path.clone());
        binding = apply_handler_adapter_plan_to_binding(binding, plan);
        binding.body = refresh_handle_payloads_from_handlers(binding.body);
        self.finish_profile_timer("intern-apply-handler-plan", started);
        self.record_target_phase_timing(original_name, "intern-apply-handler-plan", started);
        binding
    }

    fn rewrite_intern_specialization_body(
        &mut self,
        mut binding: Binding,
        binding_body_context: typed_ir::TypeBounds,
        original_name: &typed_ir::Path,
    ) -> Binding {
        let started = self.profile_timer();
        self.push_rewrite_context("intern");
        let binding_body_context_ty = closed_type_from_bounds(Some(&binding_body_context));
        binding.body = self.rewrite_expr(binding.body, Some(binding_body_context));
        if let Some(context_ty) = binding_body_context_ty {
            binding.body = retag_runtime_expr_spine_type(
                binding.body,
                normalize_hir_function_type(RuntimeType::core(context_ty)),
            );
        }
        self.pop_rewrite_context();
        self.finish_profile_timer("intern-rewrite-body", started);
        self.record_target_phase_timing(original_name, "intern-rewrite-body", started);
        binding
    }

    fn contextual_specialization_scheme_preserves_precision(
        contextual_scheme: &typed_ir::Type,
        current_ty: &RuntimeType,
    ) -> bool {
        let contextual_ty =
            normalize_hir_function_type(RuntimeType::core(contextual_scheme.clone()));
        runtime_type_shape_usable(&contextual_ty) || !runtime_type_shape_usable(current_ty)
    }

    fn intern_effect_context_specialization(
        &mut self,
        mut binding: Binding,
        arity: usize,
        effect: &typed_ir::Type,
        substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
        input_shapes: Option<Vec<typed_ir::Type>>,
    ) -> Option<typed_ir::Path> {
        let key = format!(
            "{}|effect-context-arity={arity}|effect={effect:?}|subst={substitutions:?}|inputs={input_shapes:?}",
            canonical_path(&binding.name),
        );
        if let Some(path) = self.specializations.get(&key) {
            return Some(path.clone());
        }
        let original_name = binding.name.clone();
        let path = principal_unified_path(&binding.name, self.next_index);
        self.next_index += 1;
        self.specializations.insert(key, path.clone());
        self.register_module_specialization(&path);
        debug_principal_unify_emit(&original_name, &path, &BTreeMap::new());
        binding.name = path.clone();
        binding.type_params.clear();
        self.active_specializations
            .push(ActivePrincipalSpecialization {
                target: original_name.clone(),
                substitutions: substitutions.clone(),
                path: path.clone(),
                handler_plan: None,
                input_shapes: input_shapes.clone(),
                output_shape: None,
            });
        let binding_body_context = specialization_binding_body_context(
            &binding.scheme.body,
            input_shapes.as_deref(),
            None,
        );
        let started = self.profile_timer();
        self.push_rewrite_context("effect-context");
        binding.body = self.rewrite_expr(binding.body, Some(binding_body_context));
        self.pop_rewrite_context();
        self.finish_profile_timer("effect-context-rewrite-body", started);
        let handler_plan = rewritten_binding_handler_adapter_plan(&binding)
            .filter(|plan| effect_contains_any(effect, &plan.consumes));
        self.active_specializations.pop();
        if let Some(plan) = handler_plan {
            let started = self.profile_timer();
            self.handler_specialization_paths.insert(path.clone());
            binding = apply_handler_adapter_plan_to_binding(binding, &plan);
            binding.body = force_outer_handler_lambda_param(binding.body, &plan);
            binding.body = refresh_handle_payloads_from_handlers(binding.body);
            self.finish_profile_timer("effect-context-apply-handler-plan", started);
        }
        let started = self.profile_timer();
        binding.body = refresh_local_expr_types(binding.body);
        binding.body = project_runtime_expr_types(binding.body);
        binding.scheme.body = runtime_core_type(&binding.body.ty);
        self.finish_profile_timer("effect-context-final-refresh-project", started);
        self.emitted_by_path.insert(path.clone(), binding.clone());
        self.emitted.push(binding);
        Some(path)
    }

    fn active_specialization_for(
        &self,
        target: &typed_ir::Path,
    ) -> Option<&ActivePrincipalSpecialization> {
        self.active_specializations
            .iter()
            .rev()
            .find(|active| &active.target == target)
    }

    fn active_context_substitutions(&self) -> Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
        let mut substitutions = BTreeMap::new();
        for active in &self.active_specializations {
            for (var, ty) in &active.substitutions {
                substitutions.insert(var.clone(), ty.clone());
            }
        }
        (!substitutions.is_empty()).then_some(substitutions)
    }

    fn monomorphic_binding_type(&self, path: &typed_ir::Path) -> Option<RuntimeType> {
        let binding = self.bindings_by_path.get(path)?;
        if !closed_slot_type_usable(&binding.scheme.body, false) {
            return None;
        }
        Some(RuntimeType::core(binding.scheme.body.clone()))
    }

    fn known_binding_runtime_type(&self, path: &typed_ir::Path) -> Option<RuntimeType> {
        self.emitted_by_path
            .get(path)
            .map(|binding| binding.body.ty.clone())
    }

    fn single_emitted_specialization(
        &self,
        path: &typed_ir::Path,
    ) -> Option<(typed_ir::Path, RuntimeType)> {
        let specializations = self.root_specializations.get(path)?;
        let [specialized] = specializations.as_slice() else {
            return None;
        };
        let binding = self.emitted_binding(specialized)?;
        Some((specialized.clone(), binding.body.ty.clone()))
    }

    fn single_local_emitted_specialization(
        &self,
        path: &typed_ir::Path,
    ) -> Option<(typed_ir::Path, RuntimeType)> {
        (path.segments.len() == 1)
            .then(|| self.single_emitted_specialization(path))
            .flatten()
    }

    fn rewrite_nullary_generic_from_context(
        &mut self,
        path: &typed_ir::Path,
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> Option<Expr> {
        let original = self.generic_binding(path).cloned()?;
        if core_fun_spine_exact(&original.scheme.body, 1).is_some() {
            return None;
        }
        let substitutions = self
            .nullary_generic_substitutions_from_context(&original, result_context)
            .or_else(|| self.nullary_generic_substitutions_from_active_context(&original))?;
        let specialized_ty = substitute_type(&original.scheme.body, &substitutions);
        let specialized = self.intern_specialization(original, substitutions, None, None, None)?;
        self.bump("principal-unify-nullary-context-rewrite");
        Some(Expr::typed(
            ExprKind::Var(specialized),
            RuntimeType::core(specialized_ty),
        ))
    }

    fn nullary_generic_substitutions_from_context(
        &mut self,
        original: &Binding,
        result_context: Option<&typed_ir::TypeBounds>,
    ) -> Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
        let required = self.required_vars_for_binding(original);
        if required.is_empty() {
            return None;
        }
        let context = closed_type_from_bounds(result_context)?;
        let mut substitutions = BTreeMap::new();
        let mut conflicts = BTreeSet::new();
        project_closed_substitutions_from_type(
            &original.scheme.body,
            &context,
            &required,
            &mut substitutions,
            &mut conflicts,
            false,
            64,
        );
        if !conflicts.is_empty() {
            self.bump_skip(&original.name, "nullary-context-conflict");
            return None;
        }
        complete_required_substitutions(original, &substitutions)
    }

    fn nullary_generic_substitutions_from_active_context(
        &self,
        original: &Binding,
    ) -> Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
        let required = self.required_vars_for_binding(original);
        if required.is_empty() {
            return None;
        }
        let active = self.active_context_substitutions()?;
        let mut matches = Vec::<BTreeMap<typed_ir::TypeVar, typed_ir::Type>>::new();
        for ty in active.values() {
            let ty = substitute_type(ty, &active);
            if !closed_slot_type_usable(&ty, false) {
                continue;
            }
            let mut substitutions = BTreeMap::new();
            let mut conflicts = BTreeSet::new();
            project_closed_substitutions_from_type(
                &original.scheme.body,
                &ty,
                &required,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
            if !conflicts.is_empty() {
                continue;
            }
            let Some(substitutions) = complete_required_substitutions(original, &substitutions)
            else {
                continue;
            };
            if !matches.iter().any(|existing| existing == &substitutions) {
                matches.push(substitutions);
            }
        }
        let [substitutions] = matches.as_slice() else {
            return None;
        };
        Some(substitutions.clone())
    }

    fn expr_is_nullary_generic_var(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Var(path) => self
                .generic_binding(path)
                .is_some_and(|binding| core_fun_spine_exact(&binding.scheme.body, 1).is_none()),
            ExprKind::Thunk { expr, .. }
            | ExprKind::LocalPushId { body: expr, .. }
            | ExprKind::Pack { expr, .. }
            | ExprKind::BindHere { expr }
            | ExprKind::Coerce { expr, .. } => self.expr_is_nullary_generic_var(expr),
            ExprKind::Block {
                tail: Some(tail), ..
            } => self.expr_is_nullary_generic_var(tail),
            ExprKind::AddId { thunk, .. } => self.expr_is_nullary_generic_var(thunk),
            _ => false,
        }
    }
}

fn project_container_callback_item_from_args(
    principal: &typed_ir::Type,
    args: &[&Expr],
    _required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    if args.len() < 2 {
        return;
    }
    let Some(item) = unary_container_item_type(&args[0].ty) else {
        return;
    };
    let Some((params, _ret, _ret_effect)) = core_fun_spine_parts_exact(principal, args.len())
    else {
        return;
    };
    let Some((callback, _callback_effect)) = params.get(1) else {
        return;
    };
    let Some(var) = callback_item_param_var(callback) else {
        return;
    };
    match substitutions.get(&var) {
        Some(existing) if existing == &item => {}
        Some(existing) if type_is_open_or_default_unit(existing) => {
            substitutions.insert(var, item);
        }
        Some(_) => {}
        None => {
            substitutions.insert(var, item);
        }
    }
}

fn project_predicate_result_container_item_from_args(
    ret: &typed_ir::Type,
    args: &[&Expr],
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    let Some(result_item_var) = unary_container_item_var(ret) else {
        return;
    };
    if !required_vars.contains(&result_item_var) || substitutions.contains_key(&result_item_var) {
        return;
    }
    let Some(callback_param) = args
        .iter()
        .skip(1)
        .filter_map(|arg| predicate_callback_param_type(&arg.ty))
        .find(|ty| closed_slot_type_usable(ty, false))
    else {
        return;
    };
    insert_exact_projected_substitution(substitutions, conflicts, result_item_var, callback_param);
}

fn predicate_callback_param_type(ty: &RuntimeType) -> Option<typed_ir::Type> {
    let RuntimeType::Fun { param, ret } = ty else {
        return None;
    };
    let RuntimeType::Core(ret) = ret.as_ref() else {
        return None;
    };
    is_bool_core_type(ret).then(|| runtime_core_type(param))
}

fn is_bool_core_type(ty: &typed_ir::Type) -> bool {
    matches!(
        ty,
        typed_ir::Type::Named { path, args }
            if args.is_empty()
                && path.segments.as_slice() == [typed_ir::Name("bool".to_string())]
    )
}

fn clear_erased_function_arg_effect_vars(
    params: &[(typed_ir::Type, typed_ir::Type)],
    args: &[&Expr],
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    for (arg, (param, _param_effect)) in args.iter().zip(params) {
        let RuntimeType::Fun { ret, .. } = &arg.ty else {
            continue;
        };
        let (_actual_ret, actual_ret_effect) = runtime_value_and_effect(ret);
        if !effect_is_empty(&actual_ret_effect) {
            continue;
        }
        let mut vars = BTreeSet::new();
        collect_function_effect_vars(param, &mut vars);
        for var in vars {
            if required_vars.contains(&var) {
                substitutions.insert(var.clone(), typed_ir::Type::Never);
                conflicts.remove(&var);
            }
        }
    }
}

fn collect_function_effect_vars(ty: &typed_ir::Type, out: &mut BTreeSet<typed_ir::TypeVar>) {
    let typed_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = ty
    else {
        return;
    };
    collect_core_type_vars(param_effect, out);
    collect_core_type_vars(ret_effect, out);
    collect_function_effect_vars(param, out);
    collect_function_effect_vars(ret, out);
}

fn unary_container_item_var(ty: &typed_ir::Type) -> Option<typed_ir::TypeVar> {
    let typed_ir::Type::Named { args, .. } = ty else {
        return None;
    };
    let [arg] = args.as_slice() else {
        return None;
    };
    type_arg_var(arg)
}

fn type_arg_var(arg: &typed_ir::TypeArg) -> Option<typed_ir::TypeVar> {
    match arg {
        typed_ir::TypeArg::Type(typed_ir::Type::Var(var)) => Some(var.clone()),
        typed_ir::TypeArg::Bounds(bounds) => match (&bounds.lower, &bounds.upper) {
            (Some(lower), Some(upper)) if lower == upper => match lower.as_ref() {
                typed_ir::Type::Var(var) => Some(var.clone()),
                _ => None,
            },
            (Some(bound), None) | (None, Some(bound)) => match bound.as_ref() {
                typed_ir::Type::Var(var) => Some(var.clone()),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn unary_container_item_type(ty: &RuntimeType) -> Option<typed_ir::Type> {
    unary_container_item_type_from_core(&runtime_core_type(ty))
}

fn unary_container_item_type_from_core(ty: &typed_ir::Type) -> Option<typed_ir::Type> {
    let typed_ir::Type::Named { args, .. } = ty else {
        return None;
    };
    let [arg] = args.as_slice() else {
        return None;
    };
    type_arg_closed_type(arg)
}

fn project_unary_container_item_from_param_actual(
    param: &typed_ir::Type,
    actual: &typed_ir::Type,
    _required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    let Some(var) = unary_container_item_var(param) else {
        return;
    };
    let Some(item) = unary_container_item_type_from_core(actual) else {
        return;
    };
    insert_projected_container_item_substitution(substitutions, var, item);
}

fn insert_projected_container_item_substitution(
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    var: typed_ir::TypeVar,
    item: typed_ir::Type,
) {
    match substitutions.get(&var) {
        Some(existing) if existing == &item => {}
        Some(existing) if type_is_open_or_default_unit(existing) => {
            substitutions.insert(var, item);
        }
        Some(existing) => {
            if let Some(merged) = merge_projected_value_type_precision(existing, &item) {
                substitutions.insert(var, merged);
            }
        }
        None => {
            substitutions.insert(var, item);
        }
    }
}

fn type_arg_closed_type(arg: &typed_ir::TypeArg) -> Option<typed_ir::Type> {
    match arg {
        typed_ir::TypeArg::Type(ty)
            if closed_slot_type_usable(ty, false) || function_runtime_slot_usable(ty) =>
        {
            Some(ty.clone())
        }
        typed_ir::TypeArg::Bounds(bounds) => closed_type_from_bounds(Some(bounds)).or_else(|| {
            bounds
                .lower
                .as_deref()
                .or(bounds.upper.as_deref())
                .filter(|ty| function_runtime_slot_usable(ty))
                .cloned()
        }),
        _ => None,
    }
}

fn callback_item_param_var(callback: &typed_ir::Type) -> Option<typed_ir::TypeVar> {
    let mut current = callback;
    let mut item_var = None;
    while let typed_ir::Type::Fun { param, ret, .. } = current {
        if let typed_ir::Type::Var(var) = param.as_ref() {
            item_var = Some(var.clone());
        }
        current = ret;
    }
    item_var
}

fn type_is_open_or_default_unit(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Any => true,
        typed_ir::Type::Tuple(items) => items.is_empty(),
        _ => false,
    }
}

fn handler_call_boundary_refs(
    info: &HandlerBindingInfo,
    args: &[Expr],
    result_ty: &RuntimeType,
) -> HandlerCallBoundary {
    let args = args.iter().collect::<Vec<_>>();
    handler_call_boundary(info, &args, result_ty)
}

fn principal_rewrite_expr_kind_name(kind: &ExprKind) -> &'static str {
    match kind {
        ExprKind::Apply { .. } => "apply",
        ExprKind::Lambda { .. } => "lambda",
        ExprKind::If { .. } => "if",
        ExprKind::Tuple(_) => "tuple",
        ExprKind::Record { .. } => "record",
        ExprKind::Variant { .. } => "variant",
        ExprKind::Select { .. } => "select",
        ExprKind::Match { .. } => "match",
        ExprKind::Block { .. } => "block",
        ExprKind::Handle { .. } => "handle",
        ExprKind::BindHere { .. } => "bind-here",
        ExprKind::Thunk { .. } => "thunk",
        ExprKind::LocalPushId { .. } => "local-push-id",
        ExprKind::AddId { .. } => "add-id",
        ExprKind::Coerce { .. } => "coerce",
        ExprKind::Pack { .. } => "pack",
        ExprKind::Var(_) => "var",
        ExprKind::EffectOp(_) => "effect-op",
        ExprKind::PrimitiveOp(_) => "primitive-op",
        ExprKind::Lit(_) => "lit",
        ExprKind::PeekId => "peek-id",
        ExprKind::FindId { .. } => "find-id",
    }
}

fn principal_rewrite_expr_kind_count_key(kind: &str) -> &'static str {
    match kind {
        "apply" => "principal-rewrite-expr-apply",
        "lambda" => "principal-rewrite-expr-lambda",
        "if" => "principal-rewrite-expr-if",
        "tuple" => "principal-rewrite-expr-tuple",
        "record" => "principal-rewrite-expr-record",
        "variant" => "principal-rewrite-expr-variant",
        "select" => "principal-rewrite-expr-select",
        "match" => "principal-rewrite-expr-match",
        "block" => "principal-rewrite-expr-block",
        "handle" => "principal-rewrite-expr-handle",
        "bind-here" => "principal-rewrite-expr-bind-here",
        "thunk" => "principal-rewrite-expr-thunk",
        "local-push-id" => "principal-rewrite-expr-local-push-id",
        "add-id" => "principal-rewrite-expr-add-id",
        "coerce" => "principal-rewrite-expr-coerce",
        "pack" => "principal-rewrite-expr-pack",
        "var" => "principal-rewrite-expr-var",
        "effect-op" => "principal-rewrite-expr-effect-op",
        "primitive-op" => "principal-rewrite-expr-primitive-op",
        "lit" => "principal-rewrite-expr-lit",
        "peek-id" => "principal-rewrite-expr-peek-id",
        "find-id" => "principal-rewrite-expr-find-id",
        _ => "principal-rewrite-expr-unknown",
    }
}

fn principal_rewrite_expr_kind_timing_key(kind: &str) -> &'static str {
    match kind {
        "apply" => "rewrite-expr-apply",
        "lambda" => "rewrite-expr-lambda",
        "if" => "rewrite-expr-if",
        "tuple" => "rewrite-expr-tuple",
        "record" => "rewrite-expr-record",
        "variant" => "rewrite-expr-variant",
        "select" => "rewrite-expr-select",
        "match" => "rewrite-expr-match",
        "block" => "rewrite-expr-block",
        "handle" => "rewrite-expr-handle",
        "bind-here" => "rewrite-expr-bind-here",
        "thunk" => "rewrite-expr-thunk",
        "local-push-id" => "rewrite-expr-local-push-id",
        "add-id" => "rewrite-expr-add-id",
        "coerce" => "rewrite-expr-coerce",
        "pack" => "rewrite-expr-pack",
        "var" => "rewrite-expr-var",
        "effect-op" => "rewrite-expr-effect-op",
        "primitive-op" => "rewrite-expr-primitive-op",
        "lit" => "rewrite-expr-lit",
        "peek-id" => "rewrite-expr-peek-id",
        "find-id" => "rewrite-expr-find-id",
        _ => "rewrite-expr-unknown",
    }
}

fn principal_rewrite_expr_kind_profile_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("YULANG_PRINCIPAL_REWRITE_KIND_PROFILE").is_some())
}

struct PrincipalUnifyApplySpine<'a> {
    target: &'a typed_ir::Path,
    args: Vec<&'a Expr>,
    evidences: Vec<Option<&'a typed_ir::ApplyEvidence>>,
}

fn principal_unify_apply_spine(expr: &Expr) -> Option<PrincipalUnifyApplySpine<'_>> {
    let mut current = expr;
    let mut args = Vec::new();
    let mut evidences = Vec::new();
    loop {
        match &current.kind {
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                ..
            } => {
                args.push(arg.as_ref());
                evidences.push(evidence.as_ref());
                current = callee;
            }
            ExprKind::BindHere { expr } => {
                current = expr;
            }
            _ => break,
        }
    }
    let target = match &current.kind {
        ExprKind::Var(target) | ExprKind::EffectOp(target) => target,
        _ => return None,
    };
    args.reverse();
    evidences.reverse();
    Some(PrincipalUnifyApplySpine {
        target,
        args,
        evidences,
    })
}

fn binding_body_after_applied_args(expr: &Expr, arity: usize) -> Option<&Expr> {
    let mut body = expr;
    for _ in 0..arity {
        let ExprKind::Lambda { body: next, .. } = &body.kind else {
            return None;
        };
        body = next;
    }
    Some(block_tail_expr(body))
}

fn block_tail_expr(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Block {
        stmts,
        tail: Some(tail),
    } = &current.kind
    {
        if !stmts.is_empty() {
            break;
        }
        current = tail;
    }
    current
}

fn ret_effect_has_unfilled_required_var(
    ret_effect: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> bool {
    let mut ret_effect_vars = BTreeSet::new();
    collect_core_type_vars(ret_effect, &mut ret_effect_vars);
    ret_effect_vars.into_iter().any(|var| {
        required_vars.contains(&var)
            && substitutions
                .get(&var)
                .is_none_or(|ty| matches!(ty, typed_ir::Type::Unknown | typed_ir::Type::Any))
    })
}

fn plan_substitution_map(
    plan: &typed_ir::PrincipalElaborationPlan,
) -> BTreeMap<typed_ir::TypeVar, typed_ir::Type> {
    plan.substitutions
        .iter()
        .map(|substitution| (substitution.var.clone(), substitution.ty.clone()))
        .collect()
}

fn incomplete_plan_cache_key(
    spine: &PrincipalUnifyApplySpine<'_>,
    expr: &Expr,
    result_context: Option<&typed_ir::TypeBounds>,
    active_context_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) -> IncompletePrincipalPlanKey {
    IncompletePrincipalPlanKey {
        target: spine.target.clone(),
        arg_types: spine.args.iter().map(|arg| arg.ty.clone()).collect(),
        result_type: expr.ty.clone(),
        result_context: result_context.cloned(),
        active_context_substitutions: active_context_substitutions.cloned(),
    }
}

fn principal_plan_needs_runtime_effect_slots(
    original: &Binding,
    plan: &typed_ir::PrincipalElaborationPlan,
) -> bool {
    let binding_required_vars = binding_required_vars(original);
    let plan_substitutions = plan_substitution_map(plan);
    let effect_only_vars = binding_effect_only_vars(original);
    !plan.complete
        || !missing_required_vars(original, &plan_substitutions).is_empty()
        || binding_required_vars
            .iter()
            .any(|var| !plan_substitutions.contains_key(var))
        || binding_required_vars.iter().any(|var| {
            effect_only_vars.contains(var)
                && plan_substitutions.get(var).is_some_and(effect_is_empty)
        })
}

fn scoped_active_context_substitutions(
    binding: &Binding,
    active: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
    let mut binding_vars = binding_signature_vars(binding);
    binding_vars.extend(binding.type_params.iter().cloned());
    let substitutions = active
        .iter()
        .filter(|(var, _)| !binding_vars.contains(*var))
        .map(|(var, ty)| (var.clone(), ty.clone()))
        .collect::<BTreeMap<_, _>>();
    (!substitutions.is_empty()).then_some(substitutions)
}

fn role_associated_requirement_vars(
    requirements: &[typed_ir::RoleRequirement],
) -> BTreeSet<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    for requirement in requirements {
        for arg in &requirement.args {
            let typed_ir::RoleRequirementArg::Associated { bounds, .. } = arg else {
                continue;
            };
            if let Some(lower) = bounds.lower.as_deref() {
                collect_core_type_vars(lower, &mut vars);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_core_type_vars(upper, &mut vars);
            }
        }
    }
    vars
}

fn add_single_specialization_aliases(
    module: &mut Module,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
) {
    let binding_types_by_path = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.body.ty.clone()))
        .collect::<HashMap<_, _>>();
    let mut aliases = Vec::new();
    for (original, specializations) in root_specializations {
        let [specialized] = specializations.as_slice() else {
            continue;
        };
        let Some(ty) = binding_types_by_path.get(specialized).cloned() else {
            continue;
        };
        let alias = Binding {
            name: original.clone(),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: runtime_core_type(&ty),
            },
            body: Expr::typed(ExprKind::Var(specialized.clone()), ty),
        };
        module.bindings.retain(|binding| &binding.name != original);
        aliases.push(alias);
    }
    module.bindings.extend(aliases);
}

fn rewrite_single_specialization_refs(
    module: &mut Module,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
) {
    let binding_types = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.scheme.body.clone()))
        .collect::<HashMap<_, _>>();
    let handler_originals = handler_specialization_originals(module, root_specializations);
    let rewrites = root_specializations
        .iter()
        .filter_map(|(original, specializations)| {
            if handler_originals.contains(original) {
                return None;
            }
            let [specialized] = specializations.as_slice() else {
                return None;
            };
            Some((original.clone(), specialized.clone()))
        })
        .collect::<HashMap<_, _>>();
    if rewrites.is_empty() {
        return;
    }
    let specialized_paths = rewrites.values().cloned().collect::<HashSet<_>>();
    for expr in &mut module.root_exprs {
        rewrite_single_specialization_refs_expr(
            expr,
            &rewrites,
            &specialized_paths,
            &binding_types,
        );
    }
    for binding in &mut module.bindings {
        if rewrites.contains_key(&binding.name) {
            continue;
        }
        rewrite_single_specialization_refs_expr(
            &mut binding.body,
            &rewrites,
            &specialized_paths,
            &binding_types,
        );
    }
}

fn rewrite_contextual_specialization_refs(
    module: &mut Module,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
) {
    let binding_types = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.scheme.body.clone()))
        .collect::<HashMap<_, _>>();
    for expr in &mut module.root_exprs {
        rewrite_contextual_specialization_refs_expr(expr, root_specializations, &binding_types);
    }
    for binding in &mut module.bindings {
        rewrite_contextual_specialization_refs_expr(
            &mut binding.body,
            root_specializations,
            &binding_types,
        );
    }
}

fn remove_specialized_generic_originals(
    module: &mut Module,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
) {
    module.bindings.retain(|binding| {
        binding.type_params.is_empty() || !root_specializations.contains_key(&binding.name)
    });
    close_specialized_nested_effect_only_originals(module, root_specializations);
}

fn close_specialized_nested_effect_only_originals(
    module: &mut Module,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
) {
    for binding in &mut module.bindings {
        if binding.type_params.is_empty()
            || binding.name.segments.len() == 1
            || !root_specializations.contains_key(&binding.name)
        {
            continue;
        }
        let effect_only_vars = binding_effect_only_vars(binding);
        if !binding
            .type_params
            .iter()
            .all(|var| effect_only_vars.contains(var))
        {
            continue;
        }
        let substitutions = binding
            .type_params
            .iter()
            .cloned()
            .map(|var| (var, typed_ir::Type::Never))
            .collect::<BTreeMap<_, _>>();
        *binding = substitute_binding(binding.clone(), &substitutions);
        binding.type_params.clear();
    }
}

fn module_specializations_by_original(
    module: &Module,
) -> HashMap<typed_ir::Path, Vec<typed_ir::Path>> {
    let mut out = HashMap::<typed_ir::Path, Vec<typed_ir::Path>>::new();
    for binding in &module.bindings {
        let Some(original) = unspecialized_path(&binding.name) else {
            continue;
        };
        out.entry(original).or_default().push(binding.name.clone());
    }
    out
}

fn extend_specialization_rewrite_candidate_paths(
    paths: &mut HashSet<typed_ir::Path>,
    specializations_by_original: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
) {
    for (original, specializations) in specializations_by_original {
        paths.insert(original.clone());
        paths.extend(specializations.iter().cloned());
    }
}

fn binding_body_has_principal_rewrite_candidate(
    body: &Expr,
    candidate_paths: &HashSet<typed_ir::Path>,
) -> bool {
    let mut vars = HashSet::new();
    collect_expr_vars(body, &mut vars);
    vars.iter().any(|path| candidate_paths.contains(path))
        || expr_has_principal_rewrite_candidate_ref(body, candidate_paths)
}

fn expr_has_principal_rewrite_candidate_ref(
    expr: &Expr,
    candidate_paths: &HashSet<typed_ir::Path>,
) -> bool {
    match &expr.kind {
        ExprKind::EffectOp(path) => candidate_paths.contains(path),
        ExprKind::Lambda { body, .. } => {
            expr_has_principal_rewrite_candidate_ref(body, candidate_paths)
        }
        ExprKind::Apply {
            callee,
            arg,
            instantiation,
            ..
        } => {
            instantiation
                .as_ref()
                .is_some_and(|instantiation| candidate_paths.contains(&instantiation.target))
                || expr_has_principal_rewrite_candidate_ref(callee, candidate_paths)
                || expr_has_principal_rewrite_candidate_ref(arg, candidate_paths)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_has_principal_rewrite_candidate_ref(cond, candidate_paths)
                || expr_has_principal_rewrite_candidate_ref(then_branch, candidate_paths)
                || expr_has_principal_rewrite_candidate_ref(else_branch, candidate_paths)
        }
        ExprKind::Tuple(items) => items
            .iter()
            .any(|item| expr_has_principal_rewrite_candidate_ref(item, candidate_paths)),
        ExprKind::Record { fields, spread } => {
            fields.iter().any(|field| {
                expr_has_principal_rewrite_candidate_ref(&field.value, candidate_paths)
            }) || spread.as_ref().is_some_and(|spread| match spread {
                RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                    expr_has_principal_rewrite_candidate_ref(expr, candidate_paths)
                }
            })
        }
        ExprKind::Variant { value, .. } => value
            .as_deref()
            .is_some_and(|value| expr_has_principal_rewrite_candidate_ref(value, candidate_paths)),
        ExprKind::Select { base, .. } => {
            expr_has_principal_rewrite_candidate_ref(base, candidate_paths)
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            expr_has_principal_rewrite_candidate_ref(scrutinee, candidate_paths)
                || arms.iter().any(|arm| {
                    pattern_has_principal_rewrite_candidate_ref(&arm.pattern, candidate_paths)
                        || arm.guard.as_ref().is_some_and(|guard| {
                            expr_has_principal_rewrite_candidate_ref(guard, candidate_paths)
                        })
                        || expr_has_principal_rewrite_candidate_ref(&arm.body, candidate_paths)
                })
        }
        ExprKind::Block { stmts, tail } => {
            stmts
                .iter()
                .any(|stmt| stmt_has_principal_rewrite_candidate_ref(stmt, candidate_paths))
                || tail.as_deref().is_some_and(|tail| {
                    expr_has_principal_rewrite_candidate_ref(tail, candidate_paths)
                })
        }
        ExprKind::Handle { body, arms, .. } => {
            expr_has_principal_rewrite_candidate_ref(body, candidate_paths)
                || arms.iter().any(|arm| {
                    pattern_has_principal_rewrite_candidate_ref(&arm.payload, candidate_paths)
                        || arm.guard.as_ref().is_some_and(|guard| {
                            expr_has_principal_rewrite_candidate_ref(guard, candidate_paths)
                        })
                        || expr_has_principal_rewrite_candidate_ref(&arm.body, candidate_paths)
                })
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => {
            expr_has_principal_rewrite_candidate_ref(expr, candidate_paths)
        }
        ExprKind::LocalPushId { body, .. } => {
            expr_has_principal_rewrite_candidate_ref(body, candidate_paths)
        }
        ExprKind::AddId { thunk, .. } => {
            expr_has_principal_rewrite_candidate_ref(thunk, candidate_paths)
        }
        ExprKind::Var(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => false,
    }
}

fn stmt_has_principal_rewrite_candidate_ref(
    stmt: &Stmt,
    candidate_paths: &HashSet<typed_ir::Path>,
) -> bool {
    match stmt {
        Stmt::Let { pattern, value } => {
            pattern_has_principal_rewrite_candidate_ref(pattern, candidate_paths)
                || expr_has_principal_rewrite_candidate_ref(value, candidate_paths)
        }
        Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            expr_has_principal_rewrite_candidate_ref(value, candidate_paths)
        }
    }
}

fn pattern_has_principal_rewrite_candidate_ref(
    pattern: &Pattern,
    candidate_paths: &HashSet<typed_ir::Path>,
) -> bool {
    match pattern {
        Pattern::Tuple { items, .. } => items
            .iter()
            .any(|item| pattern_has_principal_rewrite_candidate_ref(item, candidate_paths)),
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            prefix
                .iter()
                .any(|item| pattern_has_principal_rewrite_candidate_ref(item, candidate_paths))
                || spread.as_deref().is_some_and(|spread| {
                    pattern_has_principal_rewrite_candidate_ref(spread, candidate_paths)
                })
                || suffix
                    .iter()
                    .any(|item| pattern_has_principal_rewrite_candidate_ref(item, candidate_paths))
        }
        Pattern::Record { fields, spread, .. } => {
            fields.iter().any(|field| {
                pattern_has_principal_rewrite_candidate_ref(&field.pattern, candidate_paths)
                    || field.default.as_ref().is_some_and(|default| {
                        expr_has_principal_rewrite_candidate_ref(default, candidate_paths)
                    })
            }) || spread.as_ref().is_some_and(|spread| match spread {
                RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                    pattern_has_principal_rewrite_candidate_ref(pattern, candidate_paths)
                }
            })
        }
        Pattern::Variant { value, .. } => value.as_deref().is_some_and(|value| {
            pattern_has_principal_rewrite_candidate_ref(value, candidate_paths)
        }),
        Pattern::Or { left, right, .. } => {
            pattern_has_principal_rewrite_candidate_ref(left, candidate_paths)
                || pattern_has_principal_rewrite_candidate_ref(right, candidate_paths)
        }
        Pattern::As { pattern, .. } => {
            pattern_has_principal_rewrite_candidate_ref(pattern, candidate_paths)
        }
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => false,
    }
}

fn handler_specialization_originals(
    module: &Module,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
) -> HashSet<typed_ir::Path> {
    module
        .bindings
        .iter()
        .filter(|binding| {
            root_specializations.contains_key(&binding.name)
                && binding.name.segments.len() > 1
                && handler_binding_info(binding).is_some()
        })
        .map(|binding| binding.name.clone())
        .collect()
}

fn rewrite_single_specialization_refs_expr(
    expr: &mut Expr,
    rewrites: &HashMap<typed_ir::Path, typed_ir::Path>,
    specialized_paths: &HashSet<typed_ir::Path>,
    binding_types: &HashMap<typed_ir::Path, typed_ir::Type>,
) {
    rewrite_single_specialization_refs_expr_inner(
        expr,
        rewrites,
        specialized_paths,
        binding_types,
        &mut BTreeSet::new(),
    );
}

fn rewrite_contextual_specialization_refs_expr(
    expr: &mut Expr,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    binding_types: &HashMap<typed_ir::Path, typed_ir::Type>,
) {
    rewrite_contextual_specialization_refs_expr_inner(
        expr,
        root_specializations,
        binding_types,
        &mut BTreeSet::new(),
    );
}

fn rewrite_contextual_specialization_refs_expr_inner(
    expr: &mut Expr,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    binding_types: &HashMap<typed_ir::Path, typed_ir::Type>,
    shadowed: &mut BTreeSet<typed_ir::Name>,
) {
    rewrite_contextual_specialization_refs_children(
        expr,
        root_specializations,
        binding_types,
        shadowed,
    );
    refresh_known_binding_expr_type(expr, binding_types, shadowed);
    if rewrite_contextual_leaf_specialization(expr, root_specializations, binding_types, shadowed) {
        return;
    }
    let Some(spine) = principal_unify_apply_spine(expr) else {
        return;
    };
    let lookup_target = unspecialized_path(spine.target).unwrap_or_else(|| spine.target.clone());
    if lookup_target
        .segments
        .as_slice()
        .first()
        .is_some_and(|name| lookup_target.segments.len() == 1 && shadowed.contains(name))
    {
        return;
    }
    let Some(candidates) = root_specializations.get(&lookup_target) else {
        return;
    };
    let current_specialized = (spine.target != &lookup_target).then_some(spine.target);
    let args = spine
        .args
        .iter()
        .map(|arg| (*arg).clone())
        .collect::<Vec<_>>();
    let mut matches = candidates
        .iter()
        .filter(|path| current_specialized.is_none_or(|current| current == *path))
        .filter_map(|path| {
            let ty = binding_types.get(path)?;
            let (params, _, _) = core_fun_spine_parts_exact(ty, args.len())?;
            if !owned_args_fit_contextual_specialization(&args, &params) {
                return None;
            }
            let context_score =
                rebuilt_specialization_call_score(ty, &args, &expr.ty, &spine.evidences)
                    .unwrap_or(0);
            let precision_score = rebuilt_specialization_precision_score(ty, args.len());
            Some((path, ty, context_score, precision_score))
        })
        .collect::<Vec<_>>();
    if let Some(best) = matches.iter().map(|(_, _, score, _)| *score).max() {
        matches.retain(|(_, _, score, _)| *score == best);
    }
    if let Some(best) = matches.iter().map(|(_, _, _, score)| *score).max() {
        matches.retain(|(_, _, _, score)| *score == best);
    }
    debug_principal_unify_contextual_candidates(spine.target, &matches);
    if matches.len() > 1
        && matches
            .first()
            .is_some_and(|(_, first_ty, _, _)| matches.iter().all(|(_, ty, _, _)| ty == first_ty))
    {
        let last = matches.pop().expect("non-empty contextual matches");
        matches.clear();
        matches.push(last);
    }
    if matches.len() > 1 && matches.iter().all(|(_, _, score, _)| *score >= 512) {
        let last = matches.pop().expect("non-empty contextual matches");
        matches.clear();
        matches.push(last);
    }
    if matches.len() != 1 {
        return;
    }
    let (path, ty, _context_score, _precision_score) =
        matches.pop().expect("single contextual specialization");
    if let Some(rewritten) = rebuild_apply_call_owned(path.clone(), ty.clone(), args, &expr.ty) {
        *expr = rewritten;
    }
}

fn rewrite_contextual_leaf_specialization(
    expr: &mut Expr,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    binding_types: &HashMap<typed_ir::Path, typed_ir::Type>,
    shadowed: &BTreeSet<typed_ir::Name>,
) -> bool {
    let path = match &expr.kind {
        ExprKind::Var(path)
            if !path
                .segments
                .as_slice()
                .first()
                .is_some_and(|name| path.segments.len() == 1 && shadowed.contains(name)) =>
        {
            path
        }
        ExprKind::EffectOp(path) => path,
        _ => return false,
    };
    let Some((path, ty)) =
        select_contextual_leaf_specialization(path, &expr.ty, root_specializations, binding_types)
    else {
        return false;
    };
    expr.kind = ExprKind::Var(path);
    expr.ty = ty;
    true
}

fn select_contextual_leaf_specialization(
    path: &typed_ir::Path,
    expr_ty: &RuntimeType,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    binding_types: &HashMap<typed_ir::Path, typed_ir::Type>,
) -> Option<(typed_ir::Path, RuntimeType)> {
    let candidates = root_specializations.get(path)?;
    let mut matches = candidates
        .iter()
        .filter_map(|candidate| {
            let ty = binding_types.get(candidate)?;
            let expected = normalize_hir_function_type(RuntimeType::core(ty.clone()));
            let score = runtime_rebuilt_type_score(expr_ty, &expected).unwrap_or(0);
            let precision = rebuilt_specialization_precision_score(ty, core_fun_arity(ty));
            Some((candidate.clone(), expected, score, precision))
        })
        .collect::<Vec<_>>();
    if let Some(best) = matches.iter().map(|(_, _, score, _)| *score).max() {
        matches.retain(|(_, _, score, _)| *score == best);
    }
    if let Some(best) = matches.iter().map(|(_, _, _, precision)| *precision).max() {
        matches.retain(|(_, _, _, precision)| *precision == best);
    }
    if matches.len() > 1 {
        let last = matches.pop().expect("non-empty contextual leaf matches");
        matches.clear();
        matches.push(last);
    }
    let (path, ty, _, _) = matches.pop().expect("single effect op specialization");
    Some((path, ty))
}

fn refresh_known_binding_expr_type(
    expr: &mut Expr,
    binding_types: &HashMap<typed_ir::Path, typed_ir::Type>,
    shadowed: &BTreeSet<typed_ir::Name>,
) {
    match &mut expr.kind {
        ExprKind::Var(path) => {
            if path
                .segments
                .as_slice()
                .first()
                .is_some_and(|name| path.segments.len() == 1 && shadowed.contains(name))
            {
                return;
            }
            if let Some(ty) = binding_types.get(path) {
                expr.ty = normalize_hir_function_type(RuntimeType::core(ty.clone()));
            }
        }
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            ..
        } => {
            if let Some(ty) = principal_rewrite_apply_type(&callee.ty)
                .or_else(|| principal_apply_type_from_evidence_arg(evidence.as_ref(), arg))
            {
                expr.ty = ty;
            }
        }
        _ => {}
    }
}

fn rewrite_contextual_specialization_refs_children(
    expr: &mut Expr,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    binding_types: &HashMap<typed_ir::Path, typed_ir::Type>,
    shadowed: &mut BTreeSet<typed_ir::Name>,
) {
    match &mut expr.kind {
        ExprKind::Apply { callee, arg, .. } => {
            if !contextual_specialization_direct_callee_should_wait(
                callee,
                root_specializations,
                shadowed,
            ) {
                rewrite_contextual_specialization_refs_expr_inner(
                    callee,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
            rewrite_contextual_specialization_refs_expr_inner(
                arg,
                root_specializations,
                binding_types,
                shadowed,
            );
        }
        ExprKind::Lambda { param, body, .. } => {
            let inserted = shadowed.insert(param.clone());
            rewrite_contextual_specialization_refs_expr_inner(
                body,
                root_specializations,
                binding_types,
                shadowed,
            );
            if inserted {
                shadowed.remove(param);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_contextual_specialization_refs_expr_inner(
                cond,
                root_specializations,
                binding_types,
                shadowed,
            );
            rewrite_contextual_specialization_refs_expr_inner(
                then_branch,
                root_specializations,
                binding_types,
                shadowed,
            );
            rewrite_contextual_specialization_refs_expr_inner(
                else_branch,
                root_specializations,
                binding_types,
                shadowed,
            );
        }
        ExprKind::Tuple(items) => {
            for item in items {
                rewrite_contextual_specialization_refs_expr_inner(
                    item,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                rewrite_contextual_specialization_refs_expr_inner(
                    &mut field.value,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
            if let Some(spread) = spread {
                let spread = match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => expr,
                };
                rewrite_contextual_specialization_refs_expr_inner(
                    spread,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                rewrite_contextual_specialization_refs_expr_inner(
                    value,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
        }
        ExprKind::Select { base, .. } => {
            rewrite_contextual_specialization_refs_expr_inner(
                base,
                root_specializations,
                binding_types,
                shadowed,
            );
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            rewrite_contextual_specialization_refs_expr_inner(
                scrutinee,
                root_specializations,
                binding_types,
                shadowed,
            );
            for arm in arms {
                let inserted = pattern_bind_name(&arm.pattern)
                    .map(|name| (name.clone(), shadowed.insert(name.clone())));
                if let Some(guard) = &mut arm.guard {
                    rewrite_contextual_specialization_refs_expr_inner(
                        guard,
                        root_specializations,
                        binding_types,
                        shadowed,
                    );
                }
                rewrite_contextual_specialization_refs_expr_inner(
                    &mut arm.body,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
                if let Some((name, true)) = inserted {
                    shadowed.remove(&name);
                }
            }
        }
        ExprKind::Block { stmts, tail } => {
            let saved = shadowed.clone();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { pattern, value } => {
                        rewrite_contextual_specialization_refs_expr_inner(
                            value,
                            root_specializations,
                            binding_types,
                            shadowed,
                        );
                        if let Some(name) = pattern_bind_name(pattern) {
                            shadowed.insert(name.clone());
                        }
                    }
                    Stmt::Module { def, body } => {
                        rewrite_contextual_specialization_refs_expr_inner(
                            body,
                            root_specializations,
                            binding_types,
                            shadowed,
                        );
                        if let [name] = def.segments.as_slice() {
                            shadowed.insert(name.clone());
                        }
                    }
                    Stmt::Expr(body) => rewrite_contextual_specialization_refs_expr_inner(
                        body,
                        root_specializations,
                        binding_types,
                        shadowed,
                    ),
                }
            }
            if let Some(tail) = tail {
                rewrite_contextual_specialization_refs_expr_inner(
                    tail,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
            *shadowed = saved;
        }
        ExprKind::Handle { body, arms, .. } => {
            rewrite_contextual_specialization_refs_expr_inner(
                body,
                root_specializations,
                binding_types,
                shadowed,
            );
            for arm in arms {
                let payload_inserted = pattern_bind_name(&arm.payload)
                    .map(|name| (name.clone(), shadowed.insert(name.clone())));
                let resume_inserted = arm
                    .resume
                    .as_ref()
                    .map(|resume| (resume.name.clone(), shadowed.insert(resume.name.clone())));
                if let Some(guard) = &mut arm.guard {
                    rewrite_contextual_specialization_refs_expr_inner(
                        guard,
                        root_specializations,
                        binding_types,
                        shadowed,
                    );
                }
                rewrite_contextual_specialization_refs_expr_inner(
                    &mut arm.body,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
                if let Some((name, true)) = resume_inserted {
                    shadowed.remove(&name);
                }
                if let Some((name, true)) = payload_inserted {
                    shadowed.remove(&name);
                }
            }
        }
        ExprKind::AddId { thunk, .. } => rewrite_contextual_specialization_refs_expr_inner(
            thunk,
            root_specializations,
            binding_types,
            shadowed,
        ),
        ExprKind::LocalPushId { body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::BindHere { expr: body } => rewrite_contextual_specialization_refs_expr_inner(
            body,
            root_specializations,
            binding_types,
            shadowed,
        ),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn contextual_specialization_direct_callee_should_wait(
    callee: &Expr,
    root_specializations: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    shadowed: &BTreeSet<typed_ir::Name>,
) -> bool {
    let path = match &callee.kind {
        ExprKind::Var(path)
            if !path
                .segments
                .as_slice()
                .first()
                .is_some_and(|name| path.segments.len() == 1 && shadowed.contains(name)) =>
        {
            path
        }
        ExprKind::EffectOp(path) => path,
        _ => return false,
    };
    root_specializations.contains_key(path)
}

fn rebuilt_specialization_call_score(
    callee_ty: &typed_ir::Type,
    args: &[Expr],
    final_ty: &RuntimeType,
    evidences: &[Option<&typed_ir::ApplyEvidence>],
) -> Option<usize> {
    let arity = args.len();
    let final_score =
        core_fun_spine_parts_exact(callee_ty, arity).and_then(|(_params, ret, ret_effect)| {
            let expected = runtime_type_from_core_value_and_effect(ret, ret_effect);
            runtime_rebuilt_type_score(final_ty, &expected)
        });
    let evidence_score = rebuilt_specialization_evidence_score(callee_ty, evidences);
    let effect_context_score =
        rebuilt_specialization_effect_context_score(callee_ty, arity, final_ty);
    let arg_effect_score = rebuilt_specialization_arg_effect_score(callee_ty, args)?;
    let mut total = 0;
    let mut has_signal = false;
    for score in [
        final_score,
        evidence_score,
        effect_context_score,
        arg_effect_score,
    ]
    .into_iter()
    .flatten()
    {
        total += score;
        has_signal = true;
    }
    has_signal.then_some(total)
}

fn rebuilt_specialization_arg_effect_score(
    callee_ty: &typed_ir::Type,
    args: &[Expr],
) -> Option<Option<usize>> {
    let (params, _ret, _ret_effect) = core_fun_spine_parts_exact(callee_ty, args.len())?;
    let mut total = 0usize;
    let mut has_signal = false;
    for (arg, (_param, param_effect)) in args.iter().zip(params) {
        let (_actual_value, actual_effect) = runtime_value_and_effect(&arg.ty);
        let actual_paths = effect_paths(&actual_effect);
        if actual_paths.is_empty() {
            continue;
        }
        let candidate_paths = effect_paths(&param_effect);
        if actual_paths.iter().any(|actual| {
            !candidate_paths
                .iter()
                .any(|candidate| effect_paths_match(candidate, actual))
        }) {
            return None;
        }
        let extra = candidate_paths
            .iter()
            .filter(|candidate| {
                !actual_paths
                    .iter()
                    .any(|actual| effect_paths_match(candidate, actual))
            })
            .count();
        total += 512usize.saturating_sub(extra * 16);
        has_signal = true;
    }
    Some(has_signal.then_some(total))
}

fn rebuilt_specialization_effect_context_score(
    callee_ty: &typed_ir::Type,
    arity: usize,
    final_ty: &RuntimeType,
) -> Option<usize> {
    let (_params, candidate_ret, candidate_ret_effect) =
        core_fun_spine_parts_exact(callee_ty, arity)?;
    let (actual_ret, actual_ret_effect) = runtime_value_and_effect(final_ty);
    let candidate_paths = core_result_effect_paths(&candidate_ret, &candidate_ret_effect);
    let actual_paths = core_result_effect_paths(&actual_ret, &actual_ret_effect);
    if actual_paths.is_empty() {
        return None;
    }
    if actual_paths.iter().any(|actual| {
        !candidate_paths
            .iter()
            .any(|candidate| effect_paths_match(candidate, actual))
    }) {
        return None;
    }
    let extra = candidate_paths
        .iter()
        .filter(|candidate| {
            !actual_paths
                .iter()
                .any(|actual| effect_paths_match(candidate, actual))
        })
        .count();
    Some(512usize.saturating_sub(extra * 16))
}

fn rebuilt_specialization_precision_score(callee_ty: &typed_ir::Type, arity: usize) -> usize {
    let Some((_params, ret, ret_effect)) = core_fun_spine_parts_exact(callee_ty, arity) else {
        return 0;
    };
    let effect_paths = core_result_effect_paths(&ret, &ret_effect).len();
    let imprecise = core_type_imprecision_score(&ret) + core_type_imprecision_score(&ret_effect);
    1024usize.saturating_sub(effect_paths * 8 + imprecise * 16)
}

fn core_type_imprecision_score(ty: &typed_ir::Type) -> usize {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => 1,
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_imprecision_score(param)
                + core_type_imprecision_score(param_effect)
                + core_type_imprecision_score(ret_effect)
                + core_type_imprecision_score(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().map(core_type_imprecision_score).sum(),
        typed_ir::Type::Record(record) => {
            let fields = record
                .fields
                .iter()
                .map(|field| core_type_imprecision_score(&field.value))
                .sum::<usize>();
            let spread = record
                .spread
                .as_ref()
                .map(|spread| match spread {
                    typed_ir::RecordSpread::Head(spread) | typed_ir::RecordSpread::Tail(spread) => {
                        core_type_imprecision_score(spread)
                    }
                })
                .unwrap_or(0);
            fields + spread
        }
        typed_ir::Type::Variant(variant) => {
            let payloads = variant
                .cases
                .iter()
                .flat_map(|case| &case.payloads)
                .map(core_type_imprecision_score)
                .sum::<usize>();
            let tail = variant
                .tail
                .as_ref()
                .map(|tail| core_type_imprecision_score(tail))
                .unwrap_or(0);
            payloads + tail
        }
        typed_ir::Type::Named { args, .. } => args
            .iter()
            .map(|arg| match arg {
                typed_ir::TypeArg::Type(ty) => core_type_imprecision_score(ty),
                typed_ir::TypeArg::Bounds(bounds) => {
                    bounds
                        .lower
                        .as_deref()
                        .map(core_type_imprecision_score)
                        .unwrap_or(0)
                        + bounds
                            .upper
                            .as_deref()
                            .map(core_type_imprecision_score)
                            .unwrap_or(0)
                }
            })
            .sum(),
        typed_ir::Type::Row { items, tail } => {
            items.iter().map(core_type_imprecision_score).sum::<usize>()
                + core_type_imprecision_score(tail)
        }
        typed_ir::Type::Recursive { body, .. } => core_type_imprecision_score(body),
        typed_ir::Type::Never => 0,
    }
}

fn rebuilt_specialization_evidence_score(
    callee_ty: &typed_ir::Type,
    evidences: &[Option<&typed_ir::ApplyEvidence>],
) -> Option<usize> {
    let mut current = callee_ty.clone();
    let mut score = 0usize;
    for evidence in evidences {
        let typed_ir::Type::Fun {
            ret_effect, ret, ..
        } = current
        else {
            return (score > 0).then_some(score);
        };
        if let Some(evidence) = evidence.as_ref().copied() {
            score += evidence_result_score(ret.as_ref(), ret_effect.as_ref(), &evidence.result);
        }
        current = ret.as_ref().clone();
    }
    (score > 0).then_some(score)
}

fn evidence_result_score(
    candidate_value: &typed_ir::Type,
    candidate_effect: &typed_ir::Type,
    result: &typed_ir::TypeBounds,
) -> usize {
    result
        .lower
        .iter()
        .chain(result.upper.iter())
        .map(|expected| rebuilt_core_result_score(candidate_value, candidate_effect, expected))
        .max()
        .unwrap_or(0)
}

fn rebuilt_core_result_score(
    candidate_value: &typed_ir::Type,
    candidate_effect: &typed_ir::Type,
    expected: &typed_ir::Type,
) -> usize {
    let mut score = 0usize;
    if candidate_value == expected {
        score += 16;
    } else if type_compatible(expected, candidate_value) {
        score += 4;
    }
    let candidate_paths = core_result_effect_paths(candidate_value, candidate_effect);
    let expected_paths = core_result_effect_paths(expected, &typed_ir::Type::Never);
    if !candidate_paths.is_empty() && !expected_paths.is_empty() {
        if expected_paths.iter().any(|expected| {
            !candidate_paths
                .iter()
                .any(|candidate| effect_paths_match(candidate, expected))
        }) {
            return 0;
        }
        let extra = candidate_paths
            .iter()
            .filter(|candidate| {
                !expected_paths
                    .iter()
                    .any(|expected| effect_paths_match(candidate, expected))
            })
            .count();
        score += 64usize.saturating_sub(extra * 4);
    }
    score
}

fn core_result_effect_paths(
    value: &typed_ir::Type,
    application_effect: &typed_ir::Type,
) -> Vec<typed_ir::Path> {
    let mut paths = effect_paths(application_effect);
    collect_core_type_effect_paths(value, &mut paths);
    paths
}

fn collect_core_type_effect_paths(ty: &typed_ir::Type, paths: &mut Vec<typed_ir::Path>) {
    match ty {
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_unique_effect_paths(param_effect, paths);
            collect_unique_effect_paths(ret_effect, paths);
            collect_core_type_effect_paths(param, paths);
            collect_core_type_effect_paths(ret, paths);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_core_type_effect_paths(item, paths);
            }
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    typed_ir::TypeArg::Type(ty) => collect_core_type_effect_paths(ty, paths),
                    typed_ir::TypeArg::Bounds(bounds) => {
                        if let Some(lower) = bounds.lower.as_deref() {
                            collect_core_type_effect_paths(lower, paths);
                        }
                        if let Some(upper) = bounds.upper.as_deref() {
                            collect_core_type_effect_paths(upper, paths);
                        }
                    }
                }
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_core_type_effect_paths(&field.value, paths);
            }
            if let Some(spread) = &record.spread {
                let spread = match spread {
                    typed_ir::RecordSpread::Head(spread) | typed_ir::RecordSpread::Tail(spread) => {
                        spread
                    }
                };
                collect_core_type_effect_paths(spread, paths);
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_core_type_effect_paths(payload, paths);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_core_type_effect_paths(tail, paths);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_core_type_effect_paths(item, paths);
            }
            collect_core_type_effect_paths(tail, paths);
        }
        typed_ir::Type::Recursive { body, .. } => collect_core_type_effect_paths(body, paths),
        typed_ir::Type::Var(_)
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Unknown => {}
    }
}

fn collect_unique_effect_paths(effect: &typed_ir::Type, paths: &mut Vec<typed_ir::Path>) {
    for path in effect_paths(effect) {
        if !paths
            .iter()
            .any(|existing| effect_paths_match(existing, &path))
        {
            paths.push(path);
        }
    }
}

fn runtime_rebuilt_type_score(actual: &RuntimeType, expected: &RuntimeType) -> Option<usize> {
    if actual == expected {
        return Some(8);
    }
    let (actual_value, actual_effect) = runtime_value_and_effect(actual);
    let (expected_value, expected_effect) = runtime_value_and_effect(expected);
    if !type_compatible(&expected_value, &actual_value)
        || !effect_compatible(&expected_effect, &actual_effect)
    {
        return None;
    }
    let value_score = usize::from(expected_value == actual_value) * 2;
    let effect_score = usize::from(expected_effect == actual_effect) * 4;
    Some(1 + value_score + effect_score)
}

fn rewrite_single_specialization_refs_expr_inner(
    expr: &mut Expr,
    rewrites: &HashMap<typed_ir::Path, typed_ir::Path>,
    specialized_paths: &HashSet<typed_ir::Path>,
    binding_types: &HashMap<typed_ir::Path, typed_ir::Type>,
    shadowed: &mut BTreeSet<typed_ir::Name>,
) {
    match &mut expr.kind {
        ExprKind::Var(path) => {
            if path
                .segments
                .as_slice()
                .first()
                .is_some_and(|name| path.segments.len() == 1 && shadowed.contains(name))
            {
                return;
            }
            if let Some(specialized) = rewrites.get(path)
                && single_specialization_var_ref_fits(&expr.ty, specialized, binding_types)
            {
                *path = specialized.clone();
            }
        }
        ExprKind::EffectOp(path) => {
            if let Some(specialized) = rewrites.get(path)
                && single_specialization_var_ref_fits(&expr.ty, specialized, binding_types)
            {
                expr.kind = ExprKind::Var(specialized.clone());
                return;
            }
        }
        ExprKind::Apply {
            callee,
            arg,
            instantiation,
            ..
        } => {
            if !single_specialization_direct_callee_should_wait(callee, rewrites, shadowed) {
                rewrite_single_specialization_refs_expr_inner(
                    callee,
                    rewrites,
                    specialized_paths,
                    binding_types,
                    shadowed,
                );
            }
            rewrite_single_specialization_refs_expr_inner(
                arg,
                rewrites,
                specialized_paths,
                binding_types,
                shadowed,
            );
            if instantiation
                .as_ref()
                .is_some_and(|instantiation| rewrites.contains_key(&instantiation.target))
            {
                *instantiation = None;
            }
        }
        ExprKind::Lambda { param, body, .. } => {
            let inserted = shadowed.insert(param.clone());
            rewrite_single_specialization_refs_expr_inner(
                body,
                rewrites,
                specialized_paths,
                binding_types,
                shadowed,
            );
            if inserted {
                shadowed.remove(param);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_single_specialization_refs_expr_inner(
                cond,
                rewrites,
                specialized_paths,
                binding_types,
                shadowed,
            );
            rewrite_single_specialization_refs_expr_inner(
                then_branch,
                rewrites,
                specialized_paths,
                binding_types,
                shadowed,
            );
            rewrite_single_specialization_refs_expr_inner(
                else_branch,
                rewrites,
                specialized_paths,
                binding_types,
                shadowed,
            );
        }
        ExprKind::Tuple(items) => {
            for item in items {
                rewrite_single_specialization_refs_expr_inner(
                    item,
                    rewrites,
                    specialized_paths,
                    binding_types,
                    shadowed,
                );
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                rewrite_single_specialization_refs_expr_inner(
                    &mut field.value,
                    rewrites,
                    specialized_paths,
                    binding_types,
                    shadowed,
                );
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        rewrite_single_specialization_refs_expr_inner(
                            expr,
                            rewrites,
                            specialized_paths,
                            binding_types,
                            shadowed,
                        );
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                rewrite_single_specialization_refs_expr_inner(
                    value,
                    rewrites,
                    specialized_paths,
                    binding_types,
                    shadowed,
                );
            }
        }
        ExprKind::Select { base, .. } => {
            rewrite_single_specialization_refs_expr_inner(
                base,
                rewrites,
                specialized_paths,
                binding_types,
                shadowed,
            );
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            rewrite_single_specialization_refs_expr_inner(
                scrutinee,
                rewrites,
                specialized_paths,
                binding_types,
                shadowed,
            );
            for arm in arms {
                let inserted = pattern_bind_name(&arm.pattern)
                    .map(|name| (name.clone(), shadowed.insert(name.clone())));
                if let Some(guard) = &mut arm.guard {
                    rewrite_single_specialization_refs_expr_inner(
                        guard,
                        rewrites,
                        specialized_paths,
                        binding_types,
                        shadowed,
                    );
                }
                rewrite_single_specialization_refs_expr_inner(
                    &mut arm.body,
                    rewrites,
                    specialized_paths,
                    binding_types,
                    shadowed,
                );
                if let Some((name, true)) = inserted {
                    shadowed.remove(&name);
                }
            }
        }
        ExprKind::Block { stmts, tail } => {
            let saved = shadowed.clone();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { pattern, value } => {
                        rewrite_single_specialization_refs_expr_inner(
                            value,
                            rewrites,
                            specialized_paths,
                            binding_types,
                            shadowed,
                        );
                        if let Some(name) = pattern_bind_name(pattern) {
                            shadowed.insert(name.clone());
                        }
                    }
                    Stmt::Module { def, body } => {
                        rewrite_single_specialization_refs_expr_inner(
                            body,
                            rewrites,
                            specialized_paths,
                            binding_types,
                            shadowed,
                        );
                        if let [name] = def.segments.as_slice() {
                            shadowed.insert(name.clone());
                        }
                    }
                    Stmt::Expr(body) => {
                        rewrite_single_specialization_refs_expr_inner(
                            body,
                            rewrites,
                            specialized_paths,
                            binding_types,
                            shadowed,
                        );
                    }
                }
            }
            if let Some(tail) = tail {
                rewrite_single_specialization_refs_expr_inner(
                    tail,
                    rewrites,
                    specialized_paths,
                    binding_types,
                    shadowed,
                );
            }
            *shadowed = saved;
        }
        ExprKind::Handle { body, arms, .. } => {
            rewrite_single_specialization_refs_expr_inner(
                body,
                rewrites,
                specialized_paths,
                binding_types,
                shadowed,
            );
            for arm in arms {
                let payload_inserted = pattern_bind_name(&arm.payload)
                    .map(|name| (name.clone(), shadowed.insert(name.clone())));
                let resume_inserted = arm
                    .resume
                    .as_ref()
                    .map(|resume| (resume.name.clone(), shadowed.insert(resume.name.clone())));
                if let Some(guard) = &mut arm.guard {
                    rewrite_single_specialization_refs_expr_inner(
                        guard,
                        rewrites,
                        specialized_paths,
                        binding_types,
                        shadowed,
                    );
                }
                rewrite_single_specialization_refs_expr_inner(
                    &mut arm.body,
                    rewrites,
                    specialized_paths,
                    binding_types,
                    shadowed,
                );
                if let Some((name, true)) = resume_inserted {
                    shadowed.remove(&name);
                }
                if let Some((name, true)) = payload_inserted {
                    shadowed.remove(&name);
                }
            }
        }
        ExprKind::AddId { thunk, .. } => {
            rewrite_single_specialization_refs_expr_inner(
                thunk,
                rewrites,
                specialized_paths,
                binding_types,
                shadowed,
            );
        }
        ExprKind::LocalPushId { body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::BindHere { expr: body } => {
            rewrite_single_specialization_refs_expr_inner(
                body,
                rewrites,
                specialized_paths,
                binding_types,
                shadowed,
            );
        }
        ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
    if rewrite_single_specialization_apply_callee(expr, rewrites, binding_types, shadowed) {
        return;
    }
    let Some(spine) = principal_unify_apply_spine(expr) else {
        return;
    };
    if !specialized_paths.contains(spine.target) {
        return;
    }
    let Some(ty) = binding_types.get(spine.target) else {
        return;
    };
    let args = spine
        .args
        .iter()
        .map(|arg| (*arg).clone())
        .collect::<Vec<_>>();
    if let Some(rewritten) =
        rebuild_apply_call_owned(spine.target.clone(), ty.clone(), args, &expr.ty)
    {
        *expr = rewritten;
    }
}

fn single_specialization_direct_callee_should_wait(
    callee: &Expr,
    rewrites: &HashMap<typed_ir::Path, typed_ir::Path>,
    shadowed: &BTreeSet<typed_ir::Name>,
) -> bool {
    let ExprKind::Var(path) = &callee.kind else {
        return false;
    };
    if path
        .segments
        .as_slice()
        .first()
        .is_some_and(|name| path.segments.len() == 1 && shadowed.contains(name))
    {
        return false;
    }
    rewrites.contains_key(path)
}

fn rewrite_single_specialization_apply_callee(
    expr: &mut Expr,
    rewrites: &HashMap<typed_ir::Path, typed_ir::Path>,
    binding_types: &HashMap<typed_ir::Path, typed_ir::Type>,
    shadowed: &BTreeSet<typed_ir::Name>,
) -> bool {
    let Some(spine) = principal_unify_apply_spine(expr) else {
        return false;
    };
    if spine
        .target
        .segments
        .as_slice()
        .first()
        .is_some_and(|name| spine.target.segments.len() == 1 && shadowed.contains(name))
    {
        return false;
    }
    let Some(specialized) = rewrites.get(spine.target) else {
        return false;
    };
    let Some(ty) = binding_types.get(specialized) else {
        return false;
    };
    let args = spine
        .args
        .iter()
        .map(|arg| (*arg).clone())
        .collect::<Vec<_>>();
    let Some((params, _ret, _ret_effect)) = core_fun_spine_parts_exact(ty, args.len()) else {
        return false;
    };
    if !owned_args_fit_contextual_specialization(&args, &params) {
        return false;
    }
    if rebuilt_specialization_call_score(ty, &args, &expr.ty, &spine.evidences).is_none() {
        return false;
    }
    let Some(rewritten) = rebuild_apply_call_owned(specialized.clone(), ty.clone(), args, &expr.ty)
    else {
        return false;
    };
    *expr = rewritten;
    true
}

fn single_specialization_var_ref_fits(
    expr_ty: &RuntimeType,
    specialized: &typed_ir::Path,
    binding_types: &HashMap<typed_ir::Path, typed_ir::Type>,
) -> bool {
    let Some(ty) = binding_types.get(specialized) else {
        return false;
    };
    let expected = normalize_hir_function_type(RuntimeType::core(ty.clone()));
    runtime_rebuilt_type_score(expr_ty, &expected).is_some()
}

fn pattern_value_context(pattern: &Pattern) -> Option<typed_ir::TypeBounds> {
    let ty = runtime_core_type(pattern_runtime_type(pattern));
    closed_slot_type_usable(&ty, false).then(|| typed_ir::TypeBounds::exact(ty))
}

fn tuple_item_result_contexts(
    result_context: Option<&typed_ir::TypeBounds>,
    len: usize,
) -> Vec<Option<typed_ir::TypeBounds>> {
    let Some(typed_ir::Type::Tuple(items)) = closed_type_from_bounds(result_context) else {
        return vec![None; len];
    };
    if items.len() != len {
        return vec![None; len];
    }
    items
        .into_iter()
        .map(|item| {
            closed_slot_type_usable(&item, false).then(|| typed_ir::TypeBounds::exact(item))
        })
        .collect()
}

fn role_rewrite_candidate_params(
    callee_ty: &typed_ir::Type,
    arity: usize,
) -> Option<Vec<(typed_ir::Type, typed_ir::Type)>> {
    let (params, _ret, _ret_effect) = core_fun_spine_parts_exact(callee_ty, arity)?;
    Some(params)
}

fn role_rewrite_candidate_fits(
    params: &[(typed_ir::Type, typed_ir::Type)],
    args: &[&Expr],
    final_ty: &RuntimeType,
    callee_ty: &typed_ir::Type,
) -> bool {
    if !args
        .iter()
        .zip(params)
        .all(|(arg, (param, effect))| principal_arg_adapter(arg, param, effect).is_some())
    {
        return false;
    }
    if runtime_type_has_vars(final_ty) {
        return true;
    }
    let Some((_params, ret, ret_effect)) = core_fun_spine_parts_exact(callee_ty, args.len()) else {
        return false;
    };
    let (actual_ret, actual_ret_effect) = runtime_value_and_effect(final_ty);
    type_compatible(&actual_ret, &ret) && type_compatible(&actual_ret_effect, &ret_effect)
}

pub(super) fn pattern_bind_name(pattern: &Pattern) -> Option<&typed_ir::Name> {
    match pattern {
        Pattern::Bind { name, .. } => Some(name),
        Pattern::As { name, .. } => Some(name),
        _ => None,
    }
}

fn pattern_runtime_type(pattern: &Pattern) -> &RuntimeType {
    match pattern {
        Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Bind { ty, .. }
        | Pattern::Wildcard { ty }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => ty,
    }
}

fn pattern_local_runtime_type(pattern_ty: &RuntimeType, expected: &RuntimeType) -> RuntimeType {
    if !runtime_type_shape_usable(pattern_ty) && runtime_type_shape_usable(expected) {
        expected.clone()
    } else {
        pattern_ty.clone()
    }
}

fn refresh_resume_binding_return_from_context(
    mut resume: ResumeBinding,
    context: Option<&typed_ir::TypeBounds>,
) -> ResumeBinding {
    let Some(expected) = closed_type_from_bounds(context) else {
        return resume;
    };
    let Some(ty) = runtime_function_type_with_choice_return(resume.ty.clone(), &expected) else {
        return resume;
    };
    resume.ty = ty;
    resume
}

fn runtime_function_type_with_choice_return(
    ty: RuntimeType,
    expected: &typed_ir::Type,
) -> Option<RuntimeType> {
    let RuntimeType::Fun { param, ret } = ty else {
        return None;
    };
    let ret_value = runtime_core_type(&ret);
    if !type_choice_contains(expected, &ret_value) {
        return None;
    }
    Some(RuntimeType::fun(
        *param,
        runtime_param_with_updated_value_shape(*ret, expected.clone()),
    ))
}

fn contextual_join_result_type(
    result: typed_ir::Type,
    context: Option<&typed_ir::TypeBounds>,
) -> typed_ir::Type {
    let Some(context) = closed_type_from_bounds(context) else {
        return result;
    };
    if core_type_contains_unknown(&result) || type_choice_contains(&context, &result) {
        context
    } else {
        result
    }
}

fn contextual_join_result_type_with_arm_result(
    result: typed_ir::Type,
    context: Option<&typed_ir::TypeBounds>,
    arm_result: Option<&typed_ir::Type>,
) -> typed_ir::Type {
    let contextual = contextual_join_result_type(result, context);
    let Some(arm_result) = arm_result else {
        return contextual;
    };
    if core_type_is_imprecise_runtime_slot(&contextual)
        || !core_types_compatible(&contextual, arm_result)
            && !core_types_compatible(arm_result, &contextual)
    {
        arm_result.clone()
    } else {
        contextual
    }
}

fn visible_match_arm_result_type(arms: &[MatchArm]) -> Option<typed_ir::Type> {
    arms.iter()
        .map(|arm| runtime_core_type(&arm.body.ty))
        .filter(visible_join_arm_result_usable)
        .reduce(|left, right| choose_core_type(left, right, TypeChoice::VisiblePrincipal))
}

fn visible_handle_arm_result_type(arms: &[HandleArm]) -> Option<typed_ir::Type> {
    arms.iter()
        .map(|arm| runtime_core_type(&arm.body.ty))
        .filter(visible_join_arm_result_usable)
        .reduce(|left, right| choose_core_type(left, right, TypeChoice::VisiblePrincipal))
}

fn visible_join_arm_result_usable(ty: &typed_ir::Type) -> bool {
    !core_type_is_never(ty)
        && !core_type_is_imprecise_runtime_slot(ty)
        && !contains_non_runtime_type(ty)
}

fn tuple_pattern_item_runtime_type(
    expected: &RuntimeType,
    pattern_ty: &RuntimeType,
    index: usize,
) -> Option<RuntimeType> {
    runtime_tuple_items(expected)
        .or_else(|| runtime_tuple_items(pattern_ty))
        .and_then(|items| items.get(index).cloned())
        .map(RuntimeType::core)
}

fn runtime_tuple_items(ty: &RuntimeType) -> Option<&[typed_ir::Type]> {
    match ty {
        RuntimeType::Core(typed_ir::Type::Tuple(items)) => Some(items),
        RuntimeType::Unknown
        | RuntimeType::Core(_)
        | RuntimeType::Fun { .. }
        | RuntimeType::Thunk { .. } => None,
    }
}

fn list_pattern_item_runtime_type(
    expected: &RuntimeType,
    pattern_ty: &RuntimeType,
) -> Option<RuntimeType> {
    runtime_named_single_type_arg(expected)
        .or_else(|| runtime_named_single_type_arg(pattern_ty))
        .map(RuntimeType::core)
}

fn record_pattern_field_runtime_type(
    expected: &RuntimeType,
    pattern_ty: &RuntimeType,
    name: &typed_ir::Name,
) -> Option<RuntimeType> {
    runtime_record_field_type(expected, name)
        .or_else(|| runtime_record_field_type(pattern_ty, name))
        .map(RuntimeType::core)
}

fn runtime_record_field_type(ty: &RuntimeType, name: &typed_ir::Name) -> Option<typed_ir::Type> {
    match ty {
        RuntimeType::Core(typed_ir::Type::Record(record)) => record
            .fields
            .iter()
            .find(|field| field.name == *name)
            .map(|field| field.value.clone()),
        RuntimeType::Unknown
        | RuntimeType::Core(_)
        | RuntimeType::Fun { .. }
        | RuntimeType::Thunk { .. } => None,
    }
}

fn variant_pattern_payload_runtime_type(
    expected: &RuntimeType,
    pattern_ty: &RuntimeType,
    tag: &typed_ir::Name,
) -> Option<RuntimeType> {
    runtime_variant_case_payload_type(expected, tag)
        .or_else(|| runtime_variant_case_payload_type(pattern_ty, tag))
        .or_else(|| runtime_named_variant_payload_type(expected, tag))
        .or_else(|| runtime_named_variant_payload_type(pattern_ty, tag))
        .map(RuntimeType::core)
}

fn runtime_variant_case_payload_type(
    ty: &RuntimeType,
    tag: &typed_ir::Name,
) -> Option<typed_ir::Type> {
    match ty {
        RuntimeType::Core(typed_ir::Type::Variant(variant)) => variant
            .cases
            .iter()
            .find(|case| case.name == *tag)
            .and_then(|case| variant_case_payload_type(&case.payloads)),
        RuntimeType::Unknown
        | RuntimeType::Core(_)
        | RuntimeType::Fun { .. }
        | RuntimeType::Thunk { .. } => None,
    }
}

fn runtime_named_variant_payload_type(
    ty: &RuntimeType,
    tag: &typed_ir::Name,
) -> Option<typed_ir::Type> {
    match ty {
        RuntimeType::Core(typed_ir::Type::Named { path, args }) => {
            named_variant_payload_from_type_args(path, tag, args)
        }
        RuntimeType::Unknown
        | RuntimeType::Core(_)
        | RuntimeType::Fun { .. }
        | RuntimeType::Thunk { .. } => None,
    }
}

fn variant_case_payload_type(payloads: &[typed_ir::Type]) -> Option<typed_ir::Type> {
    match payloads {
        [] => None,
        [payload] => Some(payload.clone()),
        payloads => Some(typed_ir::Type::Tuple(payloads.to_vec())),
    }
}

fn named_variant_payload_from_type_args(
    path: &typed_ir::Path,
    tag: &typed_ir::Name,
    args: &[typed_ir::TypeArg],
) -> Option<typed_ir::Type> {
    if args.len() == 2 {
        match tag.0.as_str() {
            "ok" => return type_arg_core(&args[0]),
            "err" => return type_arg_core(&args[1]),
            _ => {}
        }
    }
    if args.len() == 1 {
        match tag.0.as_str() {
            "just" | "leaf" => return runtime_single_type_arg(args),
            "node" if path_last_segment_is(path, "list_view") => {
                let item = type_arg_core(&args[0])?;
                let list = typed_ir::Type::Named {
                    path: sibling_type_path(path, "list"),
                    args: vec![typed_ir::TypeArg::Type(item)],
                };
                return Some(typed_ir::Type::Tuple(vec![list.clone(), list]));
            }
            _ => {}
        }
    }
    None
}

fn path_last_segment_is(path: &typed_ir::Path, name: &str) -> bool {
    path.segments.last().is_some_and(|last| last.0 == name)
}

fn sibling_type_path(path: &typed_ir::Path, name: &str) -> typed_ir::Path {
    let mut path = path.clone();
    if let Some(last) = path.segments.last_mut() {
        *last = typed_ir::Name(name.to_string());
    }
    path
}

fn runtime_named_single_type_arg(ty: &RuntimeType) -> Option<typed_ir::Type> {
    match ty {
        RuntimeType::Core(typed_ir::Type::Named { args, .. }) => runtime_single_type_arg(args),
        RuntimeType::Unknown
        | RuntimeType::Core(_)
        | RuntimeType::Fun { .. }
        | RuntimeType::Thunk { .. } => None,
    }
}

fn runtime_single_type_arg(args: &[typed_ir::TypeArg]) -> Option<typed_ir::Type> {
    let [arg] = args else {
        return None;
    };
    type_arg_core(arg)
}

fn type_arg_core(arg: &typed_ir::TypeArg) -> Option<typed_ir::Type> {
    match arg {
        typed_ir::TypeArg::Type(ty) => Some(ty.clone()),
        typed_ir::TypeArg::Bounds(bounds) => match (&bounds.lower, &bounds.upper) {
            (Some(lower), Some(upper)) if lower == upper => Some((**lower).clone()),
            (Some(lower), None) => Some((**lower).clone()),
            (None, Some(upper)) => Some((**upper).clone()),
            _ => None,
        },
    }
}

fn refresh_apply_expr_type_from_callee(expr: Expr) -> Expr {
    let Expr { ty, kind } = expr;
    let ExprKind::Apply {
        callee,
        arg,
        evidence,
        instantiation,
    } = kind
    else {
        return Expr { ty, kind };
    };
    let refreshed_ty = principal_apply_type_from_evidence_arg(evidence.as_ref(), &arg)
        .or_else(|| principal_rewrite_apply_type(&callee.ty))
        .unwrap_or(ty);
    Expr::typed(
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        },
        refreshed_ty,
    )
}

fn principal_apply_type_from_evidence_arg(
    evidence: Option<&typed_ir::ApplyEvidence>,
    arg: &Expr,
) -> Option<RuntimeType> {
    let evidence = evidence?;
    let principal = evidence.principal_callee.as_ref()?;
    let (params, _ret, _ret_effect) = core_fun_spine_parts_exact(principal, 1)?;
    let (param, _param_effect) = params.first()?;
    let actual = runtime_core_type(&arg.ty);
    if !specialization_shape_usable(&actual) {
        return None;
    }
    let mut required_vars = BTreeSet::new();
    collect_core_type_vars(principal, &mut required_vars);
    if required_vars.is_empty() {
        return None;
    }
    let mut substitutions = evidence
        .substitutions
        .iter()
        .map(|substitution| (substitution.var.clone(), substitution.ty.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut conflicts = BTreeSet::new();
    project_closed_substitutions_from_type(
        &param,
        &actual,
        &required_vars,
        &mut substitutions,
        &mut conflicts,
        false,
        64,
    );
    if !conflicts.is_empty() {
        return None;
    }
    let callee = substitute_type(principal, &substitutions);
    let projected = principal_rewrite_apply_type(&RuntimeType::core(callee))?;
    (!runtime_type_has_vars(&projected)
        && !runtime_type_contains_unknown(&projected)
        && !runtime_type_contains_any(&projected))
    .then_some(projected)
}

fn fill_plan_runtime_slots_from_principal(
    plan: &mut typed_ir::PrincipalElaborationPlan,
    arg_count: usize,
) {
    let substitutions = plan_substitution_map(plan);
    let callee = substitute_type(&plan.principal_callee, &substitutions);
    let Some((params, ret)) = core_fun_spine_exact(&callee, arg_count) else {
        return;
    };
    for arg in &mut plan.args {
        if arg.expected_runtime.is_none()
            && let Some(param) = params.get(arg.index)
            && (closed_slot_type_usable(param, false) || function_runtime_slot_usable(param))
        {
            arg.expected_runtime = Some(param.clone());
        }
    }
    if plan.result.expected_runtime.is_none()
        && (closed_slot_type_usable(&ret, false) || function_runtime_slot_usable(&ret))
    {
        plan.result.expected_runtime = Some(ret);
    }
}

fn fill_effectful_input_runtime_slot_from_result(
    plan: &mut typed_ir::PrincipalElaborationPlan,
    arg_count: usize,
) {
    if arg_count != 1 || plan.args.len() != 1 || plan.args[0].expected_runtime.is_some() {
        return;
    }
    let Some(result) = principal_plan_result_closed_type(&plan.result) else {
        return;
    };
    if !closed_slot_type_usable(&result, false) {
        return;
    }
    let substitutions = plan_substitution_map(plan);
    let callee = substitute_type(&plan.principal_callee, &substitutions);
    let Some((params, ret, _ret_effect)) = core_fun_spine_parts_exact(&callee, arg_count) else {
        return;
    };
    let Some((param, param_effect)) = params.first() else {
        return;
    };
    if !matches!(param, typed_ir::Type::Unknown | typed_ir::Type::Any)
        || effect_is_empty(param_effect)
    {
        return;
    }
    if ret != result && !type_compatible(&result, &ret) {
        return;
    }
    plan.args[0].expected_runtime = Some(result);
}

fn merge_plan_substitutions(
    plan: &mut typed_ir::PrincipalElaborationPlan,
    substitutions: BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    for (var, ty) in substitutions {
        if plan
            .substitutions
            .iter()
            .any(|substitution| substitution.var == var)
        {
            continue;
        }
        plan.substitutions
            .push(typed_ir::TypeSubstitution { var, ty });
    }
}

fn substitute_principal_plan_context_slots(
    mut plan: typed_ir::PrincipalElaborationPlan,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::PrincipalElaborationPlan {
    for substitution in &mut plan.substitutions {
        substitution.ty = substitute_type(&substitution.ty, substitutions);
    }
    for arg in &mut plan.args {
        arg.intrinsic = substitute_bounds(arg.intrinsic.clone(), substitutions);
        arg.contextual = arg
            .contextual
            .take()
            .map(|bounds| substitute_bounds(bounds, substitutions));
        arg.expected_runtime = arg
            .expected_runtime
            .take()
            .map(|ty| substitute_type(&ty, substitutions));
    }
    plan.result.intrinsic = substitute_bounds(plan.result.intrinsic, substitutions);
    plan.result.contextual = plan
        .result
        .contextual
        .take()
        .map(|bounds| substitute_bounds(bounds, substitutions));
    plan.result.expected_runtime = plan
        .result
        .expected_runtime
        .take()
        .map(|ty| substitute_type(&ty, substitutions));
    for adapter in &mut plan.adapters {
        adapter.actual = substitute_type(&adapter.actual, substitutions);
        adapter.expected = substitute_type(&adapter.expected, substitutions);
    }
    plan
}

fn preserve_projected_substitutions_if_normalized_empty(
    plan: &mut typed_ir::PrincipalElaborationPlan,
    substitutions: BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    if !plan.complete || !plan.substitutions.is_empty() {
        return;
    }
    plan.substitutions = substitutions
        .into_iter()
        .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
        .collect();
}

fn principal_callee_scheme_suffix(
    scheme: &typed_ir::Type,
    principal_callee: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    let scheme_arity = core_fun_arity(scheme);
    let principal_arity = core_fun_arity(principal_callee);
    if principal_arity == 0 || principal_arity >= scheme_arity {
        return None;
    }
    drop_core_fun_params(scheme, scheme_arity - principal_arity)
}

fn drop_core_fun_params(ty: &typed_ir::Type, count: usize) -> Option<typed_ir::Type> {
    if count == 0 {
        return Some(ty.clone());
    }
    let typed_ir::Type::Fun { ret, .. } = ty else {
        return None;
    };
    drop_core_fun_params(ret, count - 1)
}

fn binding_required_vars(binding: &Binding) -> BTreeSet<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    vars.extend(binding.type_params.iter().cloned());
    collect_binding_type_params(binding, &mut vars);
    vars
}

fn binding_signature_vars(binding: &Binding) -> BTreeSet<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(&binding.scheme.body, &mut vars);
    for requirement in &binding.scheme.requirements {
        collect_role_requirement_vars(requirement, &mut vars);
    }
    vars
}

fn principal_unify_skip_reason_benign(reason: &str) -> bool {
    matches!(
        reason,
        "skip-non-generic-callee"
            | "skip-local-leaf-specialization"
            | "skip-recursive-leaf-specialization"
            | "skip-partial-role-call"
    )
}

fn missing_required_vars(
    binding: &Binding,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Vec<typed_ir::TypeVar> {
    let effect_only_vars = binding_effect_only_vars(binding);
    let mut vars = binding_required_vars(binding)
        .into_iter()
        .filter(|var| {
            !effect_only_vars.contains(var)
                && substitutions
                    .get(var)
                    .is_none_or(|ty| !substitution_is_complete_for_var(var, ty, &effect_only_vars))
        })
        .collect::<Vec<_>>();
    vars.sort_by(|left, right| left.0.cmp(&right.0));
    vars
}

fn required_vars_are_closed(
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> bool {
    required_vars.iter().all(|var| {
        substitutions
            .get(var)
            .is_some_and(|ty| !core_type_has_vars(ty) && !core_type_contains_unknown(ty))
    })
}

fn variant_constructor_payload_type_vars(expr: &Expr) -> Option<BTreeSet<typed_ir::TypeVar>> {
    match &expr.kind {
        ExprKind::Lambda { body, .. } => variant_constructor_payload_type_vars(body),
        ExprKind::Block {
            stmts,
            tail: Some(tail),
        } if stmts.is_empty() => variant_constructor_payload_type_vars(tail),
        ExprKind::Coerce { expr, .. } | ExprKind::Pack { expr, .. } => {
            variant_constructor_payload_type_vars(expr)
        }
        ExprKind::Variant { value, .. } => {
            let mut vars = BTreeSet::new();
            if let Some(value) = value {
                collect_hir_type_vars(&value.ty, &mut vars);
            }
            Some(vars)
        }
        _ => None,
    }
}

fn missing_binding_type_params(
    binding: &Binding,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Vec<typed_ir::TypeVar> {
    let effect_only_vars = binding_effect_only_vars(binding);
    let mut vars = binding
        .type_params
        .iter()
        .filter(|var| {
            !effect_only_vars.contains(*var)
                && substitutions
                    .get(*var)
                    .is_none_or(|ty| !substitution_is_complete_for_var(var, ty, &effect_only_vars))
        })
        .cloned()
        .collect::<Vec<_>>();
    vars.sort_by(|left, right| left.0.cmp(&right.0));
    vars
}

fn complete_required_substitutions(
    binding: &Binding,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
    let effect_only_vars = binding_effect_only_vars(binding);
    binding_required_vars(binding)
        .into_iter()
        .map(|var| {
            let Some(ty) = substitutions.get(&var) else {
                return effect_only_vars
                    .contains(&var)
                    .then_some((var, typed_ir::Type::Never));
            };
            substitution_is_complete_for_var(&var, ty, &effect_only_vars).then(|| (var, ty.clone()))
        })
        .collect()
}

fn complete_binding_type_param_substitutions(
    binding: &Binding,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
    let effect_only_vars = binding_effect_only_vars(binding);
    binding
        .type_params
        .iter()
        .cloned()
        .map(|var| {
            let Some(ty) = substitutions.get(&var) else {
                return effect_only_vars
                    .contains(&var)
                    .then_some((var, typed_ir::Type::Never));
            };
            substitution_is_complete_for_var(&var, ty, &effect_only_vars).then(|| (var, ty.clone()))
        })
        .collect()
}

fn complete_binding_signature_substitutions(
    binding: &Binding,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
    let effect_only_vars = binding_effect_only_vars(binding);
    let signature_vars = binding_signature_vars(binding);
    signature_vars
        .into_iter()
        .map(|var| {
            let Some(ty) = substitutions.get(&var) else {
                return effect_only_vars
                    .contains(&var)
                    .then_some((var, typed_ir::Type::Never));
            };
            substitution_is_complete_for_var(&var, ty, &effect_only_vars).then(|| (var, ty.clone()))
        })
        .collect()
}

fn complete_required_role_substitutions(
    binding: &Binding,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
    let effect_only_vars = binding_effect_only_vars(binding);
    binding_required_vars(binding)
        .into_iter()
        .map(|var| {
            let ty = substitutions.get(&var)?;
            substitution_is_complete_for_var(&var, ty, &effect_only_vars).then(|| (var, ty.clone()))
        })
        .collect()
}

fn substitution_is_complete_for_var(
    var: &typed_ir::TypeVar,
    ty: &typed_ir::Type,
    effect_only_vars: &BTreeSet<typed_ir::TypeVar>,
) -> bool {
    if effect_only_vars.contains(var) {
        return !matches!(
            ty,
            typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_)
        ) && !core_type_has_vars(ty);
    }
    if function_runtime_slot_usable(ty) {
        return true;
    }
    if matches!(
        ty,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_)
    ) || core_type_has_vars(ty)
    {
        return false;
    }
    !core_type_contains_unknown(ty)
}

fn function_runtime_slot_usable(ty: &typed_ir::Type) -> bool {
    let mut current = ty;
    let mut has_function_spine = false;
    while let typed_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = current
    {
        has_function_spine = true;
        if core_type_has_vars(param)
            || core_type_has_vars(param_effect)
            || core_type_has_vars(ret_effect)
        {
            return false;
        }
        current = ret;
    }
    has_function_spine && !core_type_has_vars(current)
}

fn binding_substitutions_are_only_top(
    binding: &Binding,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> bool {
    let required = binding_required_vars(binding);
    !required.is_empty()
        && required.iter().all(|var| {
            substitutions
                .get(var)
                .is_some_and(|ty| matches!(ty, typed_ir::Type::Unknown | typed_ir::Type::Any))
        })
}

fn principal_runtime_substitution_is_unit_default(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Tuple(items) if items.is_empty())
}

fn owned_args_fit_without_adapter(
    args: &[Expr],
    params: &[(typed_ir::Type, typed_ir::Type)],
) -> bool {
    args.iter()
        .zip(params)
        .all(|(arg, (param, effect))| principal_arg_adapter(arg, param, effect).is_some())
}

fn borrowed_args_accept_specialization_inputs(
    args: &[&Expr],
    params: &[(typed_ir::Type, typed_ir::Type)],
) -> bool {
    args.iter().zip(params).all(|(arg, (param, effect))| {
        let actual = runtime_core_type(&arg.ty);
        if runtime_type_contains_unknown(&arg.ty)
            || core_type_contains_unknown(&actual)
            || core_type_contains_unknown(param)
            || core_type_contains_unknown(effect)
            || core_type_has_vars(&actual)
            || core_type_has_vars(param)
            || core_type_has_vars(effect)
        {
            return true;
        }
        principal_arg_adapter(arg, param, effect).is_some()
    })
}

fn owned_args_fit_contextual_specialization(
    args: &[Expr],
    params: &[(typed_ir::Type, typed_ir::Type)],
) -> bool {
    args.iter().zip(params).all(|(arg, (param, effect))| {
        let actual = runtime_core_type(&arg.ty);
        if runtime_type_contains_unknown(&arg.ty)
            || core_type_contains_unknown(&actual)
            || core_type_contains_unknown(param)
            || core_type_contains_unknown(effect)
            || core_type_has_vars(&actual)
            || core_type_has_vars(param)
            || core_type_has_vars(effect)
        {
            return true;
        }
        principal_arg_adapter(arg, param, effect).is_some()
    })
}

fn handler_plan_is_supported(boundary: &HandlerCallBoundary, plan: &HandlerAdapterPlan) -> bool {
    (boundary.consumes_input_effect
        && plan
            .residual_after
            .as_ref()
            .is_none_or(|effect| effect_is_empty(effect) || plan.return_wrapper_effect.is_some()))
        || (boundary.consumes_input_effect
            && boundary.output_effect.as_ref().is_none_or(effect_is_empty)
            && plan.return_wrapper_effect.is_none())
        || (!boundary.consumes_input_effect
            && boundary.output_effect.as_ref().is_none_or(effect_is_empty)
            && plan.return_wrapper_effect.is_none())
        || (!boundary.consumes_input_effect
            && boundary.preserves_output_effect
            && plan.return_wrapper_effect.is_none())
        || (boundary.output_effect.as_ref().is_none_or(effect_is_empty)
            && plan.return_wrapper_effect.is_none()
            && plan.residual_before == plan.residual_after)
}

fn plan_only_lacks_handler_boundary(plan: &typed_ir::PrincipalElaborationPlan) -> bool {
    !plan.incomplete_reasons.is_empty()
        && plan.incomplete_reasons.iter().all(|reason| {
            matches!(
                reason,
                typed_ir::PrincipalElaborationIncompleteReason::HandlerBoundaryWithoutPlan
            )
        })
}

fn plan_only_lacks_open_slot_precision(plan: &typed_ir::PrincipalElaborationPlan) -> bool {
    !plan.incomplete_reasons.is_empty()
        && plan.incomplete_reasons.iter().all(|reason| {
            matches!(
                reason,
                typed_ir::PrincipalElaborationIncompleteReason::OpenArgType(_)
                    | typed_ir::PrincipalElaborationIncompleteReason::OpenResultType
            )
        })
}

fn plan_only_lacks_effect_only_missing_substitutions(
    plan: &typed_ir::PrincipalElaborationPlan,
    binding: &Binding,
) -> bool {
    let effect_only_vars = binding_effect_only_vars(binding);
    !plan.incomplete_reasons.is_empty()
        && plan.incomplete_reasons.iter().all(|reason| {
            matches!(
                reason,
                typed_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(var)
                    if effect_only_vars.contains(var)
            )
        })
}

fn plan_only_lacks_internal_missing_substitutions(
    plan: &typed_ir::PrincipalElaborationPlan,
    binding: &Binding,
) -> bool {
    let binding_params = binding.type_params.iter().collect::<BTreeSet<_>>();
    !plan.incomplete_reasons.is_empty()
        && plan.incomplete_reasons.iter().all(|reason| {
            matches!(
                reason,
                typed_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(var)
                    | typed_ir::PrincipalElaborationIncompleteReason::OpenCandidate(var)
                    if !binding_params.contains(var)
            )
        })
}

fn rebuild_apply_call(
    path: typed_ir::Path,
    callee_ty: typed_ir::Type,
    args: &[&Expr],
    final_ty: &RuntimeType,
) -> Option<Expr> {
    rebuild_apply_call_with_final_arg_effect(path, callee_ty, args, final_ty, None)
}

fn rebuild_apply_call_with_final_arg_effect(
    path: typed_ir::Path,
    callee_ty: typed_ir::Type,
    args: &[&Expr],
    final_ty: &RuntimeType,
    final_arg_effect: Option<&typed_ir::Type>,
) -> Option<Expr> {
    let mut call = Expr::typed(
        ExprKind::Var(path.clone()),
        normalize_hir_function_type(RuntimeType::core(callee_ty.clone())),
    );
    let mut current = callee_ty;
    for (index, arg) in args.iter().enumerate() {
        if index > 0 {
            call = force_rebuilt_thunked_function_callee(call);
        }
        let (param, param_effect, next, ret_effect) = core_fun_parts_with_effects_exact(&current)?;
        let param_effect = final_arg_effect
            .filter(|_| index + 1 == args.len() && matches!(arg.ty, RuntimeType::Thunk { .. }))
            .unwrap_or(&param_effect);
        let arg = principal_arg_adapter(arg, &param, param_effect)?;
        call = refine_apply_callee_input_from_arg(call, &arg);
        let specialized_ret = runtime_type_from_core_value_and_effect(next.clone(), ret_effect);
        let ty = if index + 1 == args.len() {
            closed_rebuilt_apply_type(final_ty, &specialized_ret)
        } else {
            specialized_ret
        };
        call = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(call),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            ty,
        );
        current = next;
    }
    Some(adapt_rebuilt_result_to_context(call, final_ty))
}

fn rebuild_apply_call_owned(
    path: typed_ir::Path,
    callee_ty: typed_ir::Type,
    args: Vec<Expr>,
    final_ty: &RuntimeType,
) -> Option<Expr> {
    rebuild_apply_call_owned_with_final_arg_effect(path, callee_ty, args, final_ty, None)
}

fn rebuild_apply_call_owned_with_final_arg_effect(
    path: typed_ir::Path,
    callee_ty: typed_ir::Type,
    args: Vec<Expr>,
    final_ty: &RuntimeType,
    final_arg_effect: Option<&typed_ir::Type>,
) -> Option<Expr> {
    let mut call = Expr::typed(
        ExprKind::Var(path),
        normalize_hir_function_type(RuntimeType::core(callee_ty.clone())),
    );
    let mut current = callee_ty;
    let arity = args.len();
    for (index, arg) in args.into_iter().enumerate() {
        if index > 0 {
            call = force_rebuilt_thunked_function_callee(call);
        }
        let (param, param_effect, next, ret_effect) = core_fun_parts_with_effects_exact(&current)?;
        let param_effect = final_arg_effect
            .filter(|_| index + 1 == arity && matches!(arg.ty, RuntimeType::Thunk { .. }))
            .unwrap_or(&param_effect);
        let arg = principal_arg_adapter(&arg, &param, &param_effect)?;
        call = refine_apply_callee_input_from_arg(call, &arg);
        let specialized_ret = runtime_type_from_core_value_and_effect(next.clone(), ret_effect);
        let ty = if index + 1 == arity {
            closed_rebuilt_apply_type(final_ty, &specialized_ret)
        } else {
            specialized_ret
        };
        call = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(call),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            ty,
        );
        current = next;
    }
    Some(adapt_rebuilt_result_to_context(call, final_ty))
}

fn force_rebuilt_thunked_function_callee(call: Expr) -> Expr {
    let value = match &call.ty {
        RuntimeType::Thunk { value, .. } if matches!(value.as_ref(), RuntimeType::Fun { .. }) => {
            value.as_ref().clone()
        }
        _ => return call,
    };
    Expr::typed(
        ExprKind::BindHere {
            expr: Box::new(call),
        },
        value,
    )
}

fn wrap_non_generic_binding_return_effect(
    mut binding: Binding,
    arity: usize,
    effect: typed_ir::Type,
) -> Option<Binding> {
    binding.scheme.body =
        core_fun_spine_with_final_ret_effect(&binding.scheme.body, arity, &effect)?;
    binding.body = wrap_runtime_fun_spine_return_effect(binding.body, arity, &effect)?;
    Some(binding)
}

fn final_ty_effect_context(ty: &RuntimeType) -> Option<typed_ir::Type> {
    let RuntimeType::Thunk { effect, value } = ty else {
        return None;
    };
    (!effect_is_empty(effect) && !matches!(value.as_ref(), RuntimeType::Fun { .. }))
        .then(|| effect.clone())
}

fn runtime_type_value_is_function(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Fun { .. } => true,
        RuntimeType::Thunk { value, .. } => runtime_type_value_is_function(value),
        RuntimeType::Core(typed_ir::Type::Fun { .. }) => true,
        RuntimeType::Core(_) => false,
    }
}

fn combined_forced_argument_effect(args: &[Expr]) -> Option<typed_ir::Type> {
    args.iter()
        .filter_map(forced_argument_effect)
        .reduce(merge_effects)
}

fn combined_forced_argument_effect_refs(args: &[&Expr]) -> Option<typed_ir::Type> {
    args.iter()
        .filter_map(|arg| forced_argument_effect(arg))
        .reduce(merge_effects)
}

fn forced_argument_effect(arg: &Expr) -> Option<typed_ir::Type> {
    let ExprKind::BindHere { expr } = &arg.kind else {
        return None;
    };
    let RuntimeType::Thunk { effect, .. } = &expr.ty else {
        return None;
    };
    (!effect_is_empty(effect)).then(|| effect.clone())
}

fn core_fun_spine_with_final_ret_effect(
    ty: &typed_ir::Type,
    arity: usize,
    effect: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if arity == 0 {
        return Some(ty.clone());
    }
    let typed_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = ty
    else {
        return None;
    };
    let ret = if arity == 1 {
        ret.as_ref().clone()
    } else {
        core_fun_spine_with_final_ret_effect(ret, arity - 1, effect)?
    };
    Some(typed_ir::Type::Fun {
        param: param.clone(),
        param_effect: param_effect.clone(),
        ret_effect: Box::new(if arity == 1 {
            effect.clone()
        } else {
            ret_effect.as_ref().clone()
        }),
        ret: Box::new(ret),
    })
}

fn core_fun_spine_with_input_shapes(
    ty: &typed_ir::Type,
    input_shapes: &[typed_ir::Type],
) -> Option<typed_ir::Type> {
    if input_shapes.is_empty() {
        return Some(ty.clone());
    }
    let typed_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
        ..
    } = ty
    else {
        return None;
    };
    let ret = if input_shapes.len() == 1 {
        ret.as_ref().clone()
    } else {
        core_fun_spine_with_input_shapes(ret, &input_shapes[1..])?
    };
    let param = input_shape_context_param(param, &input_shapes[0]);
    Some(typed_ir::Type::Fun {
        param: Box::new(param),
        param_effect: param_effect.clone(),
        ret_effect: ret_effect.clone(),
        ret: Box::new(ret),
    })
}

fn core_fun_spine_with_output_shape(
    ty: &typed_ir::Type,
    arity: usize,
    output_shape: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if arity == 0 {
        return Some(output_shape.clone());
    }
    let typed_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
        ..
    } = ty
    else {
        return None;
    };
    let ret = if arity == 1 {
        output_shape.clone()
    } else {
        core_fun_spine_with_output_shape(ret, arity - 1, output_shape)?
    };
    Some(typed_ir::Type::Fun {
        param: param.clone(),
        param_effect: param_effect.clone(),
        ret_effect: ret_effect.clone(),
        ret: Box::new(ret),
    })
}

fn contextual_specialization_scheme(
    ty: &typed_ir::Type,
    input_shapes: Option<&[typed_ir::Type]>,
    output_shape: Option<&typed_ir::Type>,
) -> Option<typed_ir::Type> {
    let with_inputs = input_shapes
        .and_then(|input_shapes| core_fun_spine_with_input_shapes(ty, input_shapes))
        .unwrap_or_else(|| ty.clone());
    output_shape
        .and_then(|output_shape| {
            core_fun_spine_with_output_shape(
                &with_inputs,
                input_shapes.map_or(0, <[typed_ir::Type]>::len),
                output_shape,
            )
        })
        .or_else(|| input_shapes.map(|_| with_inputs))
}

fn specialization_binding_body_context(
    scheme: &typed_ir::Type,
    input_shapes: Option<&[typed_ir::Type]>,
    output_shape: Option<&typed_ir::Type>,
) -> typed_ir::TypeBounds {
    let contextual = contextual_specialization_scheme(scheme, input_shapes, output_shape)
        .unwrap_or_else(|| scheme.clone());
    typed_ir::TypeBounds::exact(contextual)
}

fn call_specialization_callee_type(
    original: &Binding,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    handler_plan: Option<&HandlerAdapterPlan>,
    input_shapes: &[typed_ir::Type],
    output_shape: Option<&typed_ir::Type>,
    arity: usize,
) -> typed_ir::Type {
    let call_callee_ty = handler_plan
        .map(|plan| {
            let substituted = substitute_binding(original.clone(), substitutions);
            apply_handler_adapter_plan_to_binding(substituted, plan)
                .scheme
                .body
        })
        .unwrap_or_else(|| substitute_type(&original.scheme.body, substitutions));

    let contextual_input_shapes =
        if handler_plan.is_some_and(|plan| plan.return_wrapper_effect.is_some()) {
            None
        } else {
            Some(input_shapes)
        };
    if contextual_input_shapes.is_none() {
        return output_shape
            .and_then(|output_shape| {
                core_fun_spine_with_output_shape(&call_callee_ty, arity, output_shape)
            })
            .unwrap_or(call_callee_ty);
    }
    contextual_specialization_scheme(&call_callee_ty, contextual_input_shapes, output_shape)
        .unwrap_or(call_callee_ty)
}

fn preferred_specialization_output_shape(
    scheme: &typed_ir::Type,
    arity: usize,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    output: Option<typed_ir::Type>,
    _is_handler_binding: bool,
) -> Option<typed_ir::Type> {
    let output =
        prefer_constructed_union_specialization_output(scheme, arity, substitutions, output);
    let inferred = inferred_specialized_return_shape(scheme, arity, substitutions);
    match (output, inferred) {
        (Some(output), Some(inferred)) if type_choice_contains(&output, &inferred) => {
            Some(inferred)
        }
        (Some(output), _) => Some(output),
        (None, inferred) => inferred,
    }
}

fn handler_action_output_shape(args: &[Expr]) -> Option<typed_ir::Type> {
    let action = args.last()?;
    if let Some(shape) = handler_action_tail_output_shape(action) {
        return Some(shape);
    }
    let (value, effect) = runtime_value_and_effect(&action.ty);
    (!effect_is_empty(&effect) && closed_slot_type_usable(&value, false)).then_some(value)
}

fn handler_consumed_payload_output_shape(boundary: &HandlerCallBoundary) -> Option<typed_ir::Type> {
    if !boundary.consumes_input_effect || boundary.preserves_output_effect {
        return None;
    }
    let input_effect = boundary.input_effect.as_ref()?;
    let payloads = boundary
        .consumes
        .iter()
        .filter_map(|consumed| effect_payload_type_for_operation(input_effect, consumed))
        .filter(|payload| {
            closed_slot_type_usable(payload, false) && !core_type_is_imprecise_runtime_slot(payload)
        })
        .collect::<Vec<_>>();
    let [payload] = payloads.as_slice() else {
        return None;
    };
    Some(payload.clone())
}

fn prefer_handler_consumed_payload_output_shape(
    output_shape: Option<typed_ir::Type>,
    consumed_payload: Option<&typed_ir::Type>,
) -> HandlerOutputShapeChoice {
    match (output_shape, consumed_payload) {
        (None, Some(payload)) => HandlerOutputShapeChoice {
            output_shape: Some(payload.clone()),
            from_consumed_payload: true,
        },
        (output, None) => HandlerOutputShapeChoice {
            output_shape: output,
            from_consumed_payload: false,
        },
        (Some(output), Some(payload))
            if output == *payload
                || type_compatible(&output, payload) && type_compatible(payload, &output) =>
        {
            HandlerOutputShapeChoice {
                output_shape: Some(output),
                from_consumed_payload: true,
            }
        }
        (Some(output), Some(_)) => HandlerOutputShapeChoice {
            output_shape: Some(output),
            from_consumed_payload: false,
        },
    }
}

struct HandlerOutputShapeChoice {
    output_shape: Option<typed_ir::Type>,
    from_consumed_payload: bool,
}

fn narrow_handler_output_substitution(
    scheme: &typed_ir::Type,
    arity: usize,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    output: &typed_ir::Type,
) {
    let Some((_params, ret, _ret_effect)) = core_fun_spine_parts_exact(scheme, arity) else {
        return;
    };
    let Some(var) = terminal_return_var(&ret) else {
        return;
    };
    if substitutions.get(&var).is_some_and(|existing| {
        type_choice_contains(existing, output)
            || type_compatible(existing, output)
            || type_compatible(output, existing)
    }) {
        substitutions.insert(var, output.clone());
    }
}

fn narrow_handler_choice_substitutions_to_output(
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    output: &typed_ir::Type,
) {
    for ty in substitutions.values_mut() {
        if type_choice_contains(ty, output) {
            *ty = output.clone();
        }
    }
}

fn align_handler_action_input_shape_with_output(
    scheme: &typed_ir::Type,
    input_shapes: &mut [typed_ir::Type],
    output: &typed_ir::Type,
) {
    let Some((params, ret, _ret_effect)) = core_fun_spine_parts_exact(scheme, input_shapes.len())
    else {
        return;
    };
    let Some(return_var) = terminal_return_var(&ret) else {
        return;
    };
    let Some((last_param, _)) = params.last() else {
        return;
    };
    let mut param_vars = BTreeSet::new();
    collect_core_type_vars(last_param, &mut param_vars);
    if param_vars.contains(&return_var)
        && let Some(last_shape) = input_shapes.last_mut()
    {
        *last_shape = output.clone();
    }
}

fn terminal_return_var(ty: &typed_ir::Type) -> Option<typed_ir::TypeVar> {
    let mut current = ty;
    while let typed_ir::Type::Fun { ret, .. } = current {
        current = ret;
    }
    match current {
        typed_ir::Type::Var(var) => Some(var.clone()),
        _ => None,
    }
}

fn handler_action_tail_output_shape(expr: &Expr) -> Option<typed_ir::Type> {
    match &expr.kind {
        ExprKind::Thunk { value, expr, .. } => {
            let value = runtime_core_type(value);
            if closed_slot_type_usable(&value, false) {
                Some(value)
            } else {
                handler_action_tail_output_shape(expr)
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. }
        | ExprKind::LocalPushId { body: expr, .. }
        | ExprKind::AddId { thunk: expr, .. } => handler_action_tail_output_shape(expr),
        ExprKind::Block {
            tail: Some(tail), ..
        } => handler_action_tail_output_shape(tail),
        ExprKind::Apply {
            callee, evidence, ..
        } => apply_callee_return_shape(callee)
            .or_else(|| {
                evidence
                    .as_ref()
                    .and_then(apply_evidence_principal_return_shape)
            })
            .or_else(|| closed_runtime_value_type(&expr.ty)),
        _ => closed_runtime_value_type(&expr.ty),
    }
}

fn apply_callee_return_shape(callee: &Expr) -> Option<typed_ir::Type> {
    let ret = runtime_function_return_type(&callee.ty)?;
    let (value, _effect) = runtime_value_and_effect(&ret);
    closed_slot_type_usable(&value, false).then_some(value)
}

fn runtime_function_return_type(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { ret, .. } => Some(ret.as_ref().clone()),
        RuntimeType::Thunk { value, .. } => runtime_function_return_type(value),
        RuntimeType::Core(core @ typed_ir::Type::Fun { .. }) => {
            let projected = project_runtime_hir_type_with_vars(core, &BTreeSet::new());
            runtime_function_return_type(&projected)
        }
        _ => None,
    }
}

fn apply_evidence_principal_return_shape(
    evidence: &typed_ir::ApplyEvidence,
) -> Option<typed_ir::Type> {
    let principal = evidence.principal_callee.as_ref()?;
    let substitutions = evidence
        .substitutions
        .iter()
        .map(|substitution| (substitution.var.clone(), substitution.ty.clone()))
        .collect::<BTreeMap<_, _>>();
    let principal = substitute_type(principal, &substitutions);
    let arity = core_fun_arity(&principal);
    let (_params, ret, _ret_effect) = core_fun_spine_parts_exact(&principal, arity)?;
    let ret = normalize_projected_value_shape(ret);
    closed_slot_type_usable(&ret, false).then_some(ret)
}

fn prefer_constructed_union_specialization_output(
    scheme: &typed_ir::Type,
    arity: usize,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    output: Option<typed_ir::Type>,
) -> Option<typed_ir::Type> {
    let expected = output.as_ref()?;
    let substituted = substitute_type(scheme, substitutions);
    let (_params, ret, _ret_effect) = core_fun_spine_parts_exact(&substituted, arity)?;
    let typed_ir::Type::Union(items) = ret else {
        return output;
    };
    items
        .iter()
        .find_map(|item| constructed_union_item_for_payload(item, expected))
        .or(output)
}

fn type_choice_contains(choice: &typed_ir::Type, item: &typed_ir::Type) -> bool {
    match choice {
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            items.iter().any(|candidate| candidate == item)
        }
        _ => false,
    }
}

fn inferred_specialized_return_shape(
    scheme: &typed_ir::Type,
    arity: usize,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<typed_ir::Type> {
    let substituted = substitute_type(scheme, substitutions);
    let (_params, ret, _ret_effect) = core_fun_spine_parts_exact(&substituted, arity)?;
    let ret = normalize_projected_value_shape(ret);
    closed_slot_type_usable(&ret, false).then_some(ret)
}

fn constructed_union_item_for_payload(
    item: &typed_ir::Type,
    expected: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    let typed_ir::Type::Named { args, .. } = item else {
        return None;
    };
    let has_expected_payload = args.iter().any(|arg| match arg {
        typed_ir::TypeArg::Type(ty) => {
            ty == expected || type_compatible(ty, expected) || type_compatible(expected, ty)
        }
        typed_ir::TypeArg::Bounds(bounds) => bounds
            .lower
            .iter()
            .chain(bounds.upper.iter())
            .map(|ty| ty.as_ref())
            .any(|ty| {
                ty == expected || type_compatible(ty, expected) || type_compatible(expected, ty)
            }),
    });
    has_expected_payload.then(|| item.clone())
}

fn contextual_output_shape_matches(ret: &typed_ir::Type, output_shape: &typed_ir::Type) -> bool {
    ret == output_shape || type_compatible(output_shape, ret) || type_compatible(ret, output_shape)
}

fn retag_runtime_expr_spine_type(expr: Expr, ty: RuntimeType) -> Expr {
    match expr {
        Expr {
            kind: ExprKind::Block { stmts, tail },
            ..
        } => {
            let tail = tail.map(|tail| Box::new(retag_runtime_expr_spine_type(*tail, ty)));
            let ty = tail
                .as_ref()
                .map(|tail| tail.ty.clone())
                .unwrap_or(RuntimeType::Core(typed_ir::Type::Never));
            Expr::typed(ExprKind::Block { stmts, tail }, ty)
        }
        Expr {
            kind:
                ExprKind::Lambda {
                    param,
                    param_effect_annotation,
                    param_function_allowed_effects,
                    body,
                },
            ..
        } => {
            let RuntimeType::Fun {
                param: param_ty,
                ret,
            } = ty
            else {
                return Expr::typed(
                    ExprKind::Lambda {
                        param,
                        param_effect_annotation,
                        param_function_allowed_effects,
                        body,
                    },
                    ty,
                );
            };
            let body = retag_runtime_expr_spine_type(*body, *ret);
            let ty = RuntimeType::fun(*param_ty, body.ty.clone());
            Expr::typed(
                ExprKind::Lambda {
                    param,
                    param_effect_annotation,
                    param_function_allowed_effects,
                    body: Box::new(body),
                },
                ty,
            )
        }
        Expr { kind, .. } => Expr::typed(kind, ty),
    }
}

fn input_shape_context_param(
    param: &typed_ir::Type,
    input_shape: &typed_ir::Type,
) -> typed_ir::Type {
    match (param, input_shape) {
        (param, typed_ir::Type::Union(items)) if items.iter().any(|item| item == param) => {
            input_shape.clone()
        }
        _ if closed_slot_type_usable(param, false) && type_compatible(param, input_shape) => {
            param.clone()
        }
        (typed_ir::Type::Variant(param_variant), typed_ir::Type::Variant(input_variant))
            if variant_input_shape_drops_cases(param_variant, input_variant) =>
        {
            param.clone()
        }
        _ => input_shape.clone(),
    }
}

fn variant_input_shape_drops_cases(
    param: &typed_ir::VariantType,
    input: &typed_ir::VariantType,
) -> bool {
    input.cases.len() < param.cases.len()
        && input
            .cases
            .iter()
            .all(|input_case| param.cases.iter().any(|case| case.name == input_case.name))
}

fn wrap_runtime_fun_spine_return_effect(
    expr: Expr,
    arity: usize,
    effect: &typed_ir::Type,
) -> Option<Expr> {
    if arity == 0 {
        return Some(wrap_expr_in_effect_thunk(expr, effect));
    }
    if let Expr {
        ty: _,
        kind: ExprKind::Block {
            stmts,
            tail: Some(tail),
        },
    } = expr
    {
        let tail = wrap_runtime_fun_spine_return_effect(*tail, arity, effect)?;
        let ty = tail.ty.clone();
        return Some(Expr::typed(
            ExprKind::Block {
                stmts,
                tail: Some(Box::new(tail)),
            },
            ty,
        ));
    }
    let Expr {
        ty,
        kind:
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            },
    } = expr
    else {
        return None;
    };
    let RuntimeType::Fun {
        param: param_ty, ..
    } = ty
    else {
        return None;
    };
    let body = wrap_runtime_fun_spine_return_effect(*body, arity - 1, effect)?;
    let ty = RuntimeType::fun(*param_ty, body.ty.clone());
    Some(Expr::typed(
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(body),
        },
        ty,
    ))
}

fn wrap_expr_in_effect_thunk(expr: Expr, effect: &typed_ir::Type) -> Expr {
    if let RuntimeType::Thunk {
        effect: existing, ..
    } = &expr.ty
        && existing == effect
    {
        return expr;
    }
    let value = expr.ty.clone();
    Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value: value.clone(),
            expr: Box::new(expr),
        },
        RuntimeType::thunk(effect.clone(), value),
    )
}

fn closed_rebuilt_apply_type(final_ty: &RuntimeType, specialized_ret: &RuntimeType) -> RuntimeType {
    if runtime_type_value_is_never(final_ty) && !runtime_type_value_is_never(specialized_ret) {
        return specialized_ret.clone();
    }
    if rebuilt_apply_type_prefers_specialized(final_ty, specialized_ret) {
        return specialized_ret.clone();
    }
    if (runtime_type_has_vars(final_ty)
        || runtime_type_contains_any(final_ty)
        || runtime_type_contains_unknown(final_ty)
        || should_keep_specialized_runtime_type(final_ty, specialized_ret))
        && !runtime_type_has_vars(specialized_ret)
        && !runtime_type_contains_unknown(specialized_ret)
    {
        specialized_ret.clone()
    } else {
        final_ty.clone()
    }
}

fn rebuilt_apply_type_prefers_specialized(
    final_ty: &RuntimeType,
    specialized_ret: &RuntimeType,
) -> bool {
    if final_ty == specialized_ret {
        return false;
    }
    let (final_value, final_effect) = runtime_value_and_effect(final_ty);
    let (specialized_value, specialized_effect) = runtime_value_and_effect(specialized_ret);
    if !effect_compatible(&specialized_effect, &final_effect)
        || !closed_slot_type_usable(&specialized_value, false)
        || !closed_slot_type_usable(&final_value, false)
    {
        return false;
    }
    needs_runtime_coercion(&specialized_value, &final_value)
}

fn runtime_type_value_is_never(ty: &RuntimeType) -> bool {
    matches!(runtime_core_type(ty), typed_ir::Type::Never)
}

fn refresh_rewritten_args(args: Vec<Expr>) -> Vec<Expr> {
    args.into_iter()
        .map(|arg| project_runtime_expr_types(refresh_local_expr_types(arg)))
        .collect()
}

fn contextual_final_call_type(
    existing: RuntimeType,
    callee_ty: &typed_ir::Type,
    arity: usize,
    allow_incompatible_handler_refresh: bool,
) -> RuntimeType {
    let Some((_params, ret, ret_effect)) = core_fun_spine_parts_exact(callee_ty, arity) else {
        return existing;
    };
    let specialized = runtime_type_from_core_value_and_effect(ret, ret_effect);
    if allow_incompatible_handler_refresh
        && !runtime_call_result_types_compatible(&existing, &specialized)
    {
        specialized
    } else {
        closed_rebuilt_apply_type(&existing, &specialized)
    }
}

fn rewritten_binding_handler_adapter_plan(binding: &Binding) -> Option<HandlerAdapterPlan> {
    let info = handler_binding_info(binding)?;
    if info.consumes.is_empty() {
        return None;
    }
    let arity = core_fun_arity(&binding.scheme.body);
    let (params, ret, _ret_effect) = core_fun_spine_parts_exact(&binding.scheme.body, arity)?;
    let input_effect = info
        .principal_input_effect
        .as_ref()
        .filter(|effect| effect_contains_any(effect, &info.consumes))
        .cloned()
        .or_else(|| {
            info.principal_output_effect
                .as_ref()
                .filter(|effect| effect_contains_any(effect, &info.consumes))
                .cloned()
        });
    let consumes_input_effect = input_effect
        .as_ref()
        .is_some_and(|effect| effect_contains_any(effect, &info.consumes));
    if !consumes_input_effect {
        return None;
    }
    let boundary = HandlerCallBoundary {
        consumes: info.consumes.clone(),
        input_effect,
        output_effect: None,
        consumes_input_effect,
        preserves_output_effect: false,
        pure: info.pure,
    };
    let plan = handler_adapter_plan(&info, &boundary);
    let plan = refine_handler_adapter_plan_from_signature(plan, &params, &ret, &info.consumes);
    handler_plan_is_supported(&boundary, &plan).then_some(plan)
}

fn force_outer_handler_lambda_param(expr: Expr, plan: &HandlerAdapterPlan) -> Expr {
    let Some(effect) = plan
        .residual_before
        .clone()
        .filter(|effect| !effect_is_empty(effect))
    else {
        return expr;
    };
    let Expr {
        ty: RuntimeType::Fun {
            param: current_param,
            ret,
        },
        kind:
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            },
    } = expr
    else {
        return expr;
    };
    let param_ty = match *current_param {
        RuntimeType::Thunk { value, .. } => RuntimeType::thunk(effect, *value),
        other => RuntimeType::thunk(effect, other),
    };
    Expr::typed(
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        },
        RuntimeType::fun(param_ty, *ret),
    )
}

fn effect_contains_any(effect: &typed_ir::Type, targets: &[typed_ir::Path]) -> bool {
    effect_paths(effect).iter().any(|path| {
        targets
            .iter()
            .any(|target| effect_paths_match(path, target))
    })
}

fn runtime_call_result_types_compatible(left: &RuntimeType, right: &RuntimeType) -> bool {
    let left = runtime_core_type(left);
    let right = runtime_core_type(right);
    left == right || type_compatible(&left, &right) || type_compatible(&right, &left)
}

fn should_keep_specialized_runtime_type(final_ty: &RuntimeType, specialized: &RuntimeType) -> bool {
    match (final_ty, specialized) {
        (RuntimeType::Core(expected), RuntimeType::Thunk { effect, value })
            if !effect_is_empty(effect) =>
        {
            let actual = runtime_core_type(value);
            actual == *expected || type_compatible(expected, &actual)
        }
        _ => false,
    }
}

fn runtime_type_from_core_value_and_effect(
    value: typed_ir::Type,
    effect: typed_ir::Type,
) -> RuntimeType {
    let value = normalize_hir_function_type(RuntimeType::core(value));
    if effect_is_empty(&effect) {
        value
    } else {
        RuntimeType::thunk(effect, value)
    }
}

fn runtime_type_with_context_value_and_actual_effect(
    actual: &RuntimeType,
    value: typed_ir::Type,
) -> RuntimeType {
    let (_actual_value, actual_effect) = runtime_value_and_effect(actual);
    runtime_type_from_core_value_and_effect(value, actual_effect)
}

fn principal_arg_adapter(
    arg: &Expr,
    param: &typed_ir::Type,
    param_effect: &typed_ir::Type,
) -> Option<Expr> {
    let actual = runtime_core_type(&arg.ty);
    if core_type_contains_unknown(param) || core_type_contains_unknown(&actual) {
        return Some(arg.clone());
    }
    if actual != *param
        && !type_compatible(param, &actual)
        && !variant_row_accepts_actual(param, &actual)
    {
        return None;
    }
    if matches!(
        param,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_)
    ) && matches!(arg.ty, RuntimeType::Thunk { .. })
        && erased_param_should_preserve_thunk_arg(arg)
    {
        return Some(arg.clone());
    }
    let param_requires_thunk = principal_param_effect_requires_thunk(param_effect);
    let adapted = match (&arg.ty, param_requires_thunk) {
        (RuntimeType::Thunk { effect, value }, false) if !effect_is_empty(effect) => Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(arg.clone()),
            },
            value.as_ref().clone(),
        ),
        (
            RuntimeType::Thunk {
                effect: actual_effect,
                value: _,
            },
            true,
        ) => {
            if actual_effect == param_effect {
                return Some(adapt_principal_value_arg_coercion(
                    arg.clone(),
                    param,
                    param_requires_thunk,
                ));
            }
            let value = normalize_hir_function_type(RuntimeType::core(param.clone()));
            if let Some(thunk) = nested_thunk_with_effect(arg, param_effect, &value) {
                return Some(thunk);
            }
            if let Some(thunk) = retag_nested_imprecise_thunk_effect(arg, param_effect, &value) {
                return Some(thunk);
            }
            let body = force_expr_to_runtime_value(arg.clone(), &value)?;
            Expr::typed(
                ExprKind::Thunk {
                    effect: param_effect.clone(),
                    value: value.clone(),
                    expr: Box::new(body),
                },
                RuntimeType::thunk(param_effect.clone(), value),
            )
        }
        (_, true) => {
            let value = arg.ty.clone();
            if let Some(thunk) = retag_nested_imprecise_thunk_effect(arg, param_effect, &value) {
                return Some(thunk);
            }
            Expr::typed(
                ExprKind::Thunk {
                    effect: param_effect.clone(),
                    value: value.clone(),
                    expr: Box::new(arg.clone()),
                },
                RuntimeType::thunk(param_effect.clone(), value),
            )
        }
        (_, false) => arg.clone(),
    };
    Some(adapt_principal_value_arg_coercion(
        adapted,
        param,
        param_requires_thunk,
    ))
}

fn adapt_principal_value_arg_coercion(
    arg: Expr,
    param: &typed_ir::Type,
    param_requires_thunk: bool,
) -> Expr {
    if param_requires_thunk {
        return arg;
    }
    let actual = runtime_core_type(&arg.ty);
    if needs_runtime_coercion(param, &actual) {
        return Expr::typed(
            ExprKind::Coerce {
                from: actual,
                to: param.clone(),
                expr: Box::new(arg),
            },
            RuntimeType::core(param.clone()),
        );
    }
    arg
}

fn variant_row_accepts_actual(param: &typed_ir::Type, actual: &typed_ir::Type) -> bool {
    let typed_ir::Type::Variant(_) = actual else {
        return false;
    };
    match param {
        typed_ir::Type::Variant(_) => {
            type_compatible(param, actual) || type_compatible(actual, param)
        }
        typed_ir::Type::Inter(items) => items.iter().any(|item| {
            matches!(item, typed_ir::Type::Variant(_))
                && (type_compatible(item, actual) || type_compatible(actual, item))
        }),
        _ => false,
    }
}

fn specialization_input_shapes_from_call(
    original_args: &[&Expr],
    rewritten_args: &[Expr],
    evidences: &[Option<&typed_ir::ApplyEvidence>],
    params: &[(typed_ir::Type, typed_ir::Type)],
) -> Vec<typed_ir::Type> {
    rewritten_args
        .iter()
        .zip(original_args)
        .zip(params)
        .enumerate()
        .map(|(index, ((rewritten, original), (param, param_effect)))| {
            let rewritten_shape = specialization_input_shape(rewritten, param, param_effect);
            let original_shape = specialization_input_shape(original, param, param_effect);
            let call_shape =
                prefer_contextual_specialization_shape(rewritten_shape, original_shape);
            evidences
                .get(index)
                .copied()
                .flatten()
                .and_then(apply_evidence_input_shape)
                .map(|evidence_shape| {
                    prefer_contextual_specialization_shape(call_shape.clone(), evidence_shape)
                })
                .unwrap_or(call_shape)
        })
        .collect()
}

fn preserve_handler_choice_input_shapes(
    input_shapes: &mut [typed_ir::Type],
    params: &[(typed_ir::Type, typed_ir::Type)],
) {
    for (shape, (param, _effect)) in input_shapes.iter_mut().zip(params) {
        if type_choice_contains(param, shape) {
            *shape = param.clone();
        }
    }
}

fn specialization_input_shapes_from_borrowed_call(
    args: &[&Expr],
    evidences: &[Option<&typed_ir::ApplyEvidence>],
    params: &[(typed_ir::Type, typed_ir::Type)],
) -> Vec<typed_ir::Type> {
    args.iter()
        .zip(params)
        .enumerate()
        .map(|(index, (arg, (param, param_effect)))| {
            let call_shape = specialization_input_shape(arg, param, param_effect);
            evidences
                .get(index)
                .copied()
                .flatten()
                .and_then(apply_evidence_input_shape)
                .map(|evidence_shape| {
                    prefer_contextual_specialization_shape(call_shape.clone(), evidence_shape)
                })
                .unwrap_or(call_shape)
        })
        .collect()
}

fn apply_evidence_input_shape(evidence: &typed_ir::ApplyEvidence) -> Option<typed_ir::Type> {
    evidence
        .expected_arg
        .as_ref()
        .and_then(contextual_specialization_shape_from_bounds)
        .or_else(|| contextual_specialization_shape_from_bounds(&evidence.arg))
}

fn contextual_specialization_shape_from_bounds(
    bounds: &typed_ir::TypeBounds,
) -> Option<typed_ir::Type> {
    closed_type_from_bounds(Some(bounds))
        .filter(specialization_shape_usable)
        .or_else(|| {
            bounds
                .lower
                .as_deref()
                .filter(|ty| specialization_shape_usable(ty))
                .cloned()
        })
        .or_else(|| {
            bounds
                .upper
                .as_deref()
                .filter(|ty| specialization_shape_usable(ty))
                .cloned()
        })
}

fn specialization_input_shape(
    arg: &Expr,
    param: &typed_ir::Type,
    _param_effect: &typed_ir::Type,
) -> typed_ir::Type {
    let (actual, actual_effect) = runtime_value_and_effect(&arg.ty);
    if effectful_erased_arg_should_wait_for_role_completion(&actual, &actual_effect)
        && closed_slot_type_usable(param, false)
    {
        return param.clone();
    }
    actual
}

fn prefer_contextual_specialization_shape(
    rewritten: typed_ir::Type,
    original: typed_ir::Type,
) -> typed_ir::Type {
    if specialization_shape_is_more_precise(&original, &rewritten) {
        original
    } else {
        rewritten
    }
}

fn specialization_shape_is_more_precise(
    candidate: &typed_ir::Type,
    current: &typed_ir::Type,
) -> bool {
    specialization_shape_usable(candidate)
        && (core_type_contains_any(current) || core_type_contains_unknown(current))
}

fn specialization_shape_usable(ty: &typed_ir::Type) -> bool {
    !matches!(ty, typed_ir::Type::Never)
        && !core_type_has_vars(ty)
        && !core_type_contains_any(ty)
        && !core_type_contains_unknown(ty)
}

fn retag_nested_imprecise_thunk_effect(
    expr: &Expr,
    expected_effect: &typed_ir::Type,
    expected_value: &RuntimeType,
) -> Option<Expr> {
    if let Some(retagged) = retag_imprecise_thunk_effect(expr, expected_effect, expected_value) {
        return Some(retagged);
    }
    match &expr.kind {
        ExprKind::Thunk { expr, .. } | ExprKind::BindHere { expr } => {
            retag_nested_imprecise_thunk_effect(expr, expected_effect, expected_value)
        }
        _ => None,
    }
}

fn retag_imprecise_thunk_effect(
    expr: &Expr,
    expected_effect: &typed_ir::Type,
    expected_value: &RuntimeType,
) -> Option<Expr> {
    let RuntimeType::Thunk { effect, value } = &expr.ty else {
        return None;
    };
    if !core_type_is_imprecise_runtime_slot(effect)
        || effect_paths(expected_effect).is_empty()
        || runtime_core_type(value) != runtime_core_type(expected_value)
    {
        return None;
    }
    let ExprKind::Thunk { expr: body, .. } = &expr.kind else {
        return None;
    };
    Some(Expr::typed(
        ExprKind::Thunk {
            effect: expected_effect.clone(),
            value: expected_value.clone(),
            expr: body.clone(),
        },
        RuntimeType::thunk(expected_effect.clone(), expected_value.clone()),
    ))
}

fn nested_thunk_with_effect(
    expr: &Expr,
    expected_effect: &typed_ir::Type,
    expected_value: &RuntimeType,
) -> Option<Expr> {
    if let RuntimeType::Thunk { effect, value } = &expr.ty
        && effect == expected_effect
        && runtime_core_type(value) == runtime_core_type(expected_value)
    {
        return Some(expr.clone());
    }
    match &expr.kind {
        ExprKind::Thunk { expr, .. } | ExprKind::BindHere { expr } => {
            nested_thunk_with_effect(expr, expected_effect, expected_value)
        }
        _ => None,
    }
}

fn force_expr_to_runtime_value(mut expr: Expr, expected: &RuntimeType) -> Option<Expr> {
    for _ in 0..8 {
        if &expr.ty == expected {
            return Some(expr);
        }
        let RuntimeType::Thunk { value, .. } = &expr.ty else {
            return None;
        };
        let value = value.as_ref().clone();
        if runtime_core_type(&value) != runtime_core_type(expected) {
            return None;
        }
        expr = Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(expr),
            },
            value,
        );
    }
    None
}

fn refine_bind_here_inner_thunk_value_from_context(
    expr: Expr,
    result_context: Option<typed_ir::TypeBounds>,
) -> Expr {
    let Some(expected) = closed_type_from_bounds(result_context.as_ref()) else {
        return expr;
    };
    if !closed_slot_type_usable(&expected, false) {
        return expr;
    }
    let RuntimeType::Thunk { effect, value } = &expr.ty else {
        return expr;
    };
    let actual = runtime_core_type(value);
    if !runtime_type_contains_unknown(value) {
        return expr;
    }
    if !core_type_contains_unknown(&actual)
        && actual != expected
        && !type_compatible(&expected, &actual)
    {
        return expr;
    }
    let value = RuntimeType::core(expected);
    let effect = effect.clone();
    let ty = RuntimeType::thunk(effect.clone(), value.clone());
    let kind = match expr.kind {
        ExprKind::Thunk { expr, .. } => ExprKind::Thunk {
            effect,
            value,
            expr,
        },
        kind => kind,
    };
    Expr { ty, kind }
}

fn principal_param_effect_requires_thunk(effect: &typed_ir::Type) -> bool {
    !effect_is_empty(effect) && !effect_paths(effect).is_empty()
}

fn erased_param_should_preserve_thunk_arg(arg: &Expr) -> bool {
    match &arg.kind {
        ExprKind::Var(path) => path.segments.len() == 1,
        ExprKind::Apply { callee, .. } => local_apply_head(callee),
        _ => false,
    }
}

fn local_apply_head(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Var(path) => path.segments.len() == 1,
        ExprKind::Apply { callee, .. } => local_apply_head(callee),
        ExprKind::BindHere { expr } => local_apply_head(expr),
        _ => false,
    }
}

fn adapt_rebuilt_result_to_context(call: Expr, final_ty: &RuntimeType) -> Expr {
    match (&call.ty, final_ty) {
        (RuntimeType::Thunk { effect, value }, RuntimeType::Core(expected))
            if !effect_is_empty(effect) =>
        {
            let actual = runtime_core_type(value);
            if actual == *expected || type_compatible(expected, &actual) {
                return Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(call),
                    },
                    final_ty.clone(),
                );
            }
            call
        }
        _ => call,
    }
}

fn runtime_type_has_vars(ty: &RuntimeType) -> bool {
    let mut vars = BTreeSet::new();
    collect_hir_type_vars(ty, &mut vars);
    !vars.is_empty()
}

fn runtime_type_shape_usable(ty: &RuntimeType) -> bool {
    !runtime_type_has_vars(ty) && !runtime_type_contains_any(ty)
}

fn runtime_type_contains_any(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_contains_any(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_contains_any(param) || runtime_type_contains_any(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_contains_any(effect) || runtime_type_contains_any(value)
        }
    }
}

fn core_type_contains_any(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Any => true,
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { args, .. } => args.iter().any(core_type_arg_contains_any),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_contains_any(param)
                || core_type_contains_any(param_effect)
                || core_type_contains_any(ret_effect)
                || core_type_contains_any(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(core_type_contains_any),
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(core_type_contains_any) || core_type_contains_any(tail)
        }
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_contains_any(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_contains_any(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(core_type_contains_any))
                || variant
                    .tail
                    .as_ref()
                    .is_some_and(|tail| core_type_contains_any(tail))
        }
        typed_ir::Type::Recursive { body, .. } => core_type_contains_any(body),
    }
}

fn core_type_arg_contains_any(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_type_contains_any(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(core_type_contains_any)
                || bounds.upper.as_deref().is_some_and(core_type_contains_any)
        }
    }
}

fn core_fun_spine_exact(
    ty: &typed_ir::Type,
    arity: usize,
) -> Option<(Vec<typed_ir::Type>, typed_ir::Type)> {
    let mut params = Vec::with_capacity(arity);
    let mut current = ty.clone();
    for _ in 0..arity {
        let (param, ret) = core_fun_parts_exact(&current)?;
        params.push(param);
        current = ret;
    }
    Some((params, current))
}

fn core_fun_spine_parts_exact(
    ty: &typed_ir::Type,
    arity: usize,
) -> Option<(
    Vec<(typed_ir::Type, typed_ir::Type)>,
    typed_ir::Type,
    typed_ir::Type,
)> {
    let mut params = Vec::with_capacity(arity);
    let mut current = ty.clone();
    let mut current_ret_effect = typed_ir::Type::Never;
    for _ in 0..arity {
        let typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = current
        else {
            return None;
        };
        params.push((*param, *param_effect));
        current_ret_effect = *ret_effect;
        current = *ret;
    }
    Some((params, current, current_ret_effect))
}

fn core_fun_arity(ty: &typed_ir::Type) -> usize {
    let mut arity = 0;
    let mut current = ty;
    while let typed_ir::Type::Fun { ret, .. } = current {
        arity += 1;
        current = ret;
    }
    arity
}

fn core_fun_parts_with_effects_exact(
    ty: &typed_ir::Type,
) -> Option<(
    typed_ir::Type,
    typed_ir::Type,
    typed_ir::Type,
    typed_ir::Type,
)> {
    let typed_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = ty
    else {
        return None;
    };
    Some((
        param.as_ref().clone(),
        param_effect.as_ref().clone(),
        ret.as_ref().clone(),
        ret_effect.as_ref().clone(),
    ))
}

fn core_fun_parts_exact(ty: &typed_ir::Type) -> Option<(typed_ir::Type, typed_ir::Type)> {
    let typed_ir::Type::Fun { param, ret, .. } = ty else {
        return None;
    };
    Some((param.as_ref().clone(), ret.as_ref().clone()))
}

fn runtime_value_and_effect(ty: &RuntimeType) -> (typed_ir::Type, typed_ir::Type) {
    match ty {
        RuntimeType::Thunk { effect, value } => (runtime_core_type(value), effect.clone()),
        other => (runtime_core_type(other), typed_ir::Type::Never),
    }
}

fn runtime_effect_row_candidate(ty: &typed_ir::Type) -> Option<&typed_ir::Type> {
    match ty {
        typed_ir::Type::Row { .. } => Some(ty),
        _ => None,
    }
}

fn debug_principal_unify_runtime_projection(
    slot: &str,
    target: Option<&typed_ir::Path>,
    template_value: &typed_ir::Type,
    actual_value: &typed_ir::Type,
    template_effect: &typed_ir::Type,
    actual_effect: &typed_ir::Type,
) {
    if !debug_principal_unify_enabled() {
        return;
    }
    let target = target
        .map(canonical_path)
        .unwrap_or_else(|| "<unknown>".to_string());
    eprintln!(
        "principal-unify runtime-slot {target} {slot}: value {template_value:?} <= {actual_value:?}; effect {template_effect:?} <= {actual_effect:?}"
    );
}

fn debug_principal_unify_skip(target: &typed_ir::Path, reason: &str) {
    if !debug_principal_unify_enabled() {
        return;
    }
    eprintln!(
        "principal-unify skip {} reason={reason}",
        canonical_path(target)
    );
}

fn debug_principal_unify_handler_plan(
    target: &typed_ir::Path,
    boundary: &HandlerCallBoundary,
    plan: &HandlerAdapterPlan,
) {
    if !debug_principal_unify_enabled() {
        return;
    }
    eprintln!(
        "principal-unify handler-plan {} consumes={:?} input_effect={:?} output_effect={:?} consumes_input={} preserves_output={} residual_before={:?} residual_after={:?} return_wrapper={:?}",
        canonical_path(target),
        boundary.consumes,
        boundary.input_effect,
        boundary.output_effect,
        boundary.consumes_input_effect,
        boundary.preserves_output_effect,
        plan.residual_before,
        plan.residual_after,
        plan.return_wrapper_effect
    );
}

fn debug_principal_unify_projection_outcome(
    outcome: &str,
    target: Option<&typed_ir::Path>,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &BTreeSet<typed_ir::TypeVar>,
) {
    if !debug_principal_unify_enabled() {
        return;
    }
    let target = target
        .map(canonical_path)
        .unwrap_or_else(|| "<unknown>".to_string());
    eprintln!(
        "principal-unify runtime-slot {target} {outcome}: substitutions={substitutions:?}; conflicts={conflicts:?}"
    );
}

fn debug_principal_unify_emit(
    original: &typed_ir::Path,
    path: &typed_ir::Path,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    if !debug_principal_unify_enabled() {
        return;
    }
    eprintln!(
        "principal-unify emit {} <= {} substitutions={substitutions:?}",
        canonical_path(path),
        canonical_path(original)
    );
}

fn debug_principal_unify_rewrite(original: &typed_ir::Path, path: &typed_ir::Path) {
    if !debug_principal_unify_enabled() {
        return;
    }
    eprintln!(
        "principal-unify rewrite {} -> {}",
        canonical_path(original),
        canonical_path(path)
    );
}

fn debug_principal_unify_contextual_candidates(
    target: &typed_ir::Path,
    matches: &[(&typed_ir::Path, &typed_ir::Type, usize, usize)],
) {
    if !debug_principal_unify_contextual_enabled() {
        return;
    }
    let rendered = matches
        .iter()
        .map(|(path, _, context, precision)| {
            format!("{}:{context}/{precision}", canonical_path(path))
        })
        .collect::<Vec<_>>()
        .join(", ");
    eprintln!(
        "principal-unify contextual {} remaining={} candidates=[{}]",
        canonical_path(target),
        matches.len(),
        rendered
    );
}

fn debug_principal_unify_active(
    target: &typed_ir::Path,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    if !debug_principal_unify_enabled() {
        return;
    }
    eprintln!(
        "principal-unify active {} substitutions={substitutions:?}",
        canonical_path(target)
    );
}

fn debug_principal_unify_normalized_plan(plan: &typed_ir::PrincipalElaborationPlan) {
    if !debug_principal_unify_enabled() {
        return;
    }
    let target = plan
        .target
        .as_ref()
        .map(canonical_path)
        .unwrap_or_else(|| "<unknown>".to_string());
    eprintln!(
        "principal-unify normalized {target}: complete={} substitutions={:?} reasons={:?}",
        plan.complete, plan.substitutions, plan.incomplete_reasons
    );
}

fn debug_principal_unify_role_candidates<'a>(
    target: &typed_ir::Path,
    receiver_ty: &typed_ir::Type,
    candidates: impl IntoIterator<Item = &'a typed_ir::Path>,
) {
    if !debug_principal_unify_enabled() {
        return;
    }
    let candidates = candidates
        .into_iter()
        .map(canonical_path)
        .collect::<Vec<_>>();
    eprintln!(
        "principal-unify role-candidates {} receiver={receiver_ty:?} candidates={candidates:?}",
        canonical_path(target)
    );
}

fn debug_principal_unify_role_ambiguous<'a>(
    target: &typed_ir::Path,
    receiver_ty: &typed_ir::Type,
    matches: impl IntoIterator<
        Item = (
            &'a typed_ir::Path,
            &'a BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
        ),
    >,
) {
    if !debug_principal_unify_enabled() {
        return;
    }
    let matches = matches
        .into_iter()
        .map(|(path, substitutions)| format!("{} {substitutions:?}", canonical_path(path)))
        .collect::<Vec<_>>();
    eprintln!(
        "principal-unify role-ambiguous {} receiver={receiver_ty:?} matches={matches:?}",
        canonical_path(target)
    );
}

fn debug_principal_unify_role_candidate_rejected(
    candidate: &typed_ir::Path,
    reason: &str,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    missing: &[typed_ir::TypeVar],
) {
    if !debug_principal_unify_enabled() {
        return;
    }
    eprintln!(
        "principal-unify role-reject {} reason={reason} substitutions={substitutions:?} missing={missing:?}",
        canonical_path(candidate)
    );
}

fn debug_principal_unify_local_value(name: &typed_ir::Name, ty: &RuntimeType) {
    if !debug_principal_unify_enabled() {
        return;
    }
    eprintln!("principal-unify local-value {name:?} = {ty:?}");
}

fn debug_principal_unify_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_some())
}

fn debug_principal_unify_contextual_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY_CONTEXTUAL").is_some())
}

pub(super) fn runtime_function_param_type(ty: &RuntimeType) -> Option<typed_ir::Type> {
    match ty {
        RuntimeType::Core(typed_ir::Type::Fun { param, .. }) => Some(param.as_ref().clone()),
        RuntimeType::Fun { param, .. } => Some(runtime_core_type(param)),
        RuntimeType::Unknown | RuntimeType::Thunk { .. } | RuntimeType::Core(_) => None,
    }
}

fn runtime_lambda_return_value_context(ty: &RuntimeType) -> Option<typed_ir::TypeBounds> {
    let RuntimeType::Fun { ret, .. } = ty else {
        return None;
    };
    Some(typed_ir::TypeBounds::exact(runtime_core_type(ret)))
}

fn runtime_function_type_with_param(ty: RuntimeType, param: typed_ir::Type) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun {
            param: existing_param,
            ret,
        } => Some(RuntimeType::Fun {
            param: Box::new(runtime_param_with_updated_value_shape(
                *existing_param,
                param,
            )),
            ret,
        }),
        RuntimeType::Thunk { effect, value } => runtime_function_type_with_param(*value, param)
            .map(|value| RuntimeType::thunk(effect, value)),
        RuntimeType::Core(typed_ir::Type::Fun {
            param_effect,
            ret_effect,
            ret,
            ..
        }) => Some(normalize_hir_function_type(RuntimeType::core(
            typed_ir::Type::Fun {
                param: Box::new(param),
                param_effect,
                ret_effect,
                ret,
            },
        ))),
        RuntimeType::Unknown | RuntimeType::Core(_) => None,
    }
}

fn runtime_param_with_updated_value_shape(
    existing: RuntimeType,
    value: typed_ir::Type,
) -> RuntimeType {
    match existing {
        RuntimeType::Thunk {
            effect,
            value: existing_value,
        } => RuntimeType::Thunk {
            effect,
            value: Box::new(runtime_param_with_updated_value_shape(
                *existing_value,
                value,
            )),
        },
        RuntimeType::Fun { .. } if matches!(value, typed_ir::Type::Fun { .. }) => {
            normalize_hir_function_type(RuntimeType::core(value))
        }
        _ => RuntimeType::core(value),
    }
}

fn runtime_context_function_type(bounds: Option<&typed_ir::TypeBounds>) -> Option<RuntimeType> {
    let ty = closed_type_from_bounds(bounds)?;
    let ty = normalize_hir_function_type(RuntimeType::core(ty));
    matches!(ty, RuntimeType::Fun { .. }).then_some(ty)
}

pub(super) fn closed_runtime_value_type(ty: &RuntimeType) -> Option<typed_ir::Type> {
    let ty = runtime_core_type(ty);
    closed_slot_type_usable(&ty, false).then_some(ty)
}

fn runtime_function_param_slot(ty: &RuntimeType) -> Option<(typed_ir::Type, typed_ir::Type)> {
    match ty {
        RuntimeType::Core(typed_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => Some((param.as_ref().clone(), param_effect.as_ref().clone())),
        RuntimeType::Fun { param, .. } => {
            let (value, effect) = runtime_value_and_effect(param);
            Some((value, effect))
        }
        RuntimeType::Unknown | RuntimeType::Thunk { .. } | RuntimeType::Core(_) => None,
    }
}

fn apply_argument_rewrite_context(
    callee: &Expr,
    evidence: Option<&typed_ir::ApplyEvidence>,
) -> Option<typed_ir::TypeBounds> {
    let evidence_arg_context = evidence.and_then(|evidence| evidence.expected_arg.clone());
    let evidence_param_effect = evidence.and_then(apply_evidence_param_effect);
    let callee_param_slot = runtime_function_param_slot(&callee.ty)
        .or_else(|| forced_callee_function_param_slot(callee));
    match (evidence_param_effect, callee_param_slot) {
        (Some(effect), _) if principal_param_effect_requires_thunk(&effect) => None,
        (_, Some((_param, effect))) if principal_param_effect_requires_thunk(&effect) => None,
        (_, Some((param, _effect))) => Some(typed_ir::TypeBounds::exact(param)),
        (None, None) if closed_type_from_bounds(evidence_arg_context.as_ref()).is_some() => {
            evidence_arg_context
        }
        (None, None) => runtime_function_param_type(&callee.ty)
            .map(typed_ir::TypeBounds::exact)
            .or(evidence_arg_context),
        (Some(_), None) => runtime_function_param_type(&callee.ty)
            .map(typed_ir::TypeBounds::exact)
            .or(evidence_arg_context),
    }
}

fn adapt_apply_argument_from_callee(expr: Expr) -> Expr {
    let Expr { ty, kind } = expr;
    let ExprKind::Apply {
        callee,
        arg,
        evidence,
        instantiation,
    } = kind
    else {
        return Expr::typed(kind, ty);
    };
    let Some((param, param_effect)) = runtime_function_param_slot(&callee.ty)
        .or_else(|| forced_callee_function_param_slot(&callee))
    else {
        if let Some(arg) = force_thunk_arg_after_forced_callee(&callee, &arg) {
            return Expr::typed(
                ExprKind::Apply {
                    callee,
                    arg: Box::new(arg),
                    evidence,
                    instantiation,
                },
                ty,
            );
        }
        return Expr::typed(
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            },
            ty,
        );
    };
    let Some(arg) = principal_arg_adapter(&arg, &param, &param_effect) else {
        return Expr::typed(
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            },
            ty,
        );
    };
    let callee = Box::new(refine_apply_callee_input_from_arg(*callee, &arg));
    Expr::typed(
        ExprKind::Apply {
            callee,
            arg: Box::new(arg),
            evidence,
            instantiation,
        },
        ty,
    )
}

fn refine_apply_expr_callee_input(expr: Expr) -> Expr {
    let Expr { ty, kind } = expr;
    let ExprKind::Apply {
        callee,
        arg,
        evidence,
        instantiation,
    } = kind
    else {
        return Expr::typed(kind, ty);
    };
    let callee = Box::new(refine_apply_callee_input_from_arg(*callee, &arg));
    Expr::typed(
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        },
        ty,
    )
}

fn refine_apply_callee_input_from_arg(mut callee: Expr, arg: &Expr) -> Expr {
    let Some(ty) = refine_apply_function_input_from_arg(callee.ty.clone(), arg) else {
        return callee;
    };
    callee.ty = ty;
    callee
}

fn refine_apply_function_input_from_arg(ty: RuntimeType, arg: &Expr) -> Option<RuntimeType> {
    let (arg_value, arg_effect) = runtime_value_and_effect(&arg.ty);
    if core_type_contains_unknown(&arg_value) || core_type_contains_unknown(&arg_effect) {
        return None;
    }
    if !closed_slot_type_usable(&arg_value, false) && !function_runtime_slot_usable(&arg_value) {
        return None;
    }
    let arg_runtime =
        runtime_type_from_core_value_and_effect(arg_value.clone(), arg_effect.clone());
    match ty {
        RuntimeType::Fun { param, ret } => {
            if !runtime_type_contains_unknown(&param) && !runtime_type_has_vars(&param) {
                return None;
            }
            Some(RuntimeType::fun(arg_runtime, *ret))
        }
        RuntimeType::Core(typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        }) => {
            if !core_type_contains_unknown(&param)
                && !core_type_has_vars(&param)
                && !core_type_contains_unknown(&param_effect)
                && !core_type_has_vars(&param_effect)
            {
                return None;
            }
            let param = if core_type_contains_unknown(&param) || core_type_has_vars(&param) {
                Box::new(arg_value)
            } else {
                param
            };
            let param_effect =
                if core_type_contains_unknown(&param_effect) || core_type_has_vars(&param_effect) {
                    Box::new(arg_effect)
                } else {
                    param_effect
                };
            Some(normalize_hir_function_type(RuntimeType::core(
                typed_ir::Type::Fun {
                    param,
                    param_effect,
                    ret_effect,
                    ret,
                },
            )))
        }
        RuntimeType::Thunk { effect, value } => refine_apply_function_input_from_arg(*value, arg)
            .map(|value| RuntimeType::thunk(effect, value)),
        RuntimeType::Unknown | RuntimeType::Core(_) => None,
    }
}

fn lambda_param_runtime_type(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { param, .. } => Some(param.as_ref().clone()),
        RuntimeType::Core(typed_ir::Type::Fun { param, .. }) => {
            Some(RuntimeType::core(*param.clone()))
        }
        _ => None,
    }
}

fn adapt_apply_result_from_evidence(
    expr: Expr,
    result_context: Option<&typed_ir::TypeBounds>,
) -> Expr {
    let Some(expected) = closed_type_from_bounds(result_context) else {
        return expr;
    };
    let Expr { ty, kind } = expr;
    if matches!(ty, RuntimeType::Thunk { .. }) {
        return Expr::typed(kind, ty);
    }
    let ExprKind::Apply {
        callee,
        arg,
        evidence,
        instantiation,
    } = kind
    else {
        return Expr::typed(kind, ty);
    };
    let Some(effect) = evidence
        .as_ref()
        .and_then(apply_evidence_return_effect)
        .filter(|effect| !effect_is_empty(effect))
    else {
        return Expr::typed(
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            },
            ty,
        );
    };
    let actual = runtime_core_type(&ty);
    let result_is_never = evidence
        .as_ref()
        .is_some_and(apply_evidence_result_is_never);
    if actual != expected && !type_compatible(&expected, &actual) && !result_is_never {
        return Expr::typed(
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            },
            ty,
        );
    }
    let outer_ty = RuntimeType::core(expected.clone());
    let inner_ty = RuntimeType::thunk(effect, RuntimeType::core(expected));
    let inner = Expr::typed(
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        },
        inner_ty,
    );
    Expr::typed(
        ExprKind::BindHere {
            expr: Box::new(inner),
        },
        outer_ty,
    )
}

fn handle_arm_payload_runtime_type(
    handler: &crate::ir::HandleEffect,
    operation: &typed_ir::Path,
) -> Option<RuntimeType> {
    if operation == &typed_ir::Path::default() {
        return None;
    }
    let effect = handler.residual_before.as_ref()?;
    effect_payload_type_for_operation(effect, operation).map(RuntimeType::core)
}

fn refresh_handle_payloads_from_handlers(expr: Expr) -> Expr {
    let Expr { ty, kind } = expr;
    let kind = match kind {
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(refresh_handle_payloads_from_handlers(*body)),
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(refresh_handle_payloads_from_handlers(*callee)),
            arg: Box::new(refresh_handle_payloads_from_handlers(*arg)),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(refresh_handle_payloads_from_handlers(*cond)),
            then_branch: Box::new(refresh_handle_payloads_from_handlers(*then_branch)),
            else_branch: Box::new(refresh_handle_payloads_from_handlers(*else_branch)),
            evidence,
        },
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .into_iter()
                .map(refresh_handle_payloads_from_handlers)
                .collect(),
        ),
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordExprField {
                    name: field.name,
                    value: refresh_handle_payloads_from_handlers(field.value),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadExpr::Head(expr) => {
                    RecordSpreadExpr::Head(Box::new(refresh_handle_payloads_from_handlers(*expr)))
                }
                RecordSpreadExpr::Tail(expr) => {
                    RecordSpreadExpr::Tail(Box::new(refresh_handle_payloads_from_handlers(*expr)))
                }
            }),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(refresh_handle_payloads_from_handlers(*value))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(refresh_handle_payloads_from_handlers(*base)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(refresh_handle_payloads_from_handlers(*scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    guard: arm.guard.map(refresh_handle_payloads_from_handlers),
                    body: refresh_handle_payloads_from_handlers(arm.body),
                })
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts
                .into_iter()
                .map(refresh_handle_payloads_from_handlers_stmt)
                .collect(),
            tail: tail.map(|tail| Box::new(refresh_handle_payloads_from_handlers(*tail))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            let arms = arms
                .into_iter()
                .map(|arm| {
                    let payload = match handle_arm_payload_runtime_type(&handler, &arm.effect) {
                        Some(payload_ty) => {
                            refresh_pattern_value_local_types(arm.payload, &payload_ty)
                        }
                        None => match wildcard_payload_unit_context(&arm.payload) {
                            Some(payload_ty) => refresh_pattern_value_local_types(
                                arm.payload,
                                &RuntimeType::core(payload_ty),
                            ),
                            None => arm.payload,
                        },
                    };
                    HandleArm {
                        effect: arm.effect,
                        payload,
                        resume: arm.resume,
                        guard: arm.guard.map(refresh_handle_payloads_from_handlers),
                        body: refresh_handle_payloads_from_handlers(arm.body),
                    }
                })
                .collect();
            ExprKind::Handle {
                body: Box::new(refresh_handle_payloads_from_handlers(*body)),
                arms,
                evidence,
                handler,
            }
        }
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(refresh_handle_payloads_from_handlers(*expr)),
        },
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect,
            value,
            expr: Box::new(refresh_handle_payloads_from_handlers(*expr)),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(refresh_handle_payloads_from_handlers(*body)),
        },
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => ExprKind::AddId {
            id,
            allowed,
            active,
            thunk: Box::new(refresh_handle_payloads_from_handlers(*thunk)),
        },
        ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from,
            to,
            expr: Box::new(refresh_handle_payloads_from_handlers(*expr)),
        },
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(refresh_handle_payloads_from_handlers(*expr)),
        },
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => kind,
    };
    Expr { ty, kind }
}

fn refresh_handle_payloads_from_handlers_stmt(stmt: Stmt) -> Stmt {
    match stmt {
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern,
            value: refresh_handle_payloads_from_handlers(value),
        },
        Stmt::Expr(expr) => Stmt::Expr(refresh_handle_payloads_from_handlers(expr)),
        Stmt::Module { def, body } => Stmt::Module {
            def,
            body: refresh_handle_payloads_from_handlers(body),
        },
    }
}

fn project_handler_consumed_payload_substitutions(
    params: &[(typed_ir::Type, typed_ir::Type)],
    input_effect: &typed_ir::Type,
    consumes: &[typed_ir::Path],
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) -> BTreeSet<typed_ir::TypeVar> {
    let mut projected = BTreeSet::new();
    for consumed in consumes {
        let Some(actual_payload) = effect_payload_type_for_operation(input_effect, consumed)
            .filter(|payload| !core_type_is_imprecise_runtime_slot(payload))
        else {
            continue;
        };
        for (_param, param_effect) in params {
            project_consumed_payload_from_effect(
                param_effect,
                consumed,
                &actual_payload,
                required_vars,
                substitutions,
                conflicts,
                &mut projected,
            );
        }
    }
    projected
}

fn project_consumed_payload_from_effect(
    effect: &typed_ir::Type,
    consumed: &typed_ir::Path,
    actual_payload: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    projected: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match effect {
        typed_ir::Type::Named { path, args } if effect_paths_match(path, consumed) => {
            let Some(template_payload) = effect_payload_type_from_args(args) else {
                return;
            };
            let mut payload_vars = BTreeSet::new();
            collect_core_type_vars(&template_payload, &mut payload_vars);
            project_closed_substitutions_from_type(
                &template_payload,
                actual_payload,
                required_vars,
                substitutions,
                conflicts,
                false,
                32,
            );
            projected.extend(
                payload_vars
                    .into_iter()
                    .filter(|var| required_vars.contains(var)),
            );
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                project_consumed_payload_from_effect(
                    item,
                    consumed,
                    actual_payload,
                    required_vars,
                    substitutions,
                    conflicts,
                    projected,
                );
            }
            project_consumed_payload_from_effect(
                tail,
                consumed,
                actual_payload,
                required_vars,
                substitutions,
                conflicts,
                projected,
            );
        }
        _ => {}
    }
}

fn project_handler_payload_result_container_items(
    ret: &typed_ir::Type,
    effect: &typed_ir::Type,
    consumes: &[typed_ir::Path],
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    for consumed in consumes {
        let Some(payload) = effect_payload_type_for_operation(effect, consumed)
            .filter(|payload| !core_type_is_imprecise_runtime_slot(payload))
        else {
            continue;
        };
        project_payload_result_container_items(
            ret,
            &payload,
            required_vars,
            substitutions,
            conflicts,
        );
    }
}

fn project_payload_result_container_items(
    ty: &typed_ir::Type,
    payload: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match ty {
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                project_constructor_payload_arg_vars(
                    arg,
                    payload,
                    required_vars,
                    substitutions,
                    conflicts,
                );
            }
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            for item in items {
                project_payload_result_container_items(
                    item,
                    payload,
                    required_vars,
                    substitutions,
                    conflicts,
                );
            }
        }
        _ => {}
    }
}

fn runtime_type_is_unit_core(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Named { path, args } if args.is_empty() && path.segments.len() == 1 && path.segments[0].0 == "unit")
}

fn relative_operation_payload_type(
    effect: &typed_ir::Type,
    operation: &typed_ir::Path,
) -> Option<typed_ir::Type> {
    if operation.segments.len() != 1 {
        return None;
    }
    let mut payloads = Vec::new();
    collect_non_empty_effect_payload_types(effect, &mut payloads);
    match payloads.as_slice() {
        [payload] => Some(payload.clone()),
        _ => None,
    }
}

fn collect_non_empty_effect_payload_types(effect: &typed_ir::Type, out: &mut Vec<typed_ir::Type>) {
    match effect {
        typed_ir::Type::Named { args, .. } if !args.is_empty() => {
            if let Some(payload) = effect_payload_type_from_args(args) {
                out.push(payload);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_non_empty_effect_payload_types(item, out);
            }
            collect_non_empty_effect_payload_types(tail, out);
        }
        _ => {}
    }
}

fn single_precise_effect_payload_type(effect: &typed_ir::Type) -> Option<typed_ir::Type> {
    let mut payloads = Vec::new();
    collect_non_empty_effect_payload_types(effect, &mut payloads);
    let payloads = payloads
        .into_iter()
        .filter(|payload| !core_type_is_imprecise_runtime_slot(payload))
        .collect::<Vec<_>>();
    let [payload] = payloads.as_slice() else {
        return None;
    };
    Some(payload.clone())
}

fn effect_payload_type_from_args(args: &[typed_ir::TypeArg]) -> Option<typed_ir::Type> {
    match args {
        [] => None,
        [arg] => effect_payload_arg_type(arg),
        _ => {
            let payloads = args
                .iter()
                .filter_map(effect_payload_arg_type)
                .collect::<Vec<_>>();
            (!payloads.is_empty()).then_some(typed_ir::Type::Tuple(payloads))
        }
    }
}

fn runtime_unit_type() -> typed_ir::Type {
    typed_ir::Type::Named {
        path: typed_ir::Path::from_name(typed_ir::Name("unit".to_string())),
        args: Vec::new(),
    }
}

fn wildcard_payload_unit_context(pattern: &Pattern) -> Option<typed_ir::Type> {
    matches!(pattern, Pattern::Wildcard { .. }).then(runtime_unit_type)
}

fn effect_payload_arg_type(arg: &typed_ir::TypeArg) -> Option<typed_ir::Type> {
    match arg {
        typed_ir::TypeArg::Type(ty) => Some(ty.clone()),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().or(bounds.upper.as_deref()).cloned()
        }
    }
}

fn unwrap_handler_body_bind_here(body: Expr, handler: &crate::ir::HandleEffect) -> Expr {
    let Expr {
        ty,
        kind: ExprKind::BindHere { expr },
    } = body
    else {
        return body;
    };
    let RuntimeType::Thunk { effect, .. } = &expr.ty else {
        return Expr::typed(ExprKind::BindHere { expr }, ty);
    };
    let paths = effect_paths(effect);
    if paths.iter().any(|path| {
        handler
            .consumes
            .iter()
            .any(|consumed| effect_paths_match(consumed, path))
    }) {
        return *expr;
    }
    Expr::typed(ExprKind::BindHere { expr }, ty)
}

fn ensure_effectful_handler_body_thunk(body: Expr, handler: &crate::ir::HandleEffect) -> Expr {
    if handler.consumes.is_empty() || matches!(body.ty, RuntimeType::Thunk { .. }) {
        return body;
    }
    let effect = handler
        .residual_before
        .clone()
        .filter(|effect| !effect_is_empty(effect))
        .unwrap_or_else(|| typed_ir::Type::Row {
            items: handler
                .consumes
                .iter()
                .cloned()
                .map(|path| typed_ir::Type::Named {
                    path,
                    args: Vec::new(),
                })
                .collect(),
            tail: Box::new(typed_ir::Type::Never),
        });
    let value = body.ty.clone();
    Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value: value.clone(),
            expr: Box::new(body),
        },
        RuntimeType::thunk(effect, value),
    )
}

fn apply_evidence_return_effect(evidence: &typed_ir::ApplyEvidence) -> Option<typed_ir::Type> {
    closed_type_from_bounds(evidence.expected_callee.as_ref())
        .or_else(|| closed_type_from_bounds(Some(&evidence.callee)))
        .and_then(|ty| match ty {
            typed_ir::Type::Fun { ret_effect, .. } => Some(*ret_effect),
            _ => None,
        })
}

pub(super) fn apply_evidence_result_is_never(evidence: &typed_ir::ApplyEvidence) -> bool {
    choose_bounds_type(&evidence.result, BoundsChoice::ValidationEvidence)
        .is_some_and(|ty| matches!(ty, typed_ir::Type::Never))
        || evidence
            .principal_callee
            .as_ref()
            .and_then(|ty| core_fun_spine_parts_exact(ty, 1))
            .is_some_and(|(_params, ret, _ret_effect)| matches!(ret, typed_ir::Type::Never))
        || closed_type_from_bounds(evidence.expected_callee.as_ref())
            .or_else(|| closed_type_from_bounds(Some(&evidence.callee)))
            .and_then(|ty| core_fun_spine_parts_exact(&ty, 1))
            .is_some_and(|(_params, ret, _ret_effect)| matches!(ret, typed_ir::Type::Never))
}

fn expr_is_never_effect_op_apply(expr: &Expr, unifier: &PrincipalUnifier) -> bool {
    let ExprKind::Apply { callee, .. } = &expr.kind else {
        return false;
    };
    matches!(
        &callee.kind,
        ExprKind::EffectOp(path) if unifier.never_effect_ops.contains(path)
    )
}

fn apply_evidence_param_effect(evidence: &typed_ir::ApplyEvidence) -> Option<typed_ir::Type> {
    closed_type_from_bounds(evidence.expected_callee.as_ref())
        .or_else(|| closed_type_from_bounds(Some(&evidence.callee)))
        .and_then(|ty| match ty {
            typed_ir::Type::Fun { param_effect, .. } => Some(*param_effect),
            _ => None,
        })
}

fn forced_callee_function_param_slot(callee: &Expr) -> Option<(typed_ir::Type, typed_ir::Type)> {
    let ExprKind::BindHere { expr } = &callee.kind else {
        return None;
    };
    let RuntimeType::Thunk { value, .. } = &expr.ty else {
        return None;
    };
    runtime_function_param_slot(value)
}

fn force_thunk_arg_after_forced_callee(callee: &Expr, arg: &Expr) -> Option<Expr> {
    if !matches!(callee.kind, ExprKind::BindHere { .. }) {
        return None;
    }
    let RuntimeType::Thunk { effect, value } = &arg.ty else {
        return None;
    };
    if effect_is_empty(effect) {
        return None;
    }
    Some(Expr::typed(
        ExprKind::BindHere {
            expr: Box::new(arg.clone()),
        },
        value.as_ref().clone(),
    ))
}

fn principal_plan_result_closed_type(
    result: &typed_ir::PrincipalElaborationResult,
) -> Option<typed_ir::Type> {
    result
        .expected_runtime
        .clone()
        .or_else(|| closed_type_from_bounds(result.contextual.as_ref()))
        .or_else(|| closed_type_from_bounds(Some(&result.intrinsic)))
}

fn principal_plan_arg_closed_type(
    arg: &typed_ir::PrincipalElaborationArg,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<typed_ir::Type> {
    choose_precise_closed_type([
        arg.expected_runtime
            .as_ref()
            .map(|ty| substitute_type(ty, substitutions))
            .filter(|ty| closed_slot_type_usable(ty, false)),
        arg.contextual
            .as_ref()
            .and_then(|bounds| substituted_closed_type_from_bounds(bounds, substitutions)),
        substituted_closed_type_from_bounds(&arg.intrinsic, substitutions),
    ])
}

fn project_principal_arg_slot_substitutions(
    param: &typed_ir::Type,
    arg: &typed_ir::PrincipalElaborationArg,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    if let Some(expected) = &arg.expected_runtime {
        let expected = substitute_type(expected, substitutions);
        project_closed_substitutions_from_type(
            param,
            &expected,
            required_vars,
            substitutions,
            conflicts,
            false,
            64,
        );
    }
    if let Some(contextual) = &arg.contextual {
        project_closed_substitutions_from_type_bounds(
            param,
            contextual,
            required_vars,
            substitutions,
            conflicts,
            false,
            64,
        );
    }
    if let Some(contextual) = &arg.contextual {
        project_principal_slot_relation_substitutions(
            &arg.intrinsic,
            contextual,
            required_vars,
            substitutions,
            conflicts,
            false,
        );
    }
    project_closed_substitutions_from_type_bounds(
        param,
        &arg.intrinsic,
        required_vars,
        substitutions,
        conflicts,
        false,
        64,
    );
}

fn principal_plan_result_closed_type_with_substitutions(
    result: &typed_ir::PrincipalElaborationResult,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<typed_ir::Type> {
    choose_precise_closed_type([
        result
            .expected_runtime
            .as_ref()
            .map(|ty| substitute_type(ty, substitutions))
            .filter(|ty| closed_slot_type_usable(ty, false)),
        result
            .contextual
            .as_ref()
            .and_then(|bounds| substituted_closed_type_from_bounds(bounds, substitutions)),
        substituted_closed_type_from_bounds(&result.intrinsic, substitutions),
    ])
}

fn plan_has_imprecise_choice_slot_substitutions(
    plan: &typed_ir::PrincipalElaborationPlan,
    binding: &Binding,
) -> bool {
    let substitutions = plan_substitution_map(plan);
    let required_vars = binding_required_vars(binding);
    plan.args.iter().any(|arg| {
        slot_has_imprecise_choice_substitution(
            &arg.intrinsic,
            arg.contextual.as_ref(),
            arg.expected_runtime.as_ref(),
            &required_vars,
            &substitutions,
        )
    }) || slot_has_imprecise_choice_substitution(
        &plan.result.intrinsic,
        plan.result.contextual.as_ref(),
        plan.result.expected_runtime.as_ref(),
        &required_vars,
        &substitutions,
    )
}

fn slot_has_imprecise_choice_substitution(
    intrinsic: &typed_ir::TypeBounds,
    contextual: Option<&typed_ir::TypeBounds>,
    expected_runtime: Option<&typed_ir::Type>,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> bool {
    let context_precise = expected_runtime.is_some_and(|ty| closed_slot_type_usable(ty, false))
        || contextual
            .and_then(|bounds| substituted_closed_type_from_bounds(bounds, substitutions))
            .is_some();
    if context_precise {
        return false;
    }
    let mut choice_vars = BTreeSet::new();
    if let Some(lower) = intrinsic.lower.as_deref() {
        collect_choice_required_vars(lower, required_vars, &mut choice_vars);
    }
    if let Some(upper) = intrinsic.upper.as_deref() {
        collect_choice_required_vars(upper, required_vars, &mut choice_vars);
    }
    choice_vars
        .iter()
        .any(|var| substitutions.contains_key(var))
}

fn collect_choice_required_vars(
    ty: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    out: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match ty {
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_vars_in_choice_item(item, required_vars, out);
            }
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    typed_ir::TypeArg::Type(ty) => {
                        collect_choice_required_vars(ty, required_vars, out);
                    }
                    typed_ir::TypeArg::Bounds(bounds) => {
                        if let Some(lower) = bounds.lower.as_deref() {
                            collect_choice_required_vars(lower, required_vars, out);
                        }
                        if let Some(upper) = bounds.upper.as_deref() {
                            collect_choice_required_vars(upper, required_vars, out);
                        }
                    }
                }
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_choice_required_vars(param, required_vars, out);
            collect_choice_required_vars(param_effect, required_vars, out);
            collect_choice_required_vars(ret_effect, required_vars, out);
            collect_choice_required_vars(ret, required_vars, out);
        }
        typed_ir::Type::Tuple(items) => {
            for item in items {
                collect_choice_required_vars(item, required_vars, out);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_choice_required_vars(&field.value, required_vars, out);
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_choice_required_vars(payload, required_vars, out);
                }
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_choice_required_vars(item, required_vars, out);
            }
            collect_choice_required_vars(tail, required_vars, out);
        }
        typed_ir::Type::Recursive { body, .. } => {
            collect_choice_required_vars(body, required_vars, out);
        }
        typed_ir::Type::Unknown
        | typed_ir::Type::Any
        | typed_ir::Type::Never
        | typed_ir::Type::Var(_) => {}
    }
}

fn collect_vars_in_choice_item(
    ty: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    out: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match ty {
        typed_ir::Type::Var(var) if required_vars.contains(var) => {
            out.insert(var.clone());
        }
        other => collect_choice_required_vars(other, required_vars, out),
    }
}

fn project_principal_result_slot_substitutions(
    ret: &typed_ir::Type,
    result: &typed_ir::PrincipalElaborationResult,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    if let Some(expected) = &result.expected_runtime {
        let expected = substitute_type(expected, substitutions);
        project_closed_substitutions_from_type(
            ret,
            &expected,
            required_vars,
            substitutions,
            conflicts,
            false,
            64,
        );
    }
    if let Some(contextual) = &result.contextual {
        project_closed_substitutions_from_type_bounds(
            ret,
            contextual,
            required_vars,
            substitutions,
            conflicts,
            false,
            64,
        );
    }
    if let Some(contextual) = &result.contextual {
        project_principal_slot_relation_substitutions(
            &result.intrinsic,
            contextual,
            required_vars,
            substitutions,
            conflicts,
            false,
        );
    }
    project_closed_substitutions_from_type_bounds(
        ret,
        &result.intrinsic,
        required_vars,
        substitutions,
        conflicts,
        false,
        64,
    );
}

fn project_result_constructor_payload_substitutions(
    result: &typed_ir::PrincipalElaborationResult,
    payload: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    let intrinsic = substitute_bounds(result.intrinsic.clone(), substitutions);
    let Some(intrinsic) = exact_type_from_bounds_allow_unknown(&intrinsic) else {
        return;
    };
    let Some(contextual) = result
        .contextual
        .as_ref()
        .map(|bounds| substitute_bounds(bounds.clone(), substitutions))
        .and_then(|bounds| exact_type_from_bounds_allow_unknown(&bounds))
    else {
        project_union_constructor_payload_vars(
            &intrinsic,
            payload,
            required_vars,
            substitutions,
            conflicts,
        );
        return;
    };
    project_constructor_payload_substitutions(
        &intrinsic,
        &contextual,
        payload,
        required_vars,
        substitutions,
        conflicts,
    );
    project_union_constructor_payload_vars(
        &contextual,
        payload,
        required_vars,
        substitutions,
        conflicts,
    );
}

fn project_union_constructor_payload_vars(
    contextual: &typed_ir::Type,
    payload: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    let typed_ir::Type::Union(items) = contextual else {
        return;
    };
    let mut constructed = None::<typed_ir::Type>;
    for item in items {
        let typed_ir::Type::Named { args, .. } = item else {
            continue;
        };
        for arg in args {
            project_constructor_payload_arg_vars(
                arg,
                payload,
                required_vars,
                substitutions,
                conflicts,
            );
        }
        let substituted = substitute_type(item, substitutions);
        if constructed_union_item_for_payload(&substituted, payload).is_some() {
            constructed = Some(substituted);
        }
    }
    let Some(constructed) = constructed else {
        return;
    };
    for item in items {
        if let typed_ir::Type::Var(var) = item
            && required_vars.contains(var)
        {
            insert_projected_value_substitution(
                substitutions,
                conflicts,
                var.clone(),
                constructed.clone(),
            );
        }
    }
}

fn exact_type_from_bounds_allow_unknown(bounds: &typed_ir::TypeBounds) -> Option<typed_ir::Type> {
    match (bounds.lower.as_deref(), bounds.upper.as_deref()) {
        (Some(lower), Some(upper)) if lower == upper => Some(lower.clone()),
        (Some(ty), None) | (None, Some(ty)) => Some(ty.clone()),
        _ => None,
    }
}

fn project_constructor_payload_substitutions(
    intrinsic: &typed_ir::Type,
    contextual: &typed_ir::Type,
    payload: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    let typed_ir::Type::Named {
        path,
        args: intrinsic_args,
    } = intrinsic
    else {
        return;
    };
    let typed_ir::Type::Union(items) = contextual else {
        return;
    };
    let Some(contextual_named) = items.iter().find_map(|item| match item {
        typed_ir::Type::Named {
            path: item_path,
            args,
        } if item_path == path && args.len() == intrinsic_args.len() => Some(args),
        _ => None,
    }) else {
        return;
    };
    let normal_payload_args = intrinsic_args
        .iter()
        .zip(contextual_named)
        .map(|(intrinsic_arg, contextual_arg)| {
            constructor_payload_arg_substitution(intrinsic_arg, contextual_arg, payload)
        })
        .collect::<Option<Vec<_>>>();
    let Some(normal_payload_args) = normal_payload_args else {
        return;
    };
    let normal_result = typed_ir::Type::Named {
        path: path.clone(),
        args: normal_payload_args,
    };
    for item in items {
        match item {
            typed_ir::Type::Var(var) if required_vars.contains(var) => {
                insert_projected_value_substitution(
                    substitutions,
                    conflicts,
                    var.clone(),
                    normal_result.clone(),
                );
            }
            typed_ir::Type::Named {
                path: item_path,
                args,
            } if item_path == path && args.len() == intrinsic_args.len() => {
                for arg in args {
                    project_constructor_payload_arg_vars(
                        arg,
                        payload,
                        required_vars,
                        substitutions,
                        conflicts,
                    );
                }
            }
            _ => {}
        }
    }
}

fn constructor_payload_arg_substitution(
    intrinsic: &typed_ir::TypeArg,
    contextual: &typed_ir::TypeArg,
    payload: &typed_ir::Type,
) -> Option<typed_ir::TypeArg> {
    match (intrinsic, contextual) {
        (
            typed_ir::TypeArg::Type(typed_ir::Type::Unknown),
            typed_ir::TypeArg::Type(typed_ir::Type::Var(_)),
        ) => Some(typed_ir::TypeArg::Type(payload.clone())),
        (typed_ir::TypeArg::Type(typed_ir::Type::Unknown), typed_ir::TypeArg::Bounds(bounds))
            if type_bounds_contain_type_var(bounds) =>
        {
            Some(typed_ir::TypeArg::Type(payload.clone()))
        }
        (typed_ir::TypeArg::Bounds(bounds), typed_ir::TypeArg::Type(typed_ir::Type::Var(_)))
            if bounds
                .lower
                .as_deref()
                .is_some_and(|ty| matches!(ty, typed_ir::Type::Unknown))
                || bounds
                    .upper
                    .as_deref()
                    .is_some_and(|ty| matches!(ty, typed_ir::Type::Unknown)) =>
        {
            Some(typed_ir::TypeArg::Type(payload.clone()))
        }
        (typed_ir::TypeArg::Bounds(bounds), typed_ir::TypeArg::Bounds(contextual_bounds))
            if (bounds
                .lower
                .as_deref()
                .is_some_and(|ty| matches!(ty, typed_ir::Type::Unknown))
                || bounds
                    .upper
                    .as_deref()
                    .is_some_and(|ty| matches!(ty, typed_ir::Type::Unknown)))
                && type_bounds_contain_type_var(contextual_bounds) =>
        {
            Some(typed_ir::TypeArg::Type(payload.clone()))
        }
        (typed_ir::TypeArg::Type(left), typed_ir::TypeArg::Type(right)) if left == right => {
            Some(contextual.clone())
        }
        _ => None,
    }
}

fn type_bounds_contain_type_var(bounds: &typed_ir::TypeBounds) -> bool {
    let mut vars = BTreeSet::new();
    if let Some(lower) = bounds.lower.as_deref() {
        collect_core_type_vars(lower, &mut vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_core_type_vars(upper, &mut vars);
    }
    !vars.is_empty()
}

fn project_constructor_payload_arg_vars(
    arg: &typed_ir::TypeArg,
    payload: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match arg {
        typed_ir::TypeArg::Type(ty) => project_constructor_payload_type_vars(
            ty,
            payload,
            required_vars,
            substitutions,
            conflicts,
        ),
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                project_constructor_payload_type_vars(
                    lower,
                    payload,
                    required_vars,
                    substitutions,
                    conflicts,
                );
            }
            if let Some(upper) = bounds.upper.as_deref() {
                project_constructor_payload_type_vars(
                    upper,
                    payload,
                    required_vars,
                    substitutions,
                    conflicts,
                );
            }
        }
    }
}

fn project_constructor_payload_type_vars(
    ty: &typed_ir::Type,
    payload: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match ty {
        typed_ir::Type::Var(var) if required_vars.contains(var) => {
            insert_projected_value_substitution(
                substitutions,
                conflicts,
                var.clone(),
                payload.clone(),
            );
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            for item in items {
                project_constructor_payload_type_vars(
                    item,
                    payload,
                    required_vars,
                    substitutions,
                    conflicts,
                );
            }
        }
        typed_ir::Type::Recursive { body, .. } => project_constructor_payload_type_vars(
            body,
            payload,
            required_vars,
            substitutions,
            conflicts,
        ),
        _ => {}
    }
}

fn project_direct_runtime_arg_substitutions(
    principal: &typed_ir::Type,
    args: &[&Expr],
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) -> BTreeSet<typed_ir::TypeVar> {
    let mut projected = BTreeSet::new();
    let Some((params, _ret, _ret_effect)) = core_fun_spine_parts_exact(principal, args.len())
    else {
        return projected;
    };
    for (arg, (param, _param_effect)) in args.iter().zip(params) {
        let (actual, actual_effect) = runtime_value_and_effect(&arg.ty);
        if effectful_erased_arg_should_wait_for_role_completion(&actual, &actual_effect) {
            continue;
        }
        project_direct_runtime_arg_value_substitution(
            &param,
            &actual,
            required_vars,
            substitutions,
            conflicts,
            &mut projected,
        );
    }
    projected
}

fn effectful_erased_arg_should_wait_for_role_completion(
    actual: &typed_ir::Type,
    actual_effect: &typed_ir::Type,
) -> bool {
    !effect_is_empty(actual_effect)
        && (matches!(actual, typed_ir::Type::Never)
            || matches!(actual, typed_ir::Type::Tuple(items) if items.is_empty()))
}

fn project_effectful_erased_role_arg_value_from_effect(
    param: &typed_ir::Type,
    actual_effect: &typed_ir::Type,
    requirements: &[typed_ir::RoleRequirement],
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    let typed_ir::Type::Var(var) = param else {
        return;
    };
    if !required_vars.contains(var) || !role_requirements_use_input_var(requirements, var) {
        return;
    }
    let Some(actual) = effect_marker_value_projection_type(actual_effect) else {
        return;
    };
    project_closed_substitutions_from_type(
        param,
        &actual,
        required_vars,
        substitutions,
        conflicts,
        false,
        64,
    );
}

fn role_requirements_use_input_var(
    requirements: &[typed_ir::RoleRequirement],
    var: &typed_ir::TypeVar,
) -> bool {
    requirements.iter().any(|requirement| {
        requirement.args.iter().any(|arg| {
            let typed_ir::RoleRequirementArg::Input(bounds) = arg else {
                return false;
            };
            type_bounds_contain_specific_type_var(bounds, var)
        })
    })
}

fn type_bounds_contain_specific_type_var(
    bounds: &typed_ir::TypeBounds,
    var: &typed_ir::TypeVar,
) -> bool {
    let mut vars = BTreeSet::new();
    if let Some(lower) = bounds.lower.as_deref() {
        collect_core_type_vars(lower, &mut vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_core_type_vars(upper, &mut vars);
    }
    vars.contains(var)
}

fn effect_marker_value_projection_type(effect: &typed_ir::Type) -> Option<typed_ir::Type> {
    role_impl_effect_projection_types(effect)
        .into_iter()
        .rev()
        .find(|ty| closed_slot_type_usable(ty, false))
}

fn remove_effectful_erased_arg_value_substitutions(
    principal: &typed_ir::Type,
    args: &[&Expr],
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    let Some((params, _ret, _ret_effect)) = core_fun_spine_parts_exact(principal, args.len())
    else {
        return;
    };
    for (arg, (param, _param_effect)) in args.iter().zip(params) {
        let typed_ir::Type::Var(var) = param else {
            continue;
        };
        if !required_vars.contains(&var) {
            continue;
        }
        let (actual, actual_effect) = runtime_value_and_effect(&arg.ty);
        if effectful_erased_arg_should_wait_for_role_completion(&actual, &actual_effect) {
            substitutions.remove(&var);
        }
    }
}

fn fill_effectful_erased_arg_never_substitutions(
    principal: &typed_ir::Type,
    args: &[&Expr],
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    let Some((params, _ret, _ret_effect)) = core_fun_spine_parts_exact(principal, args.len())
    else {
        return;
    };
    for (arg, (param, _param_effect)) in args.iter().zip(params) {
        let typed_ir::Type::Var(var) = param else {
            continue;
        };
        if !required_vars.contains(&var) || substitutions.contains_key(&var) {
            continue;
        }
        let (actual, _actual_effect) = runtime_value_and_effect(&arg.ty);
        if matches!(actual, typed_ir::Type::Never) {
            substitutions.insert(var, typed_ir::Type::Never);
        }
    }
}

fn mark_never_runtime_arg_slots(plan: &mut typed_ir::PrincipalElaborationPlan, args: &[&Expr]) {
    for arg_slot in &mut plan.args {
        let Some(arg) = args.get(arg_slot.index) else {
            continue;
        };
        let (actual, _actual_effect) = runtime_value_and_effect(&arg.ty);
        if matches!(actual, typed_ir::Type::Never) {
            arg_slot.expected_runtime = Some(typed_ir::Type::Never);
        }
    }
}

fn project_direct_runtime_arg_value_substitution(
    param: &typed_ir::Type,
    actual: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    projected: &mut BTreeSet<typed_ir::TypeVar>,
) {
    let typed_ir::Type::Var(var) = param else {
        return;
    };
    if !required_vars.contains(var) {
        return;
    }
    let actual = normalize_projected_value_substitution_type(actual, substitutions);
    let actual = project_runtime_type_with_vars(&actual, &BTreeSet::new());
    if !closed_slot_type_usable(&actual, false) {
        return;
    }
    projected.insert(var.clone());
    insert_runtime_arg_value_substitution(substitutions, conflicts, var.clone(), actual);
}

fn insert_runtime_arg_value_substitution(
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    var: typed_ir::TypeVar,
    ty: typed_ir::Type,
) {
    let ty = normalize_projected_value_shape(ty);
    let Some(existing) = substitutions.get(&var) else {
        substitutions.insert(var.clone(), ty);
        conflicts.remove(&var);
        return;
    };
    let existing = normalize_projected_value_shape(existing.clone());
    let merged = merge_projected_value_type_precision(&existing, &ty);
    if let Some(merged) = merged {
        substitutions.insert(var.clone(), merged);
    } else {
        substitutions.insert(var.clone(), ty);
    }
    conflicts.remove(&var);
}

fn unique_closed_callback_param_candidate(
    plan: &typed_ir::PrincipalElaborationPlan,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<typed_ir::Type> {
    let mut candidates = Vec::new();
    for arg in &plan.args {
        collect_callback_param_candidates_from_bounds(
            &arg.intrinsic,
            substitutions,
            &mut candidates,
        );
        if let Some(contextual) = &arg.contextual {
            collect_callback_param_candidates_from_bounds(
                contextual,
                substitutions,
                &mut candidates,
            );
        }
        if let Some(expected) = &arg.expected_runtime {
            collect_callback_param_candidates_from_type(expected, substitutions, &mut candidates);
        }
    }
    let mut unique = Vec::<typed_ir::Type>::new();
    for candidate in candidates {
        if !unique.iter().any(|existing| existing == &candidate) {
            unique.push(candidate);
        }
    }
    let [candidate] = unique.as_slice() else {
        return None;
    };
    Some(candidate.clone())
}

fn collect_callback_param_candidates_from_bounds(
    bounds: &typed_ir::TypeBounds,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    out: &mut Vec<typed_ir::Type>,
) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_callback_param_candidates_from_type(lower, substitutions, out);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_callback_param_candidates_from_type(upper, substitutions, out);
    }
}

fn collect_callback_param_candidates_from_type(
    ty: &typed_ir::Type,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    out: &mut Vec<typed_ir::Type>,
) {
    let ty = substitute_type(ty, substitutions);
    let typed_ir::Type::Fun { param, .. } = ty else {
        return;
    };
    if closed_slot_type_usable(&param, false) {
        out.push(*param);
    } else {
        collect_closed_choice_type_candidates(&param, out);
    }
}

fn collect_closed_choice_type_candidates(ty: &typed_ir::Type, out: &mut Vec<typed_ir::Type>) {
    match ty {
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_closed_choice_type_candidates(item, out);
            }
        }
        typed_ir::Type::Recursive { body, .. } => collect_closed_choice_type_candidates(body, out),
        _ if closed_slot_type_usable(ty, false) => out.push(ty.clone()),
        _ => {}
    }
}

fn project_principal_slot_relation_substitutions(
    intrinsic: &typed_ir::TypeBounds,
    contextual: &typed_ir::TypeBounds,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    allow_never: bool,
) {
    let intrinsic = substitute_bounds(intrinsic.clone(), substitutions);
    let contextual = substitute_bounds(contextual.clone(), substitutions);
    if let Some(actual) = closed_type_from_bounds(Some(&contextual)) {
        project_type_bounds_as_templates(
            &intrinsic,
            &actual,
            required_vars,
            substitutions,
            conflicts,
            allow_never,
        );
    }
    if let Some(actual) = closed_type_from_bounds(Some(&intrinsic)) {
        project_type_bounds_as_templates(
            &contextual,
            &actual,
            required_vars,
            substitutions,
            conflicts,
            allow_never,
        );
    }
}

fn project_type_bounds_as_templates(
    templates: &typed_ir::TypeBounds,
    actual: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    allow_never: bool,
) {
    if let Some(lower) = templates.lower.as_deref() {
        project_slot_lower_template_against_closed_actual(
            lower,
            actual,
            required_vars,
            substitutions,
            conflicts,
            allow_never,
            64,
        );
    }
    if let Some(upper) = templates.upper.as_deref() {
        project_slot_upper_template_against_closed_actual(
            upper,
            actual,
            required_vars,
            substitutions,
            conflicts,
            allow_never,
            64,
        );
    }
}

fn project_slot_lower_template_against_closed_actual(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    allow_never: bool,
    depth: usize,
) {
    project_closed_substitutions_from_type(
        template,
        actual,
        required_vars,
        substitutions,
        conflicts,
        allow_never,
        depth,
    );
    project_choice_var_items_against_closed_actual(
        template,
        actual,
        required_vars,
        substitutions,
        conflicts,
        allow_never,
        SlotChoicePolarity::Lower,
        depth,
    );
}

fn project_slot_upper_template_against_closed_actual(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    allow_never: bool,
    depth: usize,
) {
    project_closed_substitutions_from_type(
        template,
        actual,
        required_vars,
        substitutions,
        conflicts,
        allow_never,
        depth,
    );
    project_choice_var_items_against_closed_actual(
        template,
        actual,
        required_vars,
        substitutions,
        conflicts,
        allow_never,
        SlotChoicePolarity::Upper,
        depth,
    );
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SlotChoicePolarity {
    Lower,
    Upper,
}

fn project_choice_var_items_against_closed_actual(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    allow_never: bool,
    polarity: SlotChoicePolarity,
    depth: usize,
) {
    if depth == 0 || !closed_slot_type_usable(actual, allow_never) {
        return;
    }
    match (polarity, template) {
        (SlotChoicePolarity::Lower, typed_ir::Type::Union(items)) => {
            for item in items {
                if let typed_ir::Type::Var(var) = item
                    && required_vars.contains(var)
                {
                    insert_projected_value_substitution(
                        substitutions,
                        conflicts,
                        var.clone(),
                        actual.clone(),
                    );
                    continue;
                }
                project_choice_var_items_against_closed_actual(
                    item,
                    actual,
                    required_vars,
                    substitutions,
                    conflicts,
                    allow_never,
                    polarity,
                    depth - 1,
                );
            }
        }
        (SlotChoicePolarity::Lower, typed_ir::Type::Inter(items))
        | (SlotChoicePolarity::Upper, typed_ir::Type::Union(items))
        | (SlotChoicePolarity::Upper, typed_ir::Type::Inter(items)) => {
            for item in items {
                project_choice_var_items_against_closed_actual(
                    item,
                    actual,
                    required_vars,
                    substitutions,
                    conflicts,
                    allow_never,
                    polarity,
                    depth - 1,
                );
            }
        }
        (_, typed_ir::Type::Recursive { body, .. }) => {
            project_choice_var_items_against_closed_actual(
                body,
                actual,
                required_vars,
                substitutions,
                conflicts,
                allow_never,
                polarity,
                depth - 1,
            );
        }
        _ => {}
    }
}

fn choose_precise_closed_type(
    candidates: impl IntoIterator<Item = Option<typed_ir::Type>>,
) -> Option<typed_ir::Type> {
    let mut fallback = None;
    for candidate in candidates.into_iter().flatten() {
        if matches!(candidate, typed_ir::Type::Unknown | typed_ir::Type::Any) {
            fallback.get_or_insert(candidate);
        } else {
            return Some(candidate);
        }
    }
    fallback
}

fn substituted_closed_type_from_bounds(
    bounds: &typed_ir::TypeBounds,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<typed_ir::Type> {
    let bounds = substitute_bounds(bounds.clone(), substitutions);
    closed_type_from_bounds(Some(&bounds))
}

pub(super) fn closed_type_from_bounds(
    bounds: Option<&typed_ir::TypeBounds>,
) -> Option<typed_ir::Type> {
    let bounds = bounds?;
    let lower = bounds
        .lower
        .as_deref()
        .cloned()
        .map(collapse_repeated_top_choice_type);
    let upper = bounds
        .upper
        .as_deref()
        .cloned()
        .map(collapse_repeated_top_choice_type);
    let choice = match (lower, upper) {
        (Some(lower), Some(upper)) if lower == upper => lower,
        (Some(ty), None) | (None, Some(ty)) => ty,
        _ => return None,
    };
    closed_slot_type_usable(&choice, false).then_some(choice)
}

fn refresh_lambda_body_local_types(
    ty: RuntimeType,
    param: typed_ir::Name,
    param_effect_annotation: Option<typed_ir::ParamEffectAnnotation>,
    param_function_allowed_effects: Option<typed_ir::FunctionSigAllowedEffects>,
    body: Expr,
) -> Expr {
    let expected_body_ty = match &ty {
        RuntimeType::Fun { ret, .. } => Some(ret.as_ref().clone()),
        _ => None,
    };
    let body = match &ty {
        RuntimeType::Fun { ret, .. } => retag_runtime_expr_spine_type(body, ret.as_ref().clone()),
        _ => body,
    };
    let refreshed = refresh_local_expr_types(Expr {
        ty,
        kind: ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(body),
        },
    });
    let ExprKind::Lambda { body, .. } = refreshed.kind else {
        return refreshed;
    };
    match expected_body_ty {
        Some(ty) => retag_runtime_expr_spine_type(*body, ty),
        None => *body,
    }
}

pub(super) fn closed_slot_type_usable(ty: &typed_ir::Type, allow_never: bool) -> bool {
    if matches!(ty, typed_ir::Type::Unknown) || (!allow_never && core_type_contains_unknown(ty)) {
        return false;
    }
    if core_type_has_vars(ty) {
        return false;
    }
    allow_never || !matches!(ty, typed_ir::Type::Never)
}

fn principal_unify_role_impls(module: &Module) -> HashMap<typed_ir::Name, Vec<Binding>> {
    let mut out: HashMap<typed_ir::Name, Vec<Binding>> = HashMap::new();
    let bindings_by_path = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let mut inserted = HashSet::new();
    for binding in &module.bindings {
        if !is_impl_method_path(&binding.name) {
            continue;
        }
        let Some(method) = binding.name.segments.last() else {
            continue;
        };
        inserted.insert(binding.name.clone());
        out.entry(method.clone()).or_default().push(binding.clone());
    }
    for role_impl in &module.role_impls {
        for member in &role_impl.members {
            if !inserted.insert(member.value.clone()) {
                continue;
            }
            let Some(binding) = bindings_by_path.get(&member.value) else {
                continue;
            };
            out.entry(member.name.clone())
                .or_default()
                .push((*binding).clone());
        }
    }
    for candidates in out.values_mut() {
        candidates.sort_by_key(|candidate| canonical_path(&candidate.name));
    }
    out
}

fn is_impl_method_path(path: &typed_ir::Path) -> bool {
    path.segments
        .iter()
        .any(|segment| segment.0.starts_with("&impl#"))
}

fn role_impl_closed_substitutions(
    binding: &Binding,
    spine: &PrincipalUnifyApplySpine<'_>,
    result_ty: &RuntimeType,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) -> Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
    let required_vars = binding_required_vars(binding);
    let Some((params, ret, ret_effect)) =
        core_fun_spine_parts_exact(&binding.scheme.body, spine.args.len())
    else {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "non-function-role-impl",
            &BTreeMap::new(),
            &missing_required_vars(binding, &BTreeMap::new()),
        );
        return None;
    };
    let (receiver_param, _) = params.first()?;
    let Some(first_arg) = spine.args.first() else {
        return None;
    };
    let first_evidence = spine.evidences.first().copied().flatten();
    let (_actual_ret, actual_ret_effect) = runtime_value_and_effect(result_ty);
    let actual_ret_effect = ambient_substitutions
        .map(|substitutions| substitute_type(&actual_ret_effect, substitutions))
        .unwrap_or(actual_ret_effect);
    let mut receiver_types =
        role_impl_arg_projection_types(first_arg, first_evidence, ambient_substitutions);
    push_never_value_effect_receiver_types(&mut receiver_types, result_ty, ambient_substitutions);
    let receiver_ty = receiver_types
        .iter()
        .find(|ty| closed_slot_type_usable(ty, false))
        .cloned()
        .unwrap_or_else(|| {
            ambient_substitutions
                .map(|substitutions| {
                    substitute_type(&runtime_core_type(&first_arg.ty), substitutions)
                })
                .unwrap_or_else(|| runtime_core_type(&first_arg.ty))
        });
    if matches!(receiver_ty, typed_ir::Type::Unknown | typed_ir::Type::Any)
        && !role_spine_has_local_imprecise_receiver(spine)
    {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "imprecise-receiver",
            &BTreeMap::new(),
            &missing_required_vars(binding, &BTreeMap::new()),
        );
        return None;
    }
    let mut substitutions = BTreeMap::new();
    let mut conflicts = BTreeSet::new();
    for (index, (arg, (param, _param_effect))) in spine.args.iter().zip(&params).enumerate() {
        let evidence = spine.evidences.get(index).copied().flatten();
        for actual in role_impl_arg_projection_types(arg, evidence, ambient_substitutions) {
            project_closed_value_substitutions_from_type(
                param,
                &actual,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                64,
            );
        }
        let protected_value_vars = substitutions.keys().cloned().collect::<BTreeSet<_>>();
        for actual in
            role_impl_arg_projection_types_for_substitution(arg, evidence, ambient_substitutions)
        {
            project_closed_substitutions_from_type(
                param,
                &actual,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
        }
        conflicts.retain(|var| !protected_value_vars.contains(var));
    }
    for actual_ret in role_impl_result_projection_types(spine, result_ty, ambient_substitutions) {
        project_closed_value_substitutions_from_type(
            &ret,
            &actual_ret,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            64,
        );
    }
    project_closed_substitutions_from_type(
        &ret_effect,
        &actual_ret_effect,
        &required_vars,
        &mut substitutions,
        &mut conflicts,
        true,
        64,
    );
    let effect_only_vars = binding_effect_only_vars(binding);
    if conflicts.iter().any(|var| !effect_only_vars.contains(var)) {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "conflict",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
        return None;
    } else if !conflicts.is_empty() {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "effect-conflict-kept",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
    }
    let receiver_is_imprecise = !closed_slot_type_usable(&receiver_ty, false);
    let substituted_receiver = substitute_type(receiver_param, &substitutions);
    let receiver_ty = if receiver_is_imprecise {
        substituted_receiver.clone()
    } else {
        receiver_types
            .iter()
            .filter(|candidate| closed_slot_type_usable(candidate, false))
            .find(|candidate| receiver_type_matches_impl(&substituted_receiver, candidate))
            .cloned()
            .unwrap_or(receiver_ty)
    };
    if receiver_is_imprecise
        && (!role_spine_has_local_imprecise_receiver(spine)
            || !role_impl_has_non_receiver_slot_support(
                &params,
                spine,
                &substitutions,
                ambient_substitutions,
            ))
    {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "imprecise-receiver",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
        return None;
    }
    if !closed_slot_type_usable(&receiver_ty, false) {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "imprecise-receiver",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
        return None;
    }
    if !receiver_type_matches_impl(&substituted_receiver, &receiver_ty) {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "receiver-mismatch",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
        return None;
    }
    if !role_impl_closed_slots_match(
        &params,
        &ret,
        spine,
        result_ty,
        &substitutions,
        ambient_substitutions,
    ) {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "slot-mismatch",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
        return None;
    }
    let completed = complete_required_role_substitutions(binding, &substitutions);
    if completed.is_none() {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "incomplete-substitution",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
    }
    completed
}

fn role_spine_has_local_imprecise_receiver(spine: &PrincipalUnifyApplySpine<'_>) -> bool {
    let Some(first_arg) = spine.args.first() else {
        return false;
    };
    let ExprKind::Var(path) = &first_arg.kind else {
        return false;
    };
    if path.segments.len() != 1 {
        return false;
    }
    let ty = runtime_core_type(&first_arg.ty);
    matches!(
        ty,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_)
    )
}

fn role_impl_has_non_receiver_slot_support(
    params: &[(typed_ir::Type, typed_ir::Type)],
    spine: &PrincipalUnifyApplySpine<'_>,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) -> bool {
    spine.args.iter().zip(params).enumerate().skip(1).any(
        |(index, (arg, (param, _param_effect)))| {
            let evidence = spine.evidences.get(index).copied().flatten();
            let param = substitute_type(param, substitutions);
            role_impl_arg_projection_types(arg, evidence, ambient_substitutions)
                .into_iter()
                .filter(|actual| closed_slot_type_usable(actual, false))
                .any(|actual| type_compatible(&param, &actual))
        },
    )
}

fn role_impl_receiver_dispatch_substitutions(
    binding: &Binding,
    spine: &PrincipalUnifyApplySpine<'_>,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) -> Option<BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
    let required_vars = binding_required_vars(binding);
    let Some((params, _ret, _ret_effect)) =
        core_fun_spine_parts_exact(&binding.scheme.body, spine.args.len())
    else {
        return None;
    };
    let (receiver_param, _) = params.first()?;
    let first_arg = spine.args.first()?;
    let first_evidence = spine.evidences.first().copied().flatten();
    let receiver_types =
        role_impl_arg_projection_types(first_arg, first_evidence, ambient_substitutions);
    let mut substitutions = BTreeMap::new();
    let mut conflicts = BTreeSet::new();
    for receiver_ty in &receiver_types {
        project_closed_value_substitutions_from_type(
            receiver_param,
            receiver_ty,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            64,
        );
    }
    if !conflicts.is_empty() {
        return None;
    }
    let substituted_receiver = substitute_type(receiver_param, &substitutions);
    let receiver_matches = receiver_types
        .iter()
        .filter(|receiver_ty| !matches!(receiver_ty, typed_ir::Type::Unknown | typed_ir::Type::Any))
        .any(|receiver_ty| receiver_type_matches_impl(&substituted_receiver, receiver_ty));
    if !receiver_matches {
        return None;
    }
    complete_required_role_substitutions(binding, &substitutions)
}

fn role_impl_closed_slots_match(
    params: &[(typed_ir::Type, typed_ir::Type)],
    ret: &typed_ir::Type,
    spine: &PrincipalUnifyApplySpine<'_>,
    result_ty: &RuntimeType,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) -> bool {
    for (index, (arg, (param, _param_effect))) in spine.args.iter().zip(params).enumerate() {
        let evidence = spine.evidences.get(index).copied().flatten();
        let mut actuals = role_impl_arg_projection_types(arg, evidence, ambient_substitutions);
        if index == 0 {
            push_never_value_effect_receiver_types(&mut actuals, result_ty, ambient_substitutions);
        }
        if actuals
            .iter()
            .all(|actual| matches!(actual, typed_ir::Type::Unknown | typed_ir::Type::Any))
        {
            continue;
        }
        let param = substitute_type(param, substitutions);
        if index == 0 {
            let precise_actuals = actuals
                .iter()
                .filter(|actual| closed_slot_type_usable(actual, false))
                .collect::<Vec<_>>();
            if precise_actuals.is_empty() {
                continue;
            }
            if !precise_actuals
                .iter()
                .any(|actual| receiver_type_matches_impl(&param, actual))
            {
                return false;
            }
        } else if actuals
            .iter()
            .filter(|actual| !matches!(actual, typed_ir::Type::Unknown | typed_ir::Type::Any))
            .any(|actual| !type_compatible(&param, actual))
        {
            return false;
        }
    }
    let actual_rets = role_impl_result_projection_types(spine, result_ty, ambient_substitutions);
    if actual_rets
        .iter()
        .all(|actual_ret| matches!(actual_ret, typed_ir::Type::Unknown | typed_ir::Type::Any))
    {
        return true;
    }
    let ret = substitute_type(ret, substitutions);
    actual_rets
        .iter()
        .filter(|actual_ret| !matches!(actual_ret, typed_ir::Type::Unknown | typed_ir::Type::Any))
        .all(|actual_ret| type_compatible(&ret, actual_ret))
}

fn role_impl_match_score(
    binding: &Binding,
    spine: &PrincipalUnifyApplySpine<'_>,
    result_ty: &RuntimeType,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) -> usize {
    let Some((params, ret, _ret_effect)) =
        core_fun_spine_parts_exact(&binding.scheme.body, spine.args.len())
    else {
        return 0;
    };
    let mut score = 0;
    for (index, (arg, (param, _param_effect))) in spine.args.iter().zip(params).enumerate() {
        let evidence = spine.evidences.get(index).copied().flatten();
        let param = substitute_type(&param, substitutions);
        score += role_impl_arg_projection_types(arg, evidence, ambient_substitutions)
            .iter()
            .filter(|actual| !matches!(actual, typed_ir::Type::Unknown | typed_ir::Type::Any))
            .map(|actual| role_impl_slot_score(&param, actual))
            .max()
            .unwrap_or(0);
    }
    let ret = substitute_type(&ret, substitutions);
    score += role_impl_result_projection_types(spine, result_ty, ambient_substitutions)
        .iter()
        .filter(|actual_ret| !matches!(actual_ret, typed_ir::Type::Unknown | typed_ir::Type::Any))
        .map(|actual_ret| role_impl_slot_score(&ret, actual_ret))
        .max()
        .unwrap_or(0);
    score
}

fn role_impl_arg_projection_types(
    arg: &Expr,
    evidence: Option<&typed_ir::ApplyEvidence>,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) -> Vec<typed_ir::Type> {
    let mut out = Vec::new();
    push_role_impl_expr_projection_types(&mut out, arg, ambient_substitutions);
    if let Some(evidence) = evidence {
        push_role_impl_bounds_projection_type(&mut out, &evidence.arg, ambient_substitutions);
        if let Some(expected_arg) = &evidence.expected_arg {
            push_role_impl_bounds_projection_type(&mut out, expected_arg, ambient_substitutions);
        }
    }
    out
}

fn role_impl_arg_projection_types_for_substitution(
    arg: &Expr,
    evidence: Option<&typed_ir::ApplyEvidence>,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) -> Vec<typed_ir::Type> {
    let mut out = Vec::new();
    push_role_impl_expr_projection_types_for_substitution(&mut out, arg, ambient_substitutions);
    if let Some(evidence) = evidence {
        push_role_impl_bounds_projection_type_for_substitution(
            &mut out,
            &evidence.arg,
            ambient_substitutions,
        );
        if let Some(expected_arg) = &evidence.expected_arg {
            push_role_impl_bounds_projection_type_for_substitution(
                &mut out,
                expected_arg,
                ambient_substitutions,
            );
        }
    }
    out
}

fn push_role_impl_expr_projection_types(
    out: &mut Vec<typed_ir::Type>,
    expr: &Expr,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) {
    let (actual, _effect) = runtime_value_and_effect(&expr.ty);
    push_role_impl_projection_type(out, actual, ambient_substitutions);
    match &expr.kind {
        ExprKind::BindHere { expr } => {
            if let RuntimeType::Thunk { value, .. } = &expr.ty {
                push_role_impl_projection_type(
                    out,
                    runtime_core_type(value),
                    ambient_substitutions,
                );
            }
            push_role_impl_expr_projection_types(out, expr, ambient_substitutions);
        }
        ExprKind::Coerce { expr, to, .. } => {
            push_role_impl_projection_type(out, to.clone(), ambient_substitutions);
            push_role_impl_expr_projection_types(out, expr, ambient_substitutions);
        }
        _ => {}
    }
}

fn push_role_impl_expr_projection_types_for_substitution(
    out: &mut Vec<typed_ir::Type>,
    expr: &Expr,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) {
    let (actual, _effect) = runtime_value_and_effect(&expr.ty);
    push_role_impl_projection_type_for_substitution(out, actual, ambient_substitutions);
    match &expr.kind {
        ExprKind::BindHere { expr } => {
            if let RuntimeType::Thunk { value, .. } = &expr.ty {
                push_role_impl_projection_type_for_substitution(
                    out,
                    runtime_core_type(value),
                    ambient_substitutions,
                );
            }
            push_role_impl_expr_projection_types_for_substitution(out, expr, ambient_substitutions);
        }
        ExprKind::Coerce { expr, to, .. } => {
            push_role_impl_projection_type_for_substitution(out, to.clone(), ambient_substitutions);
            push_role_impl_expr_projection_types_for_substitution(out, expr, ambient_substitutions);
        }
        _ => {}
    }
}

fn push_role_impl_effect_projection_types(
    out: &mut Vec<typed_ir::Type>,
    effect: &typed_ir::Type,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) {
    for ty in role_impl_effect_projection_types(effect) {
        push_role_impl_projection_type(out, ty, ambient_substitutions);
    }
}

fn role_impl_effect_projection_types(effect: &typed_ir::Type) -> Vec<typed_ir::Type> {
    let mut out = Vec::new();
    collect_role_impl_effect_projection_types(effect, &mut out);
    out
}

fn push_never_value_effect_receiver_types(
    out: &mut Vec<typed_ir::Type>,
    result_ty: &RuntimeType,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) {
    if out.iter().any(|ty| closed_slot_type_usable(ty, false)) {
        return;
    }
    let (actual_ret, actual_ret_effect) = runtime_value_and_effect(result_ty);
    let actual_ret = ambient_substitutions
        .map(|substitutions| substitute_type(&actual_ret, substitutions))
        .unwrap_or(actual_ret);
    if !matches!(actual_ret, typed_ir::Type::Never) {
        return;
    }
    push_role_impl_effect_projection_types(out, &actual_ret_effect, ambient_substitutions);
}

fn collect_role_impl_effect_projection_types(
    effect: &typed_ir::Type,
    out: &mut Vec<typed_ir::Type>,
) {
    match effect {
        typed_ir::Type::Named { .. } => {
            if !out.iter().any(|existing| existing == effect) {
                out.push(effect.clone());
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_role_impl_effect_projection_types(item, out);
            }
            collect_role_impl_effect_projection_types(tail, out);
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_role_impl_effect_projection_types(item, out);
            }
        }
        typed_ir::Type::Recursive { body, .. } => {
            collect_role_impl_effect_projection_types(body, out);
        }
        typed_ir::Type::Unknown
        | typed_ir::Type::Var(_)
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Fun { .. }
        | typed_ir::Type::Tuple(_)
        | typed_ir::Type::Record { .. }
        | typed_ir::Type::Variant(_) => {}
    }
}

fn role_impl_result_projection_types(
    spine: &PrincipalUnifyApplySpine<'_>,
    result_ty: &RuntimeType,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) -> Vec<typed_ir::Type> {
    let (actual, _effect) = runtime_value_and_effect(result_ty);
    let mut out = Vec::new();
    push_role_impl_projection_type(&mut out, actual, ambient_substitutions);
    if let Some(evidence) = spine.evidences.last().copied().flatten() {
        push_role_impl_bounds_projection_type(&mut out, &evidence.result, ambient_substitutions);
    }
    out
}

fn push_role_impl_bounds_projection_type(
    out: &mut Vec<typed_ir::Type>,
    bounds: &typed_ir::TypeBounds,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) {
    if let Some(ty) = closed_type_from_bounds(Some(bounds)) {
        push_role_impl_projection_type(out, ty, ambient_substitutions);
        return;
    }
    if let Some(substitutions) = ambient_substitutions {
        let bounds = substitute_bounds(bounds.clone(), substitutions);
        if let Some(ty) = closed_type_from_bounds(Some(&bounds)) {
            push_role_impl_projection_type(out, ty, None);
        }
    }
}

fn push_role_impl_bounds_projection_type_for_substitution(
    out: &mut Vec<typed_ir::Type>,
    bounds: &typed_ir::TypeBounds,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) {
    let bounds = ambient_substitutions
        .map(|substitutions| substitute_bounds(bounds.clone(), substitutions))
        .unwrap_or_else(|| bounds.clone());
    if let Some(lower) = bounds.lower.as_deref() {
        push_role_impl_projection_type_for_substitution(out, lower.clone(), None);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        push_role_impl_projection_type_for_substitution(out, upper.clone(), None);
    }
}

fn push_role_impl_projection_type(
    out: &mut Vec<typed_ir::Type>,
    ty: typed_ir::Type,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) {
    let ty = ambient_substitutions
        .map(|substitutions| substitute_type(&ty, substitutions))
        .unwrap_or(ty);
    if !closed_slot_type_usable(&ty, false) {
        return;
    }
    if !out.iter().any(|existing| existing == &ty) {
        out.push(ty);
    }
}

fn push_role_impl_projection_type_for_substitution(
    out: &mut Vec<typed_ir::Type>,
    ty: typed_ir::Type,
    ambient_substitutions: Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) {
    let ty = ambient_substitutions
        .map(|substitutions| substitute_type(&ty, substitutions))
        .unwrap_or(ty);
    if matches!(ty, typed_ir::Type::Unknown | typed_ir::Type::Any) {
        return;
    }
    if !out.iter().any(|existing| existing == &ty) {
        out.push(ty);
    }
}

fn role_impl_slot_score(expected: &typed_ir::Type, actual: &typed_ir::Type) -> usize {
    if expected == actual {
        return 4;
    }
    if receiver_type_matches_impl(expected, actual) {
        return 3;
    }
    if type_compatible(expected, actual) {
        return 1;
    }
    0
}

fn project_closed_value_substitutions_from_type(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    match (template, actual) {
        (typed_ir::Type::Var(var), actual) if params.contains(var) => {
            let actual = normalize_projected_value_substitution_type(actual, substitutions);
            if closed_slot_type_usable(&actual, false) {
                insert_projected_value_substitution(substitutions, conflicts, var.clone(), actual);
            }
        }
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                project_closed_value_substitutions_from_type_arg(
                    template_arg,
                    actual_arg,
                    params,
                    substitutions,
                    conflicts,
                    depth - 1,
                );
            }
        }
        (
            typed_ir::Type::Fun {
                param,
                ret_effect,
                ret,
                ..
            },
            typed_ir::Type::Fun {
                param: actual_param,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
                ..
            },
        ) => {
            project_closed_value_substitutions_from_type(
                param,
                actual_param,
                params,
                substitutions,
                conflicts,
                depth - 1,
            );
            project_closed_substitutions_from_type(
                ret_effect,
                actual_ret_effect,
                params,
                substitutions,
                conflicts,
                true,
                depth - 1,
            );
            project_closed_value_substitutions_from_type(
                ret,
                actual_ret,
                params,
                substitutions,
                conflicts,
                depth - 1,
            );
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (item, actual_item) in items.iter().zip(actual_items) {
                project_closed_value_substitutions_from_type(
                    item,
                    actual_item,
                    params,
                    substitutions,
                    conflicts,
                    depth - 1,
                );
            }
        }
        (typed_ir::Type::Variant(variant), typed_ir::Type::Variant(actual_variant)) => {
            for case in &variant.cases {
                let Some(actual_case) = actual_variant.cases.iter().find(|actual_case| {
                    actual_case.name == case.name
                        && actual_case.payloads.len() == case.payloads.len()
                }) else {
                    continue;
                };
                for (payload, actual_payload) in case.payloads.iter().zip(&actual_case.payloads) {
                    project_closed_value_substitutions_from_type(
                        payload,
                        actual_payload,
                        params,
                        substitutions,
                        conflicts,
                        depth - 1,
                    );
                }
            }
        }
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual)
            if closed_slot_type_usable(
                &normalize_projected_value_substitution_type(actual, substitutions),
                false,
            ) =>
        {
            let actual = normalize_projected_value_substitution_type(actual, substitutions);
            for item in items {
                project_closed_value_substitutions_from_type(
                    item,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    depth - 1,
                );
            }
        }
        _ => {}
    }
}

fn project_contextual_input_value_substitutions_from_type(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    match (template, actual) {
        (typed_ir::Type::Var(var), actual) if params.contains(var) => {
            let actual = normalize_projected_value_substitution_type(actual, substitutions);
            if closed_slot_type_usable(&actual, false) {
                insert_runtime_arg_value_substitution(
                    substitutions,
                    conflicts,
                    var.clone(),
                    actual,
                );
            }
        }
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                project_contextual_input_value_substitutions_from_type_arg(
                    template_arg,
                    actual_arg,
                    params,
                    substitutions,
                    conflicts,
                    depth - 1,
                );
            }
        }
        (
            typed_ir::Type::Fun {
                param,
                ret_effect,
                ret,
                ..
            },
            typed_ir::Type::Fun {
                param: actual_param,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
                ..
            },
        ) => {
            project_contextual_input_value_substitutions_from_type(
                param,
                actual_param,
                params,
                substitutions,
                conflicts,
                depth - 1,
            );
            project_closed_substitutions_from_type(
                ret_effect,
                actual_ret_effect,
                params,
                substitutions,
                conflicts,
                true,
                depth - 1,
            );
            project_contextual_input_value_substitutions_from_type(
                ret,
                actual_ret,
                params,
                substitutions,
                conflicts,
                depth - 1,
            );
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (item, actual_item) in items.iter().zip(actual_items) {
                project_contextual_input_value_substitutions_from_type(
                    item,
                    actual_item,
                    params,
                    substitutions,
                    conflicts,
                    depth - 1,
                );
            }
        }
        (typed_ir::Type::Variant(variant), typed_ir::Type::Variant(actual_variant)) => {
            for case in &variant.cases {
                let Some(actual_case) = actual_variant.cases.iter().find(|actual_case| {
                    actual_case.name == case.name
                        && actual_case.payloads.len() == case.payloads.len()
                }) else {
                    continue;
                };
                for (payload, actual_payload) in case.payloads.iter().zip(&actual_case.payloads) {
                    project_contextual_input_value_substitutions_from_type(
                        payload,
                        actual_payload,
                        params,
                        substitutions,
                        conflicts,
                        depth - 1,
                    );
                }
            }
        }
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual)
            if closed_slot_type_usable(
                &normalize_projected_value_substitution_type(actual, substitutions),
                false,
            ) =>
        {
            let actual = normalize_projected_value_substitution_type(actual, substitutions);
            for item in items {
                project_contextual_input_value_substitutions_from_type(
                    item,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    depth - 1,
                );
            }
        }
        _ => {}
    }
}

fn project_closed_value_substitutions_from_type_arg(
    template: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    depth: usize,
) {
    match (template, actual) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
            project_closed_value_substitutions_from_type(
                template,
                actual,
                params,
                substitutions,
                conflicts,
                depth,
            );
        }
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Bounds(actual)) => {
            let actual_bounds = substitute_bounds(actual.clone(), substitutions);
            if let Some(actual) = closed_type_from_bounds(Some(&actual_bounds)) {
                project_closed_value_substitutions_from_type(
                    template,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    depth,
                );
            }
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Type(actual)) => {
            let actual = normalize_projected_value_substitution_type(actual, substitutions);
            if !closed_slot_type_usable(&actual, false) {
                return;
            }
            project_closed_value_substitutions_from_bounds(
                template,
                &actual,
                params,
                substitutions,
                conflicts,
                depth,
            );
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
            let actual_bounds = substitute_bounds(actual.clone(), substitutions);
            if let Some(actual) = closed_type_from_bounds(Some(&actual_bounds)) {
                project_closed_value_substitutions_from_bounds(
                    template,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    depth,
                );
            }
        }
    }
}

fn project_contextual_input_value_substitutions_from_type_arg(
    template: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    depth: usize,
) {
    match (template, actual) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
            project_contextual_input_value_substitutions_from_type(
                template,
                actual,
                params,
                substitutions,
                conflicts,
                depth,
            );
        }
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Bounds(actual)) => {
            let actual_bounds = substitute_bounds(actual.clone(), substitutions);
            if let Some(actual) = closed_type_from_bounds(Some(&actual_bounds)) {
                project_contextual_input_value_substitutions_from_type(
                    template,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    depth,
                );
            }
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Type(actual)) => {
            let actual = normalize_projected_value_substitution_type(actual, substitutions);
            if !closed_slot_type_usable(&actual, false) {
                return;
            }
            project_contextual_input_value_substitutions_from_bounds(
                template,
                &actual,
                params,
                substitutions,
                conflicts,
                depth,
            );
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
            let actual_bounds = substitute_bounds(actual.clone(), substitutions);
            if let Some(actual) = closed_type_from_bounds(Some(&actual_bounds)) {
                project_contextual_input_value_substitutions_from_bounds(
                    template,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    depth,
                );
            }
        }
    }
}

fn project_closed_value_substitutions_from_bounds(
    template: &typed_ir::TypeBounds,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    depth: usize,
) {
    if !closed_slot_type_usable(actual, false) {
        return;
    }

    if let Some(lower) = template.lower.as_deref() {
        project_closed_value_substitutions_from_type(
            lower,
            actual,
            params,
            substitutions,
            conflicts,
            depth,
        );
    }
    if let Some(upper) = template.upper.as_deref() {
        project_closed_value_substitutions_from_type(
            upper,
            actual,
            params,
            substitutions,
            conflicts,
            depth,
        );
    }
}

fn project_contextual_input_value_substitutions_from_bounds(
    template: &typed_ir::TypeBounds,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    depth: usize,
) {
    if !closed_slot_type_usable(actual, false) {
        return;
    }

    if let Some(lower) = template.lower.as_deref() {
        project_contextual_input_value_substitutions_from_type(
            lower,
            actual,
            params,
            substitutions,
            conflicts,
            depth,
        );
    }
    if let Some(upper) = template.upper.as_deref() {
        project_contextual_input_value_substitutions_from_type(
            upper,
            actual,
            params,
            substitutions,
            conflicts,
            depth,
        );
    }
}

fn insert_projected_value_substitution(
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    var: typed_ir::TypeVar,
    ty: typed_ir::Type,
) {
    let ty = normalize_projected_value_shape(ty);
    if let Some(existing) = substitutions.get(&var) {
        let existing = normalize_projected_value_shape(existing.clone());
        if let Some(merged) = merge_projected_value_type_precision(&existing, &ty) {
            substitutions.insert(var, merged);
        } else if existing != ty {
            conflicts.insert(var);
        }
    } else {
        substitutions.insert(var, ty);
    }
}

pub(super) fn merge_projected_value_type_precision(
    existing: &typed_ir::Type,
    incoming: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if existing == incoming {
        return Some(existing.clone());
    }
    match (existing, incoming) {
        (existing, typed_ir::Type::Union(incoming_items))
            if incoming_items
                .iter()
                .any(|item| merge_projected_value_type_precision(existing, item).is_some()) =>
        {
            return Some(incoming.clone());
        }
        (typed_ir::Type::Union(existing_items), incoming)
            if existing_items
                .iter()
                .any(|item| merge_projected_value_type_precision(item, incoming).is_some()) =>
        {
            return Some(existing.clone());
        }
        (typed_ir::Type::Unknown, incoming) => Some(incoming.clone()),
        (existing, typed_ir::Type::Unknown) => Some(existing.clone()),
        (typed_ir::Type::Any, incoming) => Some(incoming.clone()),
        (existing, typed_ir::Type::Any) => Some(existing.clone()),
        (
            typed_ir::Type::Named {
                path: existing_path,
                args: existing_args,
            },
            typed_ir::Type::Named {
                path: incoming_path,
                args: incoming_args,
            },
        ) if existing_path == incoming_path && existing_args.len() == incoming_args.len() => {
            let args = existing_args
                .iter()
                .zip(incoming_args)
                .map(|(existing, incoming)| merge_projected_type_arg_precision(existing, incoming))
                .collect::<Option<Vec<_>>>()?;
            Some(typed_ir::Type::Named {
                path: existing_path.clone(),
                args,
            })
        }
        (typed_ir::Type::Tuple(existing_items), typed_ir::Type::Tuple(incoming_items))
            if existing_items.len() == incoming_items.len() =>
        {
            let items = existing_items
                .iter()
                .zip(incoming_items)
                .map(|(existing, incoming)| {
                    merge_projected_value_type_precision(existing, incoming)
                })
                .collect::<Option<Vec<_>>>()?;
            Some(typed_ir::Type::Tuple(items))
        }
        (
            typed_ir::Type::Row {
                items: existing_items,
                tail: existing_tail,
            },
            typed_ir::Type::Row {
                items: incoming_items,
                tail: incoming_tail,
            },
        ) if existing_items.len() == incoming_items.len() => {
            let items = existing_items
                .iter()
                .zip(incoming_items)
                .map(|(existing, incoming)| {
                    merge_projected_effect_type_precision(existing, incoming)
                })
                .collect::<Option<Vec<_>>>()?;
            Some(typed_ir::Type::Row {
                items,
                tail: Box::new(merge_projected_effect_type_precision(
                    existing_tail,
                    incoming_tail,
                )?),
            })
        }
        (typed_ir::Type::Row { .. }, typed_ir::Type::Row { .. }) => {
            Some(merge_effects(existing.clone(), incoming.clone()))
        }
        (
            typed_ir::Type::Fun {
                param: existing_param,
                param_effect: existing_param_effect,
                ret_effect: existing_ret_effect,
                ret: existing_ret,
            },
            typed_ir::Type::Fun {
                param: incoming_param,
                param_effect: incoming_param_effect,
                ret_effect: incoming_ret_effect,
                ret: incoming_ret,
            },
        ) => Some(typed_ir::Type::Fun {
            param: Box::new(merge_projected_value_type_precision(
                existing_param,
                incoming_param,
            )?),
            param_effect: Box::new(merge_projected_effect_type_precision(
                existing_param_effect,
                incoming_param_effect,
            )?),
            ret_effect: Box::new(merge_projected_effect_type_precision(
                existing_ret_effect,
                incoming_ret_effect,
            )?),
            ret: Box::new(merge_projected_value_type_precision(
                existing_ret,
                incoming_ret,
            )?),
        }),
        _ => None,
    }
    .or_else(|| needs_runtime_coercion(incoming, existing).then(|| incoming.clone()))
    .or_else(|| needs_runtime_coercion(existing, incoming).then(|| existing.clone()))
}

fn merge_projected_effect_type_precision(
    existing: &typed_ir::Type,
    incoming: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    match (existing, incoming) {
        (typed_ir::Type::Never, incoming) => Some(incoming.clone()),
        (existing, typed_ir::Type::Never) => Some(existing.clone()),
        (
            typed_ir::Type::Named {
                path: existing_path,
                args: existing_args,
            },
            typed_ir::Type::Named {
                path: incoming_path,
                args: incoming_args,
            },
        ) if existing_path == incoming_path
            && existing_args.is_empty()
            && !incoming_args.is_empty() =>
        {
            Some(incoming.clone())
        }
        (
            typed_ir::Type::Named {
                path: existing_path,
                args: existing_args,
            },
            typed_ir::Type::Named {
                path: incoming_path,
                args: incoming_args,
            },
        ) if existing_path == incoming_path
            && !existing_args.is_empty()
            && incoming_args.is_empty() =>
        {
            Some(existing.clone())
        }
        _ => merge_projected_value_type_precision(existing, incoming),
    }
}

fn merge_projected_type_arg_precision(
    existing: &typed_ir::TypeArg,
    incoming: &typed_ir::TypeArg,
) -> Option<typed_ir::TypeArg> {
    match (existing, incoming) {
        (typed_ir::TypeArg::Type(existing), typed_ir::TypeArg::Type(incoming)) => Some(
            typed_ir::TypeArg::Type(merge_projected_value_type_precision(existing, incoming)?),
        ),
        (typed_ir::TypeArg::Bounds(existing), typed_ir::TypeArg::Bounds(incoming)) => Some(
            typed_ir::TypeArg::Bounds(merge_projected_bounds_precision(existing, incoming)?),
        ),
        (typed_ir::TypeArg::Bounds(existing), typed_ir::TypeArg::Type(incoming))
        | (typed_ir::TypeArg::Type(incoming), typed_ir::TypeArg::Bounds(existing)) => {
            let existing = normalize_projected_type_bounds(existing.clone());
            let existing = closed_type_from_bounds(Some(&existing))?;
            Some(typed_ir::TypeArg::Type(
                merge_projected_value_type_precision(&existing, incoming)?,
            ))
        }
    }
}

fn merge_projected_bounds_precision(
    existing: &typed_ir::TypeBounds,
    incoming: &typed_ir::TypeBounds,
) -> Option<typed_ir::TypeBounds> {
    let lower = match (existing.lower.as_deref(), incoming.lower.as_deref()) {
        (Some(existing), Some(incoming)) => Some(Box::new(merge_projected_value_type_precision(
            existing, incoming,
        )?)),
        (Some(existing), None) => Some(Box::new(existing.clone())),
        (None, Some(incoming)) => Some(Box::new(incoming.clone())),
        (None, None) => None,
    };
    let upper = match (existing.upper.as_deref(), incoming.upper.as_deref()) {
        (Some(existing), Some(incoming)) => Some(Box::new(merge_projected_value_type_precision(
            existing, incoming,
        )?)),
        (Some(existing), None) => Some(Box::new(existing.clone())),
        (None, Some(incoming)) => Some(Box::new(incoming.clone())),
        (None, None) => None,
    };
    Some(typed_ir::TypeBounds { lower, upper })
}

fn normalize_projected_value_shape(ty: typed_ir::Type) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path,
            args: args.into_iter().map(normalize_projected_type_arg).collect(),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .into_iter()
                .map(normalize_projected_value_shape)
                .collect(),
        ),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(normalize_projected_value_shape(*param)),
            param_effect,
            ret_effect,
            ret: Box::new(normalize_projected_value_shape(*ret)),
        },
        typed_ir::Type::Union(items) => {
            let items = drop_never_union_items(
                items
                    .into_iter()
                    .map(normalize_projected_value_shape)
                    .collect(),
            );
            collapse_repeated_top_choice_type(typed_ir::Type::Union(items))
        }
        typed_ir::Type::Inter(items) => collapse_repeated_top_choice_type(typed_ir::Type::Inter(
            items
                .into_iter()
                .map(normalize_projected_value_shape)
                .collect(),
        )),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var,
            body: Box::new(normalize_projected_value_shape(*body)),
        },
        other => other,
    }
}

fn normalize_projected_type_arg(arg: typed_ir::TypeArg) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(normalize_projected_value_shape(ty)),
        typed_ir::TypeArg::Bounds(bounds) => {
            let bounds = normalize_projected_type_bounds(bounds);
            if let Some(ty) = closed_type_from_bounds(Some(&bounds)) {
                typed_ir::TypeArg::Type(ty)
            } else {
                typed_ir::TypeArg::Bounds(bounds)
            }
        }
    }
}

fn normalize_projected_type_bounds(bounds: typed_ir::TypeBounds) -> typed_ir::TypeBounds {
    typed_ir::TypeBounds {
        lower: bounds
            .lower
            .map(|ty| Box::new(normalize_projected_value_shape(*ty))),
        upper: bounds
            .upper
            .map(|ty| Box::new(normalize_projected_value_shape(*ty))),
    }
}

fn normalize_projected_value_substitution_type(
    ty: &typed_ir::Type,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::Type {
    normalize_projected_value_shape(substitute_type(ty, substitutions))
}

fn drop_never_union_items(items: Vec<typed_ir::Type>) -> Vec<typed_ir::Type> {
    if items.len() <= 1 {
        return items;
    }
    let kept = items
        .iter()
        .filter(|item| !matches!(item, typed_ir::Type::Never))
        .cloned()
        .collect::<Vec<_>>();
    if kept.is_empty() { items } else { kept }
}

fn collapse_repeated_top_choice_type(ty: typed_ir::Type) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Union(items) => {
            collapse_repeated_top_choice_items(items, typed_ir::Type::Union)
        }
        typed_ir::Type::Inter(items) => {
            collapse_repeated_top_choice_items(items, typed_ir::Type::Inter)
        }
        other => other,
    }
}

fn collapse_repeated_top_choice_items(
    items: Vec<typed_ir::Type>,
    rebuild: impl FnOnce(Vec<typed_ir::Type>) -> typed_ir::Type,
) -> typed_ir::Type {
    let mut unique = Vec::<typed_ir::Type>::new();
    for item in items {
        if !unique.iter().any(|existing| existing == &item) {
            unique.push(item);
        }
    }
    if unique.len() == 1 {
        unique.pop().expect("single projected value choice item")
    } else {
        rebuild(unique)
    }
}

fn binding_effect_only_vars(binding: &Binding) -> BTreeSet<typed_ir::TypeVar> {
    let mut usage = BTreeMap::<typed_ir::TypeVar, (bool, bool)>::new();
    collect_type_var_effect_usage(&binding.scheme.body, false, &mut usage);
    binding_required_vars(binding)
        .into_iter()
        .filter(|var| {
            usage
                .get(var)
                .is_some_and(|(value, effect)| !*value && *effect)
        })
        .collect()
}

fn collect_type_var_effect_usage(
    ty: &typed_ir::Type,
    in_effect: bool,
    usage: &mut BTreeMap<typed_ir::TypeVar, (bool, bool)>,
) {
    match ty {
        typed_ir::Type::Var(var) => {
            let entry = usage.entry(var.clone()).or_default();
            if in_effect {
                entry.1 = true;
            } else {
                entry.0 = true;
            }
        }
        typed_ir::Type::Named { path, args } => {
            for (index, arg) in args.iter().enumerate() {
                let arg_in_effect = in_effect || (is_std_var_ref_path(path) && index == 0);
                collect_type_arg_effect_usage(arg, arg_in_effect, usage);
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_var_effect_usage(param, in_effect, usage);
            collect_type_var_effect_usage(param_effect, true, usage);
            collect_type_var_effect_usage(ret_effect, true, usage);
            collect_type_var_effect_usage(ret, in_effect, usage);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items)
        | typed_ir::Type::Row { items, .. } => {
            for item in items {
                collect_type_var_effect_usage(item, in_effect, usage);
            }
            if let typed_ir::Type::Row { tail, .. } = ty {
                collect_type_var_effect_usage(tail, in_effect, usage);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_type_var_effect_usage(&field.value, in_effect, usage);
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_var_effect_usage(payload, in_effect, usage);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_type_var_effect_usage(tail, in_effect, usage);
            }
        }
        typed_ir::Type::Recursive { body, .. } => {
            collect_type_var_effect_usage(body, in_effect, usage);
        }
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => {}
    }
}

fn is_std_var_ref_path(path: &typed_ir::Path) -> bool {
    let [std, var, ref_name] = path.segments.as_slice() else {
        return false;
    };
    std.0 == "std" && var.0 == "var" && ref_name.0 == "ref"
}

fn project_ref_effect_arg_vars_from_value_arg(
    ty: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    let typed_ir::Type::Named { path, args } = ty else {
        return;
    };
    if !is_std_var_ref_path(path) || args.len() < 2 {
        return;
    }
    let Some(value_arg) = closed_type_arg(&args[1], substitutions) else {
        return;
    };
    for var in ref_effect_arg_vars(&args[0]) {
        if required_vars.contains(&var) {
            insert_projected_value_substitution(substitutions, conflicts, var, value_arg.clone());
        }
    }
}

fn closed_type_arg(
    arg: &typed_ir::TypeArg,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<typed_ir::Type> {
    let ty = match arg {
        typed_ir::TypeArg::Type(ty) => substitute_type(ty, substitutions),
        typed_ir::TypeArg::Bounds(bounds) => {
            let bounds = substitute_bounds(bounds.clone(), substitutions);
            closed_type_from_bounds(Some(&bounds))?
        }
    };
    (!core_type_has_vars(&ty) && !core_type_contains_unknown(&ty)).then_some(ty)
}

fn ref_effect_arg_vars(arg: &typed_ir::TypeArg) -> Vec<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    match arg {
        typed_ir::TypeArg::Type(ty) => collect_ref_effect_arg_vars(ty, &mut vars),
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                collect_ref_effect_arg_vars(lower, &mut vars);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_ref_effect_arg_vars(upper, &mut vars);
            }
        }
    }
    vars.into_iter().collect()
}

fn collect_ref_effect_arg_vars(ty: &typed_ir::Type, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        typed_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                vars.extend(ref_effect_arg_vars(arg));
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_ref_effect_arg_vars(item, vars);
            }
            collect_ref_effect_arg_vars(tail, vars);
        }
        _ => {}
    }
}

fn collect_type_arg_effect_usage(
    arg: &typed_ir::TypeArg,
    in_effect: bool,
    usage: &mut BTreeMap<typed_ir::TypeVar, (bool, bool)>,
) {
    match arg {
        typed_ir::TypeArg::Type(ty) => collect_type_var_effect_usage(ty, in_effect, usage),
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                collect_type_var_effect_usage(lower, in_effect, usage);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_type_var_effect_usage(upper, in_effect, usage);
            }
        }
    }
}

fn receiver_type_matches_impl(
    impl_receiver: &typed_ir::Type,
    actual_receiver: &typed_ir::Type,
) -> bool {
    if type_is_effect_like(impl_receiver) || type_is_effect_like(actual_receiver) {
        return effect_compatible(impl_receiver, actual_receiver)
            && effect_compatible(actual_receiver, impl_receiver);
    }
    match (impl_receiver, actual_receiver) {
        (left, right) if left == right => true,
        (
            typed_ir::Type::Named {
                path: left_path,
                args: left_args,
            },
            typed_ir::Type::Named {
                path: right_path,
                args: right_args,
            },
        ) => {
            left_path == right_path
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| receiver_type_arg_matches_impl(left, right))
        }
        (typed_ir::Type::Tuple(left_items), typed_ir::Type::Tuple(right_items)) => {
            left_items.len() == right_items.len()
                && left_items
                    .iter()
                    .zip(right_items)
                    .all(|(left, right)| receiver_type_matches_impl(left, right))
        }
        (
            typed_ir::Type::Fun {
                param: left_param,
                param_effect: left_param_effect,
                ret_effect: left_ret_effect,
                ret: left_ret,
            },
            typed_ir::Type::Fun {
                param: right_param,
                param_effect: right_param_effect,
                ret_effect: right_ret_effect,
                ret: right_ret,
            },
        ) => {
            receiver_type_matches_impl(left_param, right_param)
                && receiver_type_matches_impl(left_param_effect, right_param_effect)
                && receiver_type_matches_impl(left_ret_effect, right_ret_effect)
                && receiver_type_matches_impl(left_ret, right_ret)
        }
        _ => false,
    }
}

fn receiver_type_arg_matches_impl(left: &typed_ir::TypeArg, right: &typed_ir::TypeArg) -> bool {
    if receiver_type_arg_is_effect_like(left) || receiver_type_arg_is_effect_like(right) {
        let Some(left) = receiver_type_arg_effect_type(left) else {
            return false;
        };
        let Some(right) = receiver_type_arg_effect_type(right) else {
            return false;
        };
        return effect_compatible(left, right) && effect_compatible(right, left);
    }
    match (left, right) {
        (typed_ir::TypeArg::Type(left), typed_ir::TypeArg::Type(right)) => {
            receiver_type_matches_impl(left, right)
        }
        (typed_ir::TypeArg::Type(left), typed_ir::TypeArg::Bounds(right))
        | (typed_ir::TypeArg::Bounds(right), typed_ir::TypeArg::Type(left)) => {
            receiver_bounds_contains_type(right, left)
        }
        (typed_ir::TypeArg::Bounds(left), typed_ir::TypeArg::Bounds(right)) => {
            receiver_bounds_match(left, right)
        }
    }
}

fn receiver_type_arg_is_effect_like(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_is_effect_like(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(type_is_effect_like)
                || bounds.upper.as_deref().is_some_and(type_is_effect_like)
        }
    }
}

fn receiver_type_arg_effect_type(arg: &typed_ir::TypeArg) -> Option<&typed_ir::Type> {
    match arg {
        typed_ir::TypeArg::Type(ty) if type_is_effect_like(ty) => Some(ty),
        typed_ir::TypeArg::Type(_) => None,
        typed_ir::TypeArg::Bounds(bounds) => bounds
            .lower
            .as_deref()
            .filter(|ty| type_is_effect_like(ty))
            .or_else(|| bounds.upper.as_deref().filter(|ty| type_is_effect_like(ty))),
    }
}

fn receiver_bounds_contains_type(bounds: &typed_ir::TypeBounds, ty: &typed_ir::Type) -> bool {
    bounds
        .lower
        .as_deref()
        .is_some_and(|lower| receiver_type_matches_impl(lower, ty))
        || bounds
            .upper
            .as_deref()
            .is_some_and(|upper| receiver_type_matches_impl(upper, ty))
}

fn receiver_bounds_match(left: &typed_ir::TypeBounds, right: &typed_ir::TypeBounds) -> bool {
    match (
        left.lower.as_deref(),
        left.upper.as_deref(),
        right.lower.as_deref(),
        right.upper.as_deref(),
    ) {
        (Some(left_lower), _, Some(right_lower), _) => {
            receiver_type_matches_impl(left_lower, right_lower)
        }
        (_, Some(left_upper), _, Some(right_upper)) => {
            receiver_type_matches_impl(left_upper, right_upper)
        }
        (Some(left_lower), _, _, Some(right_upper)) => {
            receiver_type_matches_impl(left_lower, right_upper)
        }
        (_, Some(left_upper), Some(right_lower), _) => {
            receiver_type_matches_impl(left_upper, right_lower)
        }
        _ => false,
    }
}

fn principal_unify_key(
    target: &typed_ir::Path,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    handler_plan: Option<&HandlerAdapterPlan>,
    input_shapes: Option<&[typed_ir::Type]>,
    output_shape: Option<&typed_ir::Type>,
) -> String {
    let mut key = canonical_path(target);
    for (var, ty) in substitutions {
        key.push('|');
        key.push_str(&var.0);
        key.push('=');
        canonical_type(ty, &mut key);
    }
    if let Some(input_shapes) = input_shapes {
        for shape in input_shapes {
            key.push_str("|input=");
            canonical_type(shape, &mut key);
        }
    }
    if let Some(output_shape) = output_shape {
        key.push_str("|output=");
        canonical_type(output_shape, &mut key);
    }
    if let Some(plan) = handler_plan {
        if let Some(effect) = &plan.residual_before {
            key.push_str("|handler-before=");
            canonical_type(effect, &mut key);
        }
        if let Some(effect) = &plan.residual_after {
            key.push_str("|handler-after=");
            canonical_type(effect, &mut key);
        }
        if let Some(effect) = &plan.return_wrapper_effect {
            key.push_str("|handler-return=");
            canonical_type(effect, &mut key);
        }
    }
    key
}

fn principal_unified_path(target: &typed_ir::Path, index: usize) -> typed_ir::Path {
    let mut path = target.clone();
    match path.segments.last_mut() {
        Some(name) => name.0 = format!("{}__mono{index}", name.0),
        None => path.segments.push(typed_ir::Name(format!("__mono{index}"))),
    }
    path
}

fn next_principal_unify_index(module: &Module) -> usize {
    module
        .bindings
        .iter()
        .filter_map(|binding| specialization_suffix(&binding.name))
        .max()
        .map(|index| index + 1)
        .unwrap_or(0)
}

fn empty_module() -> Module {
    Module {
        path: typed_ir::Path::default(),
        bindings: Vec::new(),
        root_exprs: Vec::new(),
        roots: Vec::new(),
        role_impls: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewrites_complete_principal_plan_without_runtime_inference() {
        let t = typed_ir::TypeVar("t".to_string());
        let int = named("int");
        let id_path = path(&["id"]);
        let id_scheme = typed_ir::Scheme {
            requirements: Vec::new(),
            body: fun(
                typed_ir::Type::Var(t.clone()),
                typed_ir::Type::Var(t.clone()),
            ),
        };
        let binding = Binding {
            name: id_path.clone(),
            type_params: vec![t.clone()],
            scheme: id_scheme.clone(),
            body: Expr::typed(
                ExprKind::Lambda {
                    param: name("x"),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Var(path(&["x"])),
                        RuntimeType::core(typed_ir::Type::Var(t.clone())),
                    )),
                },
                RuntimeType::core(id_scheme.body.clone()),
            ),
        };
        let evidence = typed_ir::ApplyEvidence {
            callee_source_edge: None,
            arg_source_edge: None,
            callee: typed_ir::TypeBounds::exact(id_scheme.body.clone()),
            expected_callee: None,
            arg: typed_ir::TypeBounds::exact(int.clone()),
            expected_arg: Some(typed_ir::TypeBounds::exact(int.clone())),
            result: typed_ir::TypeBounds::exact(int.clone()),
            principal_callee: Some(id_scheme.body.clone()),
            substitutions: vec![typed_ir::TypeSubstitution {
                var: t.clone(),
                ty: int.clone(),
            }],
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: Some(typed_ir::PrincipalElaborationPlan {
                target: Some(id_path.clone()),
                principal_callee: id_scheme.body.clone(),
                substitutions: vec![typed_ir::TypeSubstitution {
                    var: t.clone(),
                    ty: int.clone(),
                }],
                args: vec![typed_ir::PrincipalElaborationArg {
                    index: 0,
                    intrinsic: typed_ir::TypeBounds::exact(int.clone()),
                    contextual: Some(typed_ir::TypeBounds::exact(int.clone())),
                    expected_runtime: Some(int.clone()),
                    source_edge: None,
                }],
                result: typed_ir::PrincipalElaborationResult {
                    intrinsic: typed_ir::TypeBounds::exact(int.clone()),
                    contextual: Some(typed_ir::TypeBounds::exact(int.clone())),
                    expected_runtime: Some(int.clone()),
                },
                adapters: Vec::new(),
                complete: true,
                incomplete_reasons: Vec::new(),
            }),
        };
        let module = Module {
            path: path(&["test"]),
            bindings: vec![binding],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(id_path.clone()),
                        RuntimeType::core(id_scheme.body),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(int.clone()),
                    )),
                    evidence: Some(evidence),
                    instantiation: None,
                },
                RuntimeType::core(int),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let (module, profile) = principal_unify_module_profiled(module);

        assert!(
            profile
                .stats
                .get("principal-unify-rewrite")
                .is_some_and(|count| *count == 1)
        );
        assert!(
            module
                .bindings
                .iter()
                .any(|binding| canonical_path(&binding.name) == "id__mono0")
        );
        let ExprKind::Apply { callee, .. } = &module.root_exprs[0].kind else {
            panic!("root should stay an apply");
        };
        let ExprKind::Var(path) = &callee.kind else {
            panic!("callee should be rewritten to specialized binding");
        };
        assert_eq!(canonical_path(path), "id__mono0");
    }

    #[test]
    fn materializes_contextual_thunk_type_when_expression_does_not_return_thunk() {
        let bool_ty = named("bool");
        let unit_ty = named("unit");
        let effect = named("std::junction::junction");
        let callee_ty = fun(unit_ty.clone(), bool_ty.clone());
        let arg = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path(&["f"])),
                    RuntimeType::core(callee_ty),
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    RuntimeType::core(unit_ty),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::thunk(effect.clone(), RuntimeType::core(bool_ty.clone())),
        );

        let adapted = principal_arg_adapter(&arg, &bool_ty, &effect).expect("adapter");

        assert!(matches!(
            adapted.ty,
            RuntimeType::Thunk {
                effect: ref actual,
                ..
            } if actual == &effect
        ));
    }

    #[test]
    fn erased_effect_param_does_not_thunk_value_argument() {
        let bool_ty = named("bool");
        let arg = Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Bool(true)),
            RuntimeType::core(bool_ty.clone()),
        );

        let adapted = principal_arg_adapter(&arg, &bool_ty, &typed_ir::Type::Any).expect("adapter");

        assert!(matches!(
            adapted.kind,
            ExprKind::Lit(typed_ir::Lit::Bool(true))
        ));
        assert_eq!(adapted.ty, RuntimeType::core(bool_ty));
    }

    #[test]
    fn erased_row_effect_param_does_not_thunk_value_argument() {
        let bool_ty = named("bool");
        let effect = typed_ir::Type::Row {
            items: Vec::new(),
            tail: Box::new(typed_ir::Type::Any),
        };
        let arg = Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Bool(true)),
            RuntimeType::core(bool_ty.clone()),
        );

        let adapted = principal_arg_adapter(&arg, &bool_ty, &effect).expect("adapter");

        assert!(matches!(
            adapted.kind,
            ExprKind::Lit(typed_ir::Lit::Bool(true))
        ));
        assert_eq!(adapted.ty, RuntimeType::core(bool_ty));
    }

    #[test]
    fn keeps_apply_that_really_returns_effect_thunk() {
        let bool_ty = named("bool");
        let unit_ty = named("unit");
        let effect = named("std::junction::junction");
        let callee_ty = fun_with_effect(
            unit_ty.clone(),
            typed_ir::Type::Never,
            bool_ty.clone(),
            effect.clone(),
        );
        let arg = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path(&["f"])),
                    RuntimeType::core(callee_ty),
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    RuntimeType::core(unit_ty),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::thunk(effect.clone(), RuntimeType::core(bool_ty.clone())),
        );

        let adapted = principal_arg_adapter(&arg, &bool_ty, &effect).expect("adapter");

        assert!(matches!(adapted.kind, ExprKind::Apply { .. }));
    }

    #[test]
    fn bind_here_context_refines_inner_unknown_thunk_value() {
        let int_ty = named("int");
        let effect = named("std::flow::sub");
        let expr = Expr::typed(
            ExprKind::Var(path(&["return_call"])),
            RuntimeType::thunk(effect.clone(), RuntimeType::Unknown),
        );

        let refined = refine_bind_here_inner_thunk_value_from_context(
            expr,
            Some(typed_ir::TypeBounds::exact(int_ty.clone())),
        );

        assert_eq!(
            refined.ty,
            RuntimeType::thunk(effect, RuntimeType::core(int_ty))
        );
    }

    #[test]
    fn apply_argument_refines_unknown_callee_input() {
        let int_ty = named("int");
        let bool_ty = named("bool");
        let callee = Expr::typed(
            ExprKind::Var(path(&["predicate"])),
            RuntimeType::fun(RuntimeType::Unknown, RuntimeType::core(bool_ty.clone())),
        );
        let arg = Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
            RuntimeType::core(int_ty.clone()),
        );

        let refined = refine_apply_callee_input_from_arg(callee, &arg);

        assert_eq!(
            refined.ty,
            RuntimeType::fun(RuntimeType::core(int_ty), RuntimeType::core(bool_ty))
        );
    }

    #[test]
    fn apply_argument_refines_typevar_callee_input() {
        let int_ty = named("int");
        let bool_ty = named("bool");
        let callee = Expr::typed(
            ExprKind::Var(path(&["predicate"])),
            RuntimeType::fun(
                RuntimeType::core(typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()))),
                RuntimeType::core(bool_ty.clone()),
            ),
        );
        let arg = Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
            RuntimeType::core(int_ty.clone()),
        );

        let refined = refine_apply_callee_input_from_arg(callee, &arg);

        assert_eq!(
            refined.ty,
            RuntimeType::fun(RuntimeType::core(int_ty), RuntimeType::core(bool_ty))
        );
    }

    fn fun(param: typed_ir::Type, ret: typed_ir::Type) -> typed_ir::Type {
        fun_with_effect(param, typed_ir::Type::Never, ret, typed_ir::Type::Never)
    }

    fn fun_with_effect(
        param: typed_ir::Type,
        param_effect: typed_ir::Type,
        ret: typed_ir::Type,
        ret_effect: typed_ir::Type,
    ) -> typed_ir::Type {
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(param_effect),
            ret_effect: Box::new(ret_effect),
            ret: Box::new(ret),
        }
    }

    fn named(value: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&[value]),
            args: Vec::new(),
        }
    }

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path::new(segments.iter().map(|segment| name(segment)).collect())
    }

    fn name(value: &str) -> typed_ir::Name {
        typed_ir::Name(value.to_string())
    }
}
