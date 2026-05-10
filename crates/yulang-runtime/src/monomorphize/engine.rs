use std::collections::{HashMap, HashSet};

use super::*;
use crate::ir::{Binding, Module};
use crate::validate::validate_module;

pub fn demand_monomorphize_module(
    module: Module,
) -> Result<DemandMonomorphizeOutput, DemandMonomorphizeError> {
    let mut pending_demands = Vec::new();
    let mut rounds = Vec::new();

    for round_index in 0..MISSING_DEMAND_ROUND_LIMIT {
        // Phase 1: check — run the demand engine with any pending demands
        let engine_out = run_demand_engine(&module, pending_demands.drain(..).collect())?;

        // Phase 2: select — keep only closed (fully concrete) specializations
        let (closed_specs, closed_fresh) = select_closed_specializations(&engine_out);

        if closed_specs.is_empty() {
            rounds.push(DemandRoundProfile::empty(round_index, engine_out.queue_profile));
            return Ok(DemandMonomorphizeOutput {
                module,
                profile: DemandMonomorphizeProfile {
                    rounds,
                    queue: engine_out.queue_profile,
                    ..DemandMonomorphizeProfile::default()
                },
            });
        }

        debug_closed_specializations(&engine_out.specializations);

        // Phase 3: emit — generate specialized bindings for fresh specializations
        let (emitted_bindings, missing_from_emit) =
            emit_fresh_bindings(&module, &closed_fresh, &closed_specs, &engine_out.checked)?;
        let missing_from_emit_count = missing_from_emit.len();

        // Phase 4: validate — filter out bindings that fail per-binding validation
        let valid = filter_valid_fresh_specializations(
            &module,
            &closed_specs,
            &closed_fresh,
            emitted_bindings,
        );

        // Phase 5: rewrite — update call sites in the module to use specializations
        let rewrite = rewrite_module_uses(
            module.clone(),
            &valid.specializations,
            &engine_out.checked,
        )?;

        // Phase 6: missing — collect demands that neither emit nor rewrite resolved
        let mut all_missing = missing_from_emit;
        all_missing.extend(rewrite.missing_demands.iter().cloned());
        let missing_from_rewrite_count = rewrite.missing_demands.len();
        pending_demands =
            compute_pending_missing_demands(&module, &valid.specializations, &all_missing);

        rounds.push(DemandRoundProfile {
            round: round_index,
            queue: engine_out.queue_profile,
            all_specializations: engine_out.specializations.len(),
            closed_specializations: closed_specs.len(),
            fresh_closed: closed_fresh.len(),
            emitted_valid: valid.emitted.len(),
            emitted_rejected: valid.rejected.len(),
            missing_from_emit: missing_from_emit_count,
            missing_from_rewrite: missing_from_rewrite_count,
            pending_next: pending_demands.len(),
            rewrite_changed_bindings: rewrite.changed_bindings,
            rewrite_changed_roots: rewrite.changed_roots,
        });

        if !pending_demands.is_empty() && round_index + 1 < MISSING_DEMAND_ROUND_LIMIT {
            debug_missing_demand_round(round_index, &pending_demands);
            continue;
        }

        if rewrite.changed_roots == 0 && rewrite.changed_bindings == 0 {
            return Ok(DemandMonomorphizeOutput {
                module: rewrite.module,
                profile: DemandMonomorphizeProfile {
                    rounds,
                    queue: engine_out.queue_profile,
                    ..DemandMonomorphizeProfile::default()
                },
            });
        }

        // Phase 7: commit — add emitted bindings and prune unreachable ones
        let module = commit_demand_round(rewrite.module, valid.emitted, &valid.emitted_names);
        let retained_names: HashSet<_> = module.bindings.iter().map(|b| b.name.clone()).collect();
        let emitted_specializations: Vec<_> = valid
            .specializations
            .iter()
            .filter(|s| {
                valid.emitted_names.contains(&s.path) && retained_names.contains(&s.path)
            })
            .cloned()
            .collect();

        return Ok(DemandMonomorphizeOutput {
            module,
            profile: DemandMonomorphizeProfile {
                specializations: emitted_specializations.len(),
                queue: engine_out.queue_profile,
                emitted_specializations,
                rejected_specializations: valid.rejected,
                rounds,
            },
        });
    }

    Ok(DemandMonomorphizeOutput {
        module,
        profile: DemandMonomorphizeProfile {
            rounds,
            ..DemandMonomorphizeProfile::default()
        },
    })
}

const MISSING_DEMAND_ROUND_LIMIT: usize = 6;

fn run_demand_engine(
    module: &Module,
    pending: Vec<Demand>,
) -> Result<DemandEngineOutput, DemandCheckError> {
    let mut engine = DemandEngine::from_module(module);
    engine.push_demands(pending);
    engine.run()
}

fn select_closed_specializations(
    engine_out: &DemandEngineOutput,
) -> (Vec<DemandSpecialization>, Vec<DemandSpecialization>) {
    let closed = engine_out
        .specializations
        .iter()
        .filter(|s| s.solved.is_closed())
        .cloned()
        .collect();
    let closed_fresh = engine_out
        .fresh_specializations
        .iter()
        .filter(|s| s.solved.is_closed())
        .cloned()
        .collect();
    (closed, closed_fresh)
}

fn emit_fresh_bindings(
    module: &Module,
    fresh: &[DemandSpecialization],
    all_closed: &[DemandSpecialization],
    checked: &[CheckedDemand],
) -> Result<(Vec<Binding>, Vec<MissingDemand>), DemandEmitError> {
    let out = DemandEmitter::from_module_with_checked(module, fresh, all_closed, checked)
        .emit_all_report()?;
    Ok((out.bindings, out.missing_demands))
}

fn rewrite_module_uses(
    module: Module,
    specializations: &[DemandSpecialization],
    checked: &[CheckedDemand],
) -> Result<DemandRewriteOutput, DemandEmitError> {
    DemandEmitter::rewrite_module_uses_with_checked_report(module, specializations, checked)
}

fn compute_pending_missing_demands(
    module: &Module,
    specializations: &[DemandSpecialization],
    missing: &[MissingDemand],
) -> Vec<Demand> {
    unresolved_missing_demands(module, specializations, missing)
}

fn commit_demand_round(
    mut module: Module,
    emitted: Vec<Binding>,
    emitted_names: &HashSet<core_ir::Path>,
) -> Module {
    module.bindings.extend(emitted);
    retain_reachable_emitted_bindings(&mut module, emitted_names);
    module
}

fn debug_closed_specializations(specializations: &[DemandSpecialization]) {
    if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_none() {
        return;
    }
    for specialization in specializations {
        let status = if specialization.solved.is_closed() {
            "closed"
        } else {
            "open"
        };
        eprintln!(
            "demand specialization {status} {:?} -> {:?}: {:?}",
            specialization.target, specialization.path, specialization.solved
        );
    }
}

struct ValidDemandOutput {
    specializations: Vec<DemandSpecialization>,
    emitted: Vec<Binding>,
    emitted_names: HashSet<core_ir::Path>,
    rejected: Vec<RejectedDemandSpecialization>,
}

fn filter_valid_fresh_specializations(
    module: &Module,
    specializations: &[DemandSpecialization],
    fresh_specializations: &[DemandSpecialization],
    emitted: Vec<Binding>,
) -> ValidDemandOutput {
    let original_bindings = module
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    let fresh_paths = fresh_specializations
        .iter()
        .map(|specialization| specialization.path.clone())
        .collect::<HashSet<_>>();
    let fresh_by_path = fresh_specializations
        .iter()
        .map(|s| (s.path.clone(), s.clone()))
        .collect::<HashMap<_, _>>();
    let mut valid_fresh_paths = HashSet::new();
    let mut rejected = Vec::new();
    let mut emitted_by_path = Vec::new();
    for (specialization, binding) in fresh_specializations.iter().zip(emitted) {
        if emitted_binding_validates(module, &binding) {
            valid_fresh_paths.insert(specialization.path.clone());
        } else {
            if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some() {
                eprintln!(
                    "demand specialization {:?} skipped after per-binding validation",
                    specialization.path
                );
            }
            rejected.push(RejectedDemandSpecialization {
                specialization: specialization.clone(),
                reason: RejectionReason::ValidationFailed,
            });
        }
        emitted_by_path.push((specialization.path.clone(), binding));
    }
    loop {
        let mut removed = Vec::new();
        for (path, binding) in &emitted_by_path {
            if !valid_fresh_paths.contains(path) {
                continue;
            }
            let mut refs = Vec::new();
            collect_expr_refs(&binding.body, &mut refs);
            if let Some(rejected_dep) = refs.iter().find(|referenced| {
                fresh_paths.contains(*referenced) && !valid_fresh_paths.contains(*referenced)
            }) {
                removed.push((path.clone(), rejected_dep.clone()));
            }
        }
        if removed.is_empty() {
            break;
        }
        let debug = std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some();
        for (path, dep) in removed {
            if valid_fresh_paths.remove(&path) {
                if debug {
                    eprintln!(
                        "demand specialization {:?} skipped because a fresh dependency was rejected",
                        path
                    );
                }
                if let Some(specialization) = fresh_by_path.get(&path) {
                    rejected.push(RejectedDemandSpecialization {
                        specialization: specialization.clone(),
                        reason: RejectionReason::DependsOnRejectedFresh(dep),
                    });
                }
            }
        }
    }
    let valid_specializations = specializations
        .iter()
        .filter(|specialization| {
            original_bindings.contains(&specialization.path)
                || valid_fresh_paths.contains(&specialization.path)
        })
        .cloned()
        .collect();
    let mut valid_emitted = Vec::new();
    let mut emitted_names = HashSet::new();
    for (path, binding) in emitted_by_path {
        if valid_fresh_paths.contains(&path) {
            emitted_names.insert(path);
            valid_emitted.push(binding);
        }
    }
    ValidDemandOutput {
        specializations: valid_specializations,
        emitted: valid_emitted,
        emitted_names,
        rejected,
    }
}

fn emitted_binding_validates(module: &Module, binding: &Binding) -> bool {
    let candidate = Module {
        path: module.path.clone(),
        bindings: vec![binding.clone()],
        root_exprs: Vec::new(),
        roots: Vec::new(),
        role_impls: module.role_impls.clone(),
    };
    match validate_module(&candidate) {
        Ok(()) => true,
        Err(error) => {
            if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some() {
                eprintln!(
                    "demand specialization {:?} rejected by validation: {error:?}",
                    binding.name
                );
            }
            if std::env::var_os("YULANG_DEBUG_MONO_DUMP_REJECTED").is_some() {
                eprintln!("{binding:#?}");
            }
            false
        }
    }
}

fn retain_reachable_emitted_bindings(module: &mut Module, emitted_names: &HashSet<core_ir::Path>) {
    if emitted_names.is_empty() {
        return;
    }
    let reachable = reachable_binding_paths(module);
    module.bindings.retain(|binding| {
        !emitted_names.contains(&binding.name) || reachable.contains(&binding.name)
    });
}

fn unresolved_missing_demands(
    module: &Module,
    specializations: &[DemandSpecialization],
    missing: &[MissingDemand],
) -> Vec<Demand> {
    if missing.is_empty() {
        return Vec::new();
    }
    let known = specializations
        .iter()
        .map(|specialization| specialization.key.clone())
        .collect::<HashSet<_>>();
    let checker = DemandChecker::from_module(module);
    let mut queue = checker.missing_demands_queue(missing);
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    while let Some(demand) = queue.pop_front() {
        if known.contains(&demand.key) || !seen.insert(demand.key.clone()) {
            continue;
        }
        out.push(demand);
    }
    out
}

fn debug_missing_demand_round(round: usize, demands: &[Demand]) {
    if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_none() {
        return;
    }
    for demand in demands {
        eprintln!(
            "demand specialization round {round} discovered missing {:?}: {:?}",
            demand.target, demand.key.signature
        );
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandMonomorphizeOutput {
    pub module: Module,
    pub profile: DemandMonomorphizeProfile,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct DemandMonomorphizeProfile {
    pub specializations: usize,
    pub queue: DemandQueueProfile,
    pub emitted_specializations: Vec<DemandSpecialization>,
    pub rejected_specializations: Vec<RejectedDemandSpecialization>,
    pub rounds: Vec<DemandRoundProfile>,
}

/// Per-round observability: shows what each iteration of the demand loop did.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct DemandRoundProfile {
    pub round: usize,
    pub queue: DemandQueueProfile,
    pub all_specializations: usize,
    pub closed_specializations: usize,
    pub fresh_closed: usize,
    pub emitted_valid: usize,
    pub emitted_rejected: usize,
    pub missing_from_emit: usize,
    pub missing_from_rewrite: usize,
    pub pending_next: usize,
    pub rewrite_changed_bindings: usize,
    pub rewrite_changed_roots: usize,
}

impl DemandRoundProfile {
    fn empty(round: usize, queue: DemandQueueProfile) -> Self {
        Self {
            round,
            queue,
            ..Self::default()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RejectedDemandSpecialization {
    pub specialization: DemandSpecialization,
    pub reason: RejectionReason,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RejectionReason {
    ValidationFailed,
    DependsOnRejectedFresh(core_ir::Path),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DemandMonomorphizeError {
    Check(DemandCheckError),
    Emit(DemandEmitError),
}

impl From<DemandCheckError> for DemandMonomorphizeError {
    fn from(error: DemandCheckError) -> Self {
        Self::Check(error)
    }
}

impl From<DemandEmitError> for DemandMonomorphizeError {
    fn from(error: DemandEmitError) -> Self {
        Self::Emit(error)
    }
}

pub struct DemandEngine<'a> {
    checker: DemandChecker<'a>,
    queue: DemandQueue,
    specializations: SpecializationTable,
    checked: Vec<CheckedDemand>,
}

impl<'a> DemandEngine<'a> {
    pub fn from_module(module: &'a Module) -> Self {
        let mut collector = DemandCollector::from_module(module);
        collector.collect_module(module);
        debug_demand_queue_source("initial collect", collector.queue());
        Self {
            checker: DemandChecker::from_module(module),
            queue: collector.into_queue(),
            specializations: SpecializationTable::from_module(module),
            checked: Vec::new(),
        }
    }

    pub fn push_demands(&mut self, demands: impl IntoIterator<Item = Demand>) {
        for demand in demands {
            debug_demand_source("pending missing", &demand.target, &demand.key.signature);
            self.queue
                .push_signature(demand.target, demand.expected, demand.key.signature);
        }
    }

    pub fn run(mut self) -> Result<DemandEngineOutput, DemandCheckError> {
        while let Some(demand) = self.queue.pop_front() {
            let checked = match self.checker.check_demand(&demand) {
                Ok(checked) => checked,
                Err(error) => {
                    if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some() {
                        eprintln!(
                            "demand rejected for {:?}: {:?}: {:?}",
                            demand.target, demand.key.signature, error
                        );
                    }
                    continue;
                }
            };
            self.specializations.allocate_fresh(&checked);
            let mut child_demands = checked.child_demands.clone();
            let child_source = format!("checked child from {:?}", checked.target);
            debug_demand_queue_source(&child_source, &child_demands);
            while let Some(child) = child_demands.pop_front() {
                self.queue
                    .push_signature(child.target, child.expected, child.key.signature);
            }
            self.checked.push(checked);
        }
        let specializations = self.specializations.into_output();
        let queue_profile = self.queue.profile();
        Ok(DemandEngineOutput {
            checked: self.checked,
            specializations: specializations.known,
            fresh_specializations: specializations.fresh,
            queue_profile,
        })
    }
}

fn debug_demand_queue_source(source: &str, queue: &DemandQueue) {
    if std::env::var_os("YULANG_DEBUG_DEMAND_SOURCE").is_none() {
        return;
    }
    for demand in queue.iter() {
        debug_demand_source(source, &demand.target, &demand.key.signature);
    }
}

fn debug_demand_source(source: &str, target: &core_ir::Path, signature: &DemandSignature) {
    if std::env::var_os("YULANG_DEBUG_DEMAND_SOURCE").is_none() {
        return;
    }
    let status = if signature.is_closed() {
        "closed"
    } else {
        "open"
    };
    eprintln!("demand source {source} {status} {target:?}: {signature:?}");
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandEngineOutput {
    pub checked: Vec<CheckedDemand>,
    pub specializations: Vec<DemandSpecialization>,
    pub fresh_specializations: Vec<DemandSpecialization>,
    pub queue_profile: DemandQueueProfile,
}

impl DemandEngineOutput {
    pub fn emit_bindings(&self, module: &Module) -> Result<Vec<Binding>, DemandEmitError> {
        DemandEmitter::from_module_with_checked(
            module,
            &self.fresh_specializations,
            &self.specializations,
            &self.checked,
        )
        .emit_all()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Binding, Expr, ExprKind, Root, Type as RuntimeType};

    #[test]
    fn engine_processes_root_and_child_demands_in_order() {
        let id = path("id");
        let use_id = path("use_id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                binding(
                    id.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(core_ir::Type::Any),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                ),
                binding(
                    use_id.clone(),
                    Vec::new(),
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(named("int")),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(id.clone()),
                                    RuntimeType::fun(
                                        RuntimeType::core(core_ir::Type::Any),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Var(path("x")),
                                    RuntimeType::core(named("int")),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::core(named("int")),
                        )),
                    },
                ),
            ],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(use_id.clone()),
                        RuntimeType::fun(
                            RuntimeType::core(named("int")),
                            RuntimeType::core(named("int")),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::core(named("int")),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = DemandEngine::from_module(&module)
            .run()
            .expect("ran engine");
        let checked_targets = output
            .checked
            .iter()
            .map(|checked| checked.target.clone())
            .collect::<Vec<_>>();

        assert_eq!(checked_targets, vec![id]);
        assert_eq!(output.specializations.len(), 1);
        assert_eq!(
            output.specializations[0].path,
            core_ir::Path::from_name(core_ir::Name("id__ddmono0".to_string()))
        );
        let emitted = output.emit_bindings(&module).expect("emitted bindings");
        assert_eq!(emitted.len(), 1);
        assert_eq!(emitted[0].name, path("id__ddmono0"));
        assert!(emitted[0].type_params.is_empty());
    }

    #[test]
    fn demand_monomorphize_rewrites_root_call_to_specialization() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![binding(
                id.clone(),
                vec![core_ir::TypeVar("a".to_string())],
                RuntimeType::fun(
                    RuntimeType::core(core_ir::Type::Any),
                    RuntimeType::core(core_ir::Type::Any),
                ),
                ExprKind::Lambda {
                    param: core_ir::Name("x".to_string()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Var(path("x")),
                        RuntimeType::core(core_ir::Type::Any),
                    )),
                },
            )],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(id),
                        RuntimeType::fun(
                            RuntimeType::core(core_ir::Type::Any),
                            RuntimeType::core(core_ir::Type::Any),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::core(named("int")),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = demand_monomorphize_module(module).expect("demand monomorphized");

        assert_eq!(output.profile.specializations, 1);
        assert_eq!(output.module.bindings.len(), 2);
        let ExprKind::Apply { callee, .. } = &output.module.root_exprs[0].kind else {
            panic!("expected rewritten root call");
        };
        let ExprKind::Var(path) = &callee.kind else {
            panic!("expected specialized callee");
        };
        assert_eq!(
            path,
            &core_ir::Path::from_name(core_ir::Name("id__ddmono0".to_string()))
        );
    }

    #[test]
    fn filtering_rejects_fresh_bindings_that_depend_on_rejected_fresh_bindings() {
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: Vec::new(),
            roots: Vec::new(),
            role_impls: Vec::new(),
        };
        let wrapper = path_segments(&["std", "wrapper__ddmono0"]);
        let helper = path_segments(&["std", "helper__ddmono1"]);
        let ok = path_segments(&["std", "ok__ddmono2"]);
        let specs = vec![
            specialization(path_segments(&["std", "wrapper"]), wrapper.clone()),
            specialization(path_segments(&["std", "helper"]), helper.clone()),
            specialization(path_segments(&["std", "ok"]), ok.clone()),
        ];
        let emitted = vec![
            monomorphic_binding(
                wrapper.clone(),
                Expr::typed(
                    ExprKind::Var(helper.clone()),
                    RuntimeType::core(named("int")),
                ),
            ),
            Binding {
                name: helper,
                type_params: Vec::new(),
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: named("bool"),
                },
                body: Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                    RuntimeType::core(named("int")),
                ),
            },
            monomorphic_binding(
                ok.clone(),
                Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Int("2".to_string())),
                    RuntimeType::core(named("int")),
                ),
            ),
        ];

        let output = filter_valid_fresh_specializations(&module, &specs, &specs, emitted);

        assert_eq!(
            output
                .specializations
                .iter()
                .map(|specialization| specialization.path.clone())
                .collect::<Vec<_>>(),
            vec![ok.clone()]
        );
        assert_eq!(
            output
                .emitted
                .iter()
                .map(|binding| binding.name.clone())
                .collect::<Vec<_>>(),
            vec![ok]
        );
    }

    fn binding(
        name: core_ir::Path,
        type_params: Vec<core_ir::TypeVar>,
        ty: RuntimeType,
        kind: ExprKind,
    ) -> Binding {
        Binding {
            name,
            type_params,
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: core_ir::Type::Any,
            },
            body: Expr::typed(kind, ty),
        }
    }

    fn monomorphic_binding(name: core_ir::Path, body: Expr) -> Binding {
        Binding {
            name,
            type_params: Vec::new(),
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: named("int"),
            },
            body,
        }
    }

    fn specialization(target: core_ir::Path, path: core_ir::Path) -> DemandSpecialization {
        let solved = DemandSignature::Core(named_demand("int"));
        DemandSpecialization {
            target: target.clone(),
            path,
            key: DemandKey::from_signature(target, solved.clone()),
            solved,
        }
    }

    fn named_demand(name: &str) -> DemandCoreType {
        DemandCoreType::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }

    fn path_segments(segments: &[&str]) -> core_ir::Path {
        core_ir::Path {
            segments: segments
                .iter()
                .map(|segment| core_ir::Name((*segment).to_string()))
                .collect(),
        }
    }
}
