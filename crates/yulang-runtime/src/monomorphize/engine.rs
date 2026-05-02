use std::collections::{HashMap, HashSet};

use super::*;
use crate::ir::{Binding, Expr, ExprKind, Module, RecordSpreadExpr, Stmt};
use crate::validate::validate_module;

pub fn demand_monomorphize_module(
    module: Module,
) -> Result<DemandMonomorphizeOutput, DemandMonomorphizeError> {
    let mut pending_demands = Vec::new();
    for round in 0..MISSING_DEMAND_ROUND_LIMIT {
        let mut engine = DemandEngine::from_module(&module);
        engine.push_demands(pending_demands.drain(..));
        let engine_output = engine.run()?;
        if engine_output.specializations.is_empty() {
            return Ok(DemandMonomorphizeOutput {
                module,
                profile: DemandMonomorphizeProfile::default(),
            });
        }
        let specializations = engine_output
            .specializations
            .iter()
            .filter(|specialization| specialization.solved.is_closed())
            .cloned()
            .collect::<Vec<_>>();
        if specializations.is_empty() {
            return Ok(DemandMonomorphizeOutput {
                module,
                profile: DemandMonomorphizeProfile::default(),
            });
        }
        if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some() {
            for specialization in &engine_output.specializations {
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
        let checked = engine_output.checked;
        let fresh_specializations = engine_output
            .fresh_specializations
            .iter()
            .filter(|specialization| specialization.solved.is_closed())
            .cloned()
            .collect::<Vec<_>>();
        let emitted = DemandEmitter::from_module_with_checked(
            &module,
            &fresh_specializations,
            &specializations,
            &checked,
        )
        .emit_all_report()?;
        let mut missing_demands = emitted.missing_demands.clone();
        let valid_output = filter_valid_fresh_specializations(
            &module,
            &specializations,
            &fresh_specializations,
            emitted.bindings,
        );
        let rewrite = DemandEmitter::rewrite_module_uses_with_checked_report(
            module.clone(),
            &valid_output.specializations,
            &checked,
        )?;
        missing_demands.extend(rewrite.missing_demands.clone());
        pending_demands =
            unresolved_missing_demands(&module, &valid_output.specializations, &missing_demands);
        if !pending_demands.is_empty() && round + 1 < MISSING_DEMAND_ROUND_LIMIT {
            debug_missing_demand_round(round, &pending_demands);
            continue;
        }
        if rewrite.changed_roots == 0 && rewrite.changed_bindings == 0 {
            return Ok(DemandMonomorphizeOutput {
                module: rewrite.module,
                profile: DemandMonomorphizeProfile::default(),
            });
        }
        let mut module = rewrite.module;
        let emitted_count = valid_output.emitted.len();
        let emitted_names = valid_output
            .emitted
            .iter()
            .map(|binding| binding.name.clone())
            .collect::<HashSet<_>>();
        module.bindings.extend(valid_output.emitted);
        retain_reachable_emitted_bindings(&mut module, &emitted_names);
        return Ok(DemandMonomorphizeOutput {
            module,
            profile: DemandMonomorphizeProfile {
                specializations: emitted_count,
            },
        });
    }
    Ok(DemandMonomorphizeOutput {
        module,
        profile: DemandMonomorphizeProfile::default(),
    })
}

const MISSING_DEMAND_ROUND_LIMIT: usize = 6;

struct ValidDemandOutput {
    specializations: Vec<DemandSpecialization>,
    emitted: Vec<Binding>,
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
    let mut valid_fresh_paths = HashSet::new();
    let mut emitted_by_path = Vec::new();
    for (specialization, binding) in fresh_specializations.iter().zip(emitted) {
        if emitted_binding_validates(module, &binding) {
            valid_fresh_paths.insert(specialization.path.clone());
        } else if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some() {
            eprintln!(
                "demand specialization {:?} skipped after per-binding validation",
                specialization.path
            );
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
            if refs.iter().any(|referenced| {
                fresh_paths.contains(referenced) && !valid_fresh_paths.contains(referenced)
            }) {
                removed.push(path.clone());
            }
        }
        if removed.is_empty() {
            break;
        }
        let debug = std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some();
        for path in removed {
            valid_fresh_paths.remove(&path);
            if debug {
                eprintln!(
                    "demand specialization {:?} skipped because a fresh dependency was rejected",
                    path
                );
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
    let valid_emitted = emitted_by_path
        .into_iter()
        .filter_map(|(path, binding)| valid_fresh_paths.contains(&path).then_some(binding))
        .collect();
    ValidDemandOutput {
        specializations: valid_specializations,
        emitted: valid_emitted,
    }
}

fn emitted_binding_validates(module: &Module, binding: &Binding) -> bool {
    let candidate = Module {
        path: module.path.clone(),
        bindings: vec![binding.clone()],
        root_exprs: Vec::new(),
        roots: Vec::new(),
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
    let bodies = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.body.clone()))
        .collect::<HashMap<_, _>>();
    let mut reachable = HashSet::new();
    let mut stack = Vec::new();
    for root in &module.roots {
        if let crate::ir::Root::Binding(path) = root {
            stack.push(path.clone());
        }
    }
    for expr in &module.root_exprs {
        collect_expr_refs(expr, &mut stack);
    }
    while let Some(path) = stack.pop() {
        if !reachable.insert(path.clone()) {
            continue;
        }
        if let Some(body) = bodies.get(&path) {
            collect_expr_refs(body, &mut stack);
        }
    }
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

fn collect_expr_refs(expr: &Expr, out: &mut Vec<core_ir::Path>) {
    match &expr.kind {
        ExprKind::Var(path) => out.push(path.clone()),
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => collect_expr_refs(body, out),
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_refs(callee, out);
            collect_expr_refs(arg, out);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_refs(cond, out);
            collect_expr_refs(then_branch, out);
            collect_expr_refs(else_branch, out);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_refs(item, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_refs(&field.value, out);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_expr_refs(expr, out);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_refs(value, out);
            }
        }
        ExprKind::Select { base, .. } => collect_expr_refs(base, out),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_refs(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(guard, out);
                }
                collect_expr_refs(&arm.body, out);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_refs(stmt, out);
            }
            if let Some(tail) = tail {
                collect_expr_refs(tail, out);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_refs(body, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(guard, out);
                }
                collect_expr_refs(&arm.body, out);
            }
        }
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_stmt_refs(stmt: &Stmt, out: &mut Vec<core_ir::Path>) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_refs(value, out);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandMonomorphizeOutput {
    pub module: Module,
    pub profile: DemandMonomorphizeProfile,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct DemandMonomorphizeProfile {
    pub specializations: usize,
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
        Self {
            checker: DemandChecker::from_module(module),
            queue: collector.into_queue(),
            specializations: SpecializationTable::from_module(module),
            checked: Vec::new(),
        }
    }

    pub fn push_demands(&mut self, demands: impl IntoIterator<Item = Demand>) {
        for demand in demands {
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
            self.specializations.intern(&checked);
            let mut child_demands = checked.child_demands.clone();
            while let Some(child) = child_demands.pop_front() {
                self.queue
                    .push_signature(child.target, child.expected, child.key.signature);
            }
            self.checked.push(checked);
        }
        let specializations = self.specializations.into_output();
        Ok(DemandEngineOutput {
            checked: self.checked,
            specializations: specializations.known,
            fresh_specializations: specializations.fresh,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandEngineOutput {
    pub checked: Vec<CheckedDemand>,
    pub specializations: Vec<DemandSpecialization>,
    pub fresh_specializations: Vec<DemandSpecialization>,
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
