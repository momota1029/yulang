use mono::{EffectFamily, Program, StackWeight, Type};
use poly::expr as poly_expr;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::fmt::Write as _;

use super::{
    EffectSubtractionDemand, SolvedExprType, SolvedTask, TypeGraph, TypeSlot, TypeSlotKind,
    TypeclassResolution, WeightedSlotEdge, WeightedTypeBound, close_resolved_runtime_surface,
    stack_weight_is_empty,
};

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct SpecializeOutput {
    pub program: Program,
    pub runtime_evidence: RuntimeEvidenceSurface,
}

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct RuntimeEvidenceSurface {
    #[serde(default)]
    pub host_manifest: Option<poly::host_manifest::HostActManifest>,
    #[serde(default)]
    pub static_routes: Vec<RuntimeEvidenceStaticRoute>,
    #[serde(default)]
    pub known_state_handlers: Vec<RuntimeEvidenceKnownStateHandler>,
    #[serde(default)]
    pub known_state_accesses: Vec<RuntimeEvidenceKnownStateAccess>,
    pub tasks: Vec<RuntimeEvidenceTask>,
}

impl RuntimeEvidenceSurface {
    pub(super) fn attach_known_state_handlers(&mut self, arena: &poly_expr::Arena) {
        let known_state_effects = known_state_effects_from_arena(arena);
        self.known_state_handlers = known_state_handlers_from_effects(&known_state_effects);
        self.known_state_accesses =
            known_state_accesses_from_tasks(&known_state_effects, &self.tasks);
    }

    pub fn attach_static_routes(&mut self, arena: &poly_expr::Arena, program: &Program) {
        self.static_routes =
            static_routes_from_tasks(arena, program, self.host_manifest.as_ref(), &self.tasks);
    }

    pub(super) fn push_solved_task(
        &mut self,
        arena: &poly_expr::Arena,
        owner: RuntimeEvidenceTaskOwner,
        solved: &SolvedTask,
    ) {
        self.tasks
            .push(RuntimeEvidenceTask::from_solved(arena, owner, solved));
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceStaticRoute {
    pub operation_expr: u32,
    pub apply: u32,
    pub callee: u32,
    #[serde(default)]
    pub operation_def: u32,
    pub family: Vec<String>,
    pub resolution: RuntimeEvidenceStaticRouteResolution,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceStaticRouteResolution {
    StaticHandler { handler_expr: u32 },
    Dynamic(RuntimeEvidenceStaticRouteDynamicReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceStaticRouteDynamicReason {
    OpenRow,
    MultipleCandidates,
    HygieneBarrier,
    ProviderEnvDependent,
    DelayedBoundary,
    HostEscape,
    Unclassified,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceKnownStateHandler {
    #[serde(default)]
    pub synthetic_var: u32,
    pub effect_path: Vec<String>,
    pub source: RuntimeEvidenceKnownStateHandlerSource,
    pub continuation: RuntimeEvidenceKnownStateContinuationSemantics,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceKnownStateAccess {
    pub synthetic_var: u32,
    pub operation_expr: u32,
    pub apply: u32,
    pub callee: u32,
    pub arg: u32,
    pub operation_def: u32,
    pub role: RuntimeEvidenceKnownStateAccessRole,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceKnownStateAccessRole {
    StateGet,
    StateSet,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceKnownStateHandlerSource {
    CompilerLocalVar,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceKnownStateContinuationSemantics {
    SnapshotFork,
}

#[derive(Debug, Clone)]
struct RuntimeEvidenceKnownStateEffect {
    synthetic_var: u32,
    effect_path: Vec<String>,
    get_operation: Option<u32>,
    set_operation: Option<u32>,
}

fn known_state_effects_from_arena(
    arena: &poly_expr::Arena,
) -> Vec<RuntimeEvidenceKnownStateEffect> {
    let mut effects = arena.synthetic_var_effects.clone();
    effects.sort_by(|left, right| left.effect_path.cmp(&right.effect_path));
    effects
        .into_iter()
        .enumerate()
        .map(|(index, effect)| RuntimeEvidenceKnownStateEffect {
            synthetic_var: index as u32,
            effect_path: effect.effect_path,
            get_operation: effect.get_operation.map(|def| def.0),
            set_operation: effect.set_operation.map(|def| def.0),
        })
        .collect()
}

fn known_state_handlers_from_effects(
    effects: &[RuntimeEvidenceKnownStateEffect],
) -> Vec<RuntimeEvidenceKnownStateHandler> {
    effects
        .iter()
        .map(|effect| RuntimeEvidenceKnownStateHandler {
            synthetic_var: effect.synthetic_var,
            effect_path: effect.effect_path.clone(),
            source: RuntimeEvidenceKnownStateHandlerSource::CompilerLocalVar,
            continuation: RuntimeEvidenceKnownStateContinuationSemantics::SnapshotFork,
        })
        .collect()
}

fn known_state_accesses_from_tasks(
    effects: &[RuntimeEvidenceKnownStateEffect],
    tasks: &[RuntimeEvidenceTask],
) -> Vec<RuntimeEvidenceKnownStateAccess> {
    let mut operations = std::collections::BTreeMap::new();
    for effect in effects {
        if let Some(def) = effect.get_operation {
            operations.insert(
                def,
                (
                    effect.synthetic_var,
                    RuntimeEvidenceKnownStateAccessRole::StateGet,
                ),
            );
        }
        if let Some(def) = effect.set_operation {
            operations.insert(
                def,
                (
                    effect.synthetic_var,
                    RuntimeEvidenceKnownStateAccessRole::StateSet,
                ),
            );
        }
    }
    if operations.is_empty() {
        return Vec::new();
    }

    let mut accesses = Vec::new();
    for task in tasks {
        for node in &task.nodes {
            let RuntimeEvidenceNodeKind::OperationCall {
                callee, arg, def, ..
            } = &node.kind
            else {
                continue;
            };
            let Some((synthetic_var, role)) = operations.get(def).copied() else {
                continue;
            };
            accesses.push(RuntimeEvidenceKnownStateAccess {
                synthetic_var,
                operation_expr: node.expr,
                apply: node.expr,
                callee: *callee,
                arg: *arg,
                operation_def: *def,
                role,
            });
        }
    }
    accesses.sort_by_key(|access| {
        (
            access.synthetic_var,
            access.operation_def,
            access.operation_expr,
        )
    });
    accesses
}

fn static_routes_from_tasks(
    arena: &poly_expr::Arena,
    program: &Program,
    host_manifest: Option<&poly::host_manifest::HostActManifest>,
    tasks: &[RuntimeEvidenceTask],
) -> Vec<RuntimeEvidenceStaticRoute> {
    let program_index = StaticRouteProgramIndex::new(program);
    let mut analyses = Vec::new();
    for (task_index, task) in tasks.iter().enumerate() {
        let mut classifier =
            TaskStaticRouteClassifier::new(arena, &program_index, task_index, task);
        classifier.visit_expr(arena, task_root_expr(task), 0);
        analyses.push(classifier.finish());
    }
    let mut routes = StaticRouteL2Resolver::new(host_manifest, tasks, analyses).finish();
    routes.sort_by_key(|route| (route.operation_expr, route.apply, route.callee));
    routes
}

fn task_root_expr(task: &RuntimeEvidenceTask) -> u32 {
    match task.owner {
        RuntimeEvidenceTaskOwner::RootExpr { expr, .. } => expr,
        RuntimeEvidenceTaskOwner::InstanceBody { body, .. } => body,
    }
}

struct TaskStaticRouteClassifier {
    task_index: usize,
    operation_calls: BTreeMap<u32, RuntimeEvidenceOperationCallSite>,
    app_calls: BTreeMap<u32, RuntimeEvidenceAppCallSite>,
    active_handlers: Vec<RuntimeEvidenceActiveHandler>,
    routes: BTreeMap<u32, RuntimeEvidenceStaticRoute>,
    operation_lambda_depths: BTreeMap<u32, u32>,
    operation_hygiene_barriers: BTreeMap<u32, bool>,
    call_edges: Vec<RuntimeEvidenceCallEdge>,
}

impl TaskStaticRouteClassifier {
    fn new(
        arena: &poly_expr::Arena,
        program_index: &StaticRouteProgramIndex,
        task_index: usize,
        task: &RuntimeEvidenceTask,
    ) -> Self {
        let ref_signatures = task
            .ref_signatures
            .iter()
            .map(|signature| (signature.expr, &signature.ty))
            .collect::<HashMap<_, _>>();
        let slot_backed_operations = task
            .nodes
            .iter()
            .filter_map(|node| {
                matches!(node.kind, RuntimeEvidenceNodeKind::OperationCall { .. })
                    .then_some((node.expr, !node.slots.is_empty()))
            })
            .collect::<HashMap<_, _>>();
        let operation_calls = task
            .sites
            .iter()
            .filter_map(|site| {
                let RuntimeEvidenceSiteKind::OperationCall {
                    callee,
                    arg: _,
                    def,
                    path,
                } = &site.kind
                else {
                    return None;
                };
                Some((
                    site.expr,
                    RuntimeEvidenceOperationCallSite {
                        operation_expr: site.expr,
                        apply: site.expr,
                        callee: *callee,
                        operation_def: *def,
                        family: path.clone(),
                        lambda_depth: None,
                        provider_env_dependent: slot_backed_operations
                            .get(&site.expr)
                            .copied()
                            .unwrap_or(false),
                        hygiene_barrier: false,
                    },
                ))
            })
            .collect();
        let app_calls = task
            .sites
            .iter()
            .filter_map(|site| {
                let RuntimeEvidenceSiteKind::App {
                    callee,
                    arg: _,
                    argument_contract,
                } = &site.kind
                else {
                    return None;
                };
                let (head, index) =
                    call_spine_head_and_arg_index(arena, poly_expr::ExprId(*callee));
                let callee_instance =
                    program_index.instance_for_callee(arena, head, &ref_signatures)?;
                Some((
                    site.expr,
                    RuntimeEvidenceAppCallSite {
                        callee_instance,
                        applied_lambda_depth: index as u32 + 1,
                        delayed_boundary: *argument_contract,
                    },
                ))
            })
            .collect();
        Self {
            task_index,
            operation_calls,
            app_calls,
            active_handlers: Vec::new(),
            routes: BTreeMap::new(),
            operation_lambda_depths: BTreeMap::new(),
            operation_hygiene_barriers: BTreeMap::new(),
            call_edges: Vec::new(),
        }
    }

    fn finish(self) -> StaticRouteTaskAnalysis {
        let operations = self
            .operation_calls
            .into_values()
            .map(|mut operation| {
                let lambda_depth = self
                    .operation_lambda_depths
                    .get(&operation.operation_expr)
                    .copied();
                operation.hygiene_barrier = self
                    .operation_hygiene_barriers
                    .get(&operation.operation_expr)
                    .copied()
                    .unwrap_or(false);
                operation.lambda_depth = lambda_depth;
                operation
            })
            .collect();
        StaticRouteTaskAnalysis {
            owner: self.task_index,
            operations,
            l1_routes: self.routes,
            call_edges: self.call_edges,
        }
    }

    fn visit_expr(&mut self, arena: &poly_expr::Arena, expr: u32, lambda_depth: u32) {
        self.visit_expr_with_context(
            arena,
            expr,
            lambda_depth,
            StaticRouteVisitContext::default(),
        );
    }

    fn visit_expr_with_context(
        &mut self,
        arena: &poly_expr::Arena,
        expr: u32,
        lambda_depth: u32,
        context: StaticRouteVisitContext,
    ) {
        if let Some(operation) = self.operation_calls.get(&expr).cloned() {
            self.record_operation(operation, lambda_depth, context.hygiene_boundary);
        }
        if let Some(app) = self.app_calls.get(&expr).copied() {
            self.record_call_edge(app, lambda_depth);
        }

        match arena.expr(poly_expr::ExprId(expr)) {
            poly_expr::Expr::Lit(_) | poly_expr::Expr::PrimitiveOp(_) | poly_expr::Expr::Var(_) => {
            }
            poly_expr::Expr::App(callee, arg) | poly_expr::Expr::RefSet(callee, arg) => {
                self.visit_expr_with_context(arena, callee.0, lambda_depth, context);
                self.visit_expr_with_context(arena, arg.0, lambda_depth, context.in_app_argument());
            }
            poly_expr::Expr::Lambda(_, body) => {
                self.visit_expr_with_context(
                    arena,
                    body.0,
                    lambda_depth + 1,
                    context.enter_lambda(),
                );
            }
            poly_expr::Expr::Tuple(items) => {
                for item in items {
                    self.visit_expr_with_context(arena, item.0, lambda_depth, context);
                }
            }
            poly_expr::Expr::Record { fields, spread } => {
                for (_, value) in fields {
                    self.visit_expr_with_context(arena, value.0, lambda_depth, context);
                }
                match spread {
                    poly_expr::RecordSpread::Head(expr) | poly_expr::RecordSpread::Tail(expr) => {
                        self.visit_expr_with_context(arena, expr.0, lambda_depth, context);
                    }
                    poly_expr::RecordSpread::None => {}
                }
            }
            poly_expr::Expr::PolyVariant(_, payloads) => {
                for payload in payloads {
                    self.visit_expr_with_context(arena, payload.0, lambda_depth, context);
                }
            }
            poly_expr::Expr::Select(base, _) => {
                self.visit_expr_with_context(arena, base.0, lambda_depth, context);
            }
            poly_expr::Expr::Case(scrutinee, arms) => {
                self.visit_expr_with_context(arena, scrutinee.0, lambda_depth, context);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr_with_context(arena, guard.0, lambda_depth, context);
                    }
                    self.visit_expr_with_context(arena, arm.body.0, lambda_depth, context);
                }
            }
            poly_expr::Expr::Catch(body, arms) => {
                let handled_paths = arms
                    .iter()
                    .filter_map(|arm| {
                        arm.operation
                            .as_ref()
                            .map(|operation| operation.path.clone())
                    })
                    .collect::<Vec<_>>();
                self.active_handlers.push(RuntimeEvidenceActiveHandler {
                    handler_expr: expr,
                    lambda_depth,
                    handled_paths,
                });
                self.visit_expr_with_context(arena, body.0, lambda_depth, context);
                self.active_handlers.pop();

                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr_with_context(arena, guard.0, lambda_depth, context);
                    }
                    self.visit_expr_with_context(arena, arm.body.0, lambda_depth, context);
                }
            }
            poly_expr::Expr::Block(stmts, tail) => {
                for stmt in stmts {
                    self.visit_stmt_with_context(arena, stmt, lambda_depth, context);
                }
                if let Some(tail) = tail {
                    self.visit_expr_with_context(arena, tail.0, lambda_depth, context);
                }
            }
        }
    }

    fn visit_stmt_with_context(
        &mut self,
        arena: &poly_expr::Arena,
        stmt: &poly_expr::Stmt,
        lambda_depth: u32,
        context: StaticRouteVisitContext,
    ) {
        match stmt {
            poly_expr::Stmt::Let(_, _, expr) | poly_expr::Stmt::Expr(expr) => {
                self.visit_expr_with_context(arena, expr.0, lambda_depth, context);
            }
            poly_expr::Stmt::Module(_, stmts) => {
                for stmt in stmts {
                    self.visit_stmt_with_context(arena, stmt, lambda_depth, context);
                }
            }
        }
    }

    fn record_operation(
        &mut self,
        operation: RuntimeEvidenceOperationCallSite,
        lambda_depth: u32,
        hygiene_boundary: bool,
    ) {
        self.operation_lambda_depths
            .insert(operation.operation_expr, lambda_depth);
        self.operation_hygiene_barriers
            .insert(operation.operation_expr, hygiene_boundary);
        let Some(handler) = self.active_handlers.iter().rev().find(|handler| {
            handler.lambda_depth == lambda_depth
                && handler
                    .handled_paths
                    .iter()
                    .any(|path| path == &operation.family)
        }) else {
            return;
        };
        let resolution = RuntimeEvidenceStaticRouteResolution::StaticHandler {
            handler_expr: handler.handler_expr,
        };
        self.routes.insert(
            operation.operation_expr,
            RuntimeEvidenceStaticRoute {
                operation_expr: operation.operation_expr,
                apply: operation.apply,
                callee: operation.callee,
                operation_def: operation.operation_def,
                family: operation.family,
                resolution,
            },
        );
    }

    fn record_call_edge(&mut self, app: RuntimeEvidenceAppCallSite, lambda_depth: u32) {
        self.call_edges.push(RuntimeEvidenceCallEdge {
            caller_task: self.task_index,
            callee_instance: app.callee_instance,
            site_lambda_depth: lambda_depth,
            applied_lambda_depth: app.applied_lambda_depth,
            delayed_boundary: app.delayed_boundary,
            active_handlers: self
                .active_handlers
                .iter()
                .filter(|handler| handler.lambda_depth == lambda_depth)
                .cloned()
                .collect(),
        });
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct StaticRouteVisitContext {
    hygiene_boundary: bool,
    app_argument_context: bool,
}

impl StaticRouteVisitContext {
    fn in_app_argument(self) -> Self {
        Self {
            app_argument_context: true,
            ..self
        }
    }

    fn enter_lambda(self) -> Self {
        Self {
            // A lambda flowing through an application argument is a callback-shaped boundary:
            // this stage has only direct callee edges, so catch context cannot be inherited
            // through the callback invocation site.
            hygiene_boundary: self.hygiene_boundary || self.app_argument_context,
            app_argument_context: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeEvidenceOperationCallSite {
    operation_expr: u32,
    apply: u32,
    callee: u32,
    operation_def: u32,
    family: Vec<String>,
    lambda_depth: Option<u32>,
    provider_env_dependent: bool,
    hygiene_barrier: bool,
}

#[derive(Debug, Clone)]
struct StaticRouteTaskAnalysis {
    owner: usize,
    operations: Vec<RuntimeEvidenceOperationCallSite>,
    l1_routes: BTreeMap<u32, RuntimeEvidenceStaticRoute>,
    call_edges: Vec<RuntimeEvidenceCallEdge>,
}

#[derive(Debug, Clone, Copy)]
struct RuntimeEvidenceAppCallSite {
    callee_instance: u32,
    applied_lambda_depth: u32,
    delayed_boundary: bool,
}

#[derive(Debug, Clone)]
struct RuntimeEvidenceCallEdge {
    caller_task: usize,
    callee_instance: u32,
    site_lambda_depth: u32,
    applied_lambda_depth: u32,
    delayed_boundary: bool,
    active_handlers: Vec<RuntimeEvidenceActiveHandler>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeEvidenceActiveHandler {
    handler_expr: u32,
    lambda_depth: u32,
    handled_paths: Vec<Vec<String>>,
}

struct StaticRouteProgramIndex {
    instances: Vec<(u32, Type, u32)>,
}

impl StaticRouteProgramIndex {
    fn new(program: &Program) -> Self {
        let instances = program
            .instances
            .iter()
            .map(|instance| match instance.source {
                mono::InstanceSource::Def(def) => {
                    (def.0, instance.signature.ty.clone(), instance.id.0)
                }
            })
            .collect();
        Self { instances }
    }

    fn instance_for_callee(
        &self,
        arena: &poly_expr::Arena,
        callee: poly_expr::ExprId,
        ref_signatures: &HashMap<u32, &Type>,
    ) -> Option<u32> {
        let poly_expr::Expr::Var(ref_id) = arena.expr(callee) else {
            return None;
        };
        let def = arena.ref_target(*ref_id)?;
        let Some(poly_expr::Def::Let { body: Some(_), .. }) = arena.defs.get(def) else {
            return None;
        };
        let signature = *ref_signatures.get(&callee.0)?;
        let signature = close_resolved_runtime_surface(signature.clone(), TypeSlotKind::Value);
        self.instances
            .iter()
            .find(|(instance_def, instance_ty, _)| {
                *instance_def == def.0 && instance_ty == &signature
            })
            .map(|(_, _, instance)| *instance)
    }
}

struct StaticRouteL2Resolver<'a> {
    host_manifest: Option<&'a poly::host_manifest::HostActManifest>,
    analyses: Vec<StaticRouteTaskAnalysis>,
    instance_tasks: HashMap<u32, usize>,
    task_sccs: Vec<usize>,
    scc_tasks: Vec<Vec<usize>>,
    topo_order: Vec<usize>,
}

impl<'a> StaticRouteL2Resolver<'a> {
    fn new(
        host_manifest: Option<&'a poly::host_manifest::HostActManifest>,
        tasks: &[RuntimeEvidenceTask],
        analyses: Vec<StaticRouteTaskAnalysis>,
    ) -> Self {
        let instance_tasks = tasks
            .iter()
            .enumerate()
            .filter_map(|(task_index, task)| match task.owner {
                RuntimeEvidenceTaskOwner::InstanceBody { instance, .. } => {
                    Some((instance, task_index))
                }
                RuntimeEvidenceTaskOwner::RootExpr { .. } => None,
            })
            .collect::<HashMap<_, _>>();
        let graph_edges = analyses
            .iter()
            .flat_map(|analysis| {
                analysis.call_edges.iter().filter_map(|edge| {
                    instance_tasks
                        .get(&edge.callee_instance)
                        .copied()
                        .map(|target| (edge.caller_task, target))
                })
            })
            .collect::<Vec<_>>();
        let sccs = StaticRouteSccs::new(tasks.len(), &graph_edges);
        Self {
            host_manifest,
            analyses,
            instance_tasks,
            task_sccs: sccs.task_sccs,
            scc_tasks: sccs.scc_tasks,
            topo_order: sccs.topo_order,
        }
    }

    fn finish(self) -> Vec<RuntimeEvidenceStaticRoute> {
        let contexts = self.propagate_contexts();
        let mut routes = Vec::new();
        for analysis in &self.analyses {
            let task_context = &contexts[self.task_sccs[analysis.owner]];
            for operation in &analysis.operations {
                if let Some(route) = analysis.l1_routes.get(&operation.operation_expr) {
                    routes.push(route.clone());
                    continue;
                }
                let resolution = self.resolve_operation_from_context(task_context, operation);
                routes.push(RuntimeEvidenceStaticRoute {
                    operation_expr: operation.operation_expr,
                    apply: operation.apply,
                    callee: operation.callee,
                    operation_def: operation.operation_def,
                    family: operation.family.clone(),
                    resolution,
                });
            }
        }
        routes
    }

    fn propagate_contexts(&self) -> Vec<StaticRouteContextMap> {
        let mut contexts = vec![StaticRouteContextMap::default(); self.scc_tasks.len()];
        for scc in &self.topo_order {
            let internal_edges = self.edges_from_scc(*scc);
            for edge in internal_edges.iter().filter(|edge| {
                self.instance_tasks
                    .get(&edge.callee_instance)
                    .is_some_and(|target| self.task_sccs[*target] == *scc)
            }) {
                let edge_context = context_for_edge(&contexts[*scc], edge);
                contexts[*scc].merge(edge_context);
            }

            let outgoing_edges = self.edges_from_scc(*scc);
            for edge in outgoing_edges {
                let Some(target_task) = self.instance_tasks.get(&edge.callee_instance).copied()
                else {
                    continue;
                };
                let target_scc = self.task_sccs[target_task];
                if target_scc == *scc {
                    continue;
                }
                let edge_context = context_for_edge(&contexts[*scc], edge);
                contexts[target_scc].merge(edge_context);
            }
        }
        contexts
    }

    fn edges_from_scc(&self, scc: usize) -> Vec<&RuntimeEvidenceCallEdge> {
        self.scc_tasks[scc]
            .iter()
            .flat_map(|task| self.analyses[*task].call_edges.iter())
            .collect()
    }

    fn resolve_operation_from_context(
        &self,
        context: &StaticRouteContextMap,
        operation: &RuntimeEvidenceOperationCallSite,
    ) -> RuntimeEvidenceStaticRouteResolution {
        let lambda_depth = operation.lambda_depth.unwrap_or(u32::MAX);
        let handlers = context.handlers_for(&operation.family, lambda_depth);
        match handlers.as_slice() {
            [handler_expr] => RuntimeEvidenceStaticRouteResolution::StaticHandler {
                handler_expr: *handler_expr,
            },
            [] => dynamic_static_route_resolution(self.host_manifest, operation),
            _ => RuntimeEvidenceStaticRouteResolution::Dynamic(
                RuntimeEvidenceStaticRouteDynamicReason::MultipleCandidates,
            ),
        }
    }
}

#[derive(Debug, Clone, Default)]
struct StaticRouteContextMap {
    by_family: BTreeMap<Vec<String>, BTreeMap<u32, u32>>,
}

impl StaticRouteContextMap {
    fn insert(&mut self, family: Vec<String>, handler_expr: u32, max_lambda_depth: u32) {
        let entry = self.by_family.entry(family).or_default();
        entry
            .entry(handler_expr)
            .and_modify(|existing| *existing = (*existing).max(max_lambda_depth))
            .or_insert(max_lambda_depth);
    }

    fn merge(&mut self, other: StaticRouteContextMap) {
        for (family, handlers) in other.by_family {
            for (handler_expr, max_lambda_depth) in handlers {
                self.insert(family.clone(), handler_expr, max_lambda_depth);
            }
        }
    }

    fn handlers_for(&self, family: &[String], lambda_depth: u32) -> Vec<u32> {
        self.by_family
            .get(family)
            .map(|handlers| {
                handlers
                    .iter()
                    .filter_map(|(handler, max_depth)| {
                        (*max_depth >= lambda_depth).then_some(*handler)
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn propagated_at_depth(&self, site_lambda_depth: u32, applied_lambda_depth: u32) -> Self {
        let mut propagated = Self::default();
        for (family, handlers) in &self.by_family {
            for (handler, max_depth) in handlers {
                if *max_depth >= site_lambda_depth {
                    propagated.insert(family.clone(), *handler, applied_lambda_depth);
                }
            }
        }
        propagated
    }
}

fn context_for_edge(
    inherited: &StaticRouteContextMap,
    edge: &RuntimeEvidenceCallEdge,
) -> StaticRouteContextMap {
    if edge.delayed_boundary {
        return StaticRouteContextMap::default();
    }
    let mut context =
        inherited.propagated_at_depth(edge.site_lambda_depth, edge.applied_lambda_depth);
    let local = local_handler_context(edge);
    for family in local.by_family.keys() {
        context.by_family.remove(family);
    }
    context.merge(local);
    context
}

fn local_handler_context(edge: &RuntimeEvidenceCallEdge) -> StaticRouteContextMap {
    let mut context = StaticRouteContextMap::default();
    let mut seen = BTreeSet::new();
    for handler in edge.active_handlers.iter().rev() {
        for family in &handler.handled_paths {
            if seen.insert(family.clone()) {
                context.insert(
                    family.clone(),
                    handler.handler_expr,
                    edge.applied_lambda_depth,
                );
            }
        }
    }
    context
}

struct StaticRouteSccs {
    task_sccs: Vec<usize>,
    scc_tasks: Vec<Vec<usize>>,
    topo_order: Vec<usize>,
}

impl StaticRouteSccs {
    fn new(task_count: usize, edges: &[(usize, usize)]) -> Self {
        let tarjan = StaticRouteTarjan::new(task_count, edges).finish();
        let mut scc_edge_sets = vec![BTreeSet::new(); tarjan.scc_tasks.len()];
        for (source, target) in edges {
            let source_scc = tarjan.task_sccs[*source];
            let target_scc = tarjan.task_sccs[*target];
            if source_scc != target_scc {
                scc_edge_sets[source_scc].insert(target_scc);
            }
        }
        let scc_edges = scc_edge_sets
            .into_iter()
            .map(|edges| edges.into_iter().collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let topo_order = topo_order_for_sccs(&scc_edges);
        Self {
            task_sccs: tarjan.task_sccs,
            scc_tasks: tarjan.scc_tasks,
            topo_order,
        }
    }
}

struct StaticRouteTarjan<'a> {
    edges: &'a [(usize, usize)],
    next_index: usize,
    stack: Vec<usize>,
    on_stack: Vec<bool>,
    indices: Vec<Option<usize>>,
    lowlinks: Vec<usize>,
    task_sccs: Vec<usize>,
    scc_tasks: Vec<Vec<usize>>,
}

impl<'a> StaticRouteTarjan<'a> {
    fn new(task_count: usize, edges: &'a [(usize, usize)]) -> Self {
        Self {
            edges,
            next_index: 0,
            stack: Vec::new(),
            on_stack: vec![false; task_count],
            indices: vec![None; task_count],
            lowlinks: vec![0; task_count],
            task_sccs: vec![usize::MAX; task_count],
            scc_tasks: Vec::new(),
        }
    }

    fn finish(mut self) -> StaticRouteTarjanOutput {
        for task in 0..self.indices.len() {
            if self.indices[task].is_none() {
                self.visit(task);
            }
        }
        StaticRouteTarjanOutput {
            task_sccs: self.task_sccs,
            scc_tasks: self.scc_tasks,
        }
    }

    fn visit(&mut self, task: usize) {
        let index = self.next_index;
        self.next_index += 1;
        self.indices[task] = Some(index);
        self.lowlinks[task] = index;
        self.stack.push(task);
        self.on_stack[task] = true;

        for target in self.targets_for(task) {
            if self.indices[target].is_none() {
                self.visit(target);
                self.lowlinks[task] = self.lowlinks[task].min(self.lowlinks[target]);
            } else if self.on_stack[target] {
                self.lowlinks[task] = self.lowlinks[task].min(self.indices[target].unwrap());
            }
        }

        if self.lowlinks[task] == self.indices[task].unwrap() {
            let scc = self.scc_tasks.len();
            let mut tasks = Vec::new();
            loop {
                let member = self.stack.pop().expect("tarjan stack should contain root");
                self.on_stack[member] = false;
                self.task_sccs[member] = scc;
                tasks.push(member);
                if member == task {
                    break;
                }
            }
            tasks.sort_unstable();
            self.scc_tasks.push(tasks);
        }
    }

    fn targets_for(&self, task: usize) -> Vec<usize> {
        self.edges
            .iter()
            .filter_map(|(source, target)| (*source == task).then_some(*target))
            .collect()
    }
}

struct StaticRouteTarjanOutput {
    task_sccs: Vec<usize>,
    scc_tasks: Vec<Vec<usize>>,
}

fn topo_order_for_sccs(edges: &[Vec<usize>]) -> Vec<usize> {
    let mut indegree = vec![0usize; edges.len()];
    for targets in edges {
        for target in targets {
            indegree[*target] += 1;
        }
    }
    let mut queue = indegree
        .iter()
        .enumerate()
        .filter_map(|(scc, degree)| (*degree == 0).then_some(scc))
        .collect::<VecDeque<_>>();
    let mut order = Vec::new();
    while let Some(scc) = queue.pop_front() {
        order.push(scc);
        for target in &edges[scc] {
            indegree[*target] -= 1;
            if indegree[*target] == 0 {
                queue.push_back(*target);
            }
        }
    }
    order
}

fn dynamic_static_route_resolution(
    host_manifest: Option<&poly::host_manifest::HostActManifest>,
    operation: &RuntimeEvidenceOperationCallSite,
) -> RuntimeEvidenceStaticRouteResolution {
    if host_manifest_has_known_act(host_manifest, &operation.family) {
        RuntimeEvidenceStaticRouteResolution::Dynamic(
            RuntimeEvidenceStaticRouteDynamicReason::HostEscape,
        )
    } else if operation.provider_env_dependent {
        RuntimeEvidenceStaticRouteResolution::Dynamic(
            RuntimeEvidenceStaticRouteDynamicReason::ProviderEnvDependent,
        )
    } else if operation.hygiene_barrier {
        RuntimeEvidenceStaticRouteResolution::Dynamic(
            RuntimeEvidenceStaticRouteDynamicReason::HygieneBarrier,
        )
    } else {
        RuntimeEvidenceStaticRouteResolution::Dynamic(
            RuntimeEvidenceStaticRouteDynamicReason::Unclassified,
        )
    }
}

fn host_manifest_has_known_act(
    host_manifest: Option<&poly::host_manifest::HostActManifest>,
    operation_path: &[String],
) -> bool {
    host_manifest.is_some_and(|host_manifest| {
        host_manifest
            .acts
            .iter()
            .any(|act| operation_path.starts_with(&act.path))
    })
}

pub fn format_runtime_evidence_surface(surface: &RuntimeEvidenceSurface) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "runtime evidence tasks [{}]", surface.tasks.len());
    if let Some(host_manifest) = &surface.host_manifest {
        let _ = writeln!(
            out,
            "host act manifest acts [{}] operations [{}] hash {}",
            host_manifest.acts.len(),
            host_manifest.operations.len(),
            host_manifest.hash.0
        );
    }
    if !surface.known_state_handlers.is_empty() {
        let _ = writeln!(
            out,
            "known state handlers [{}]",
            surface.known_state_handlers.len()
        );
        for handler in &surface.known_state_handlers {
            let _ = writeln!(
                out,
                "  sv{} {} source {} continuation {}",
                handler.synthetic_var,
                handler.effect_path.join("::"),
                format_known_state_handler_source(handler.source),
                format_known_state_continuation(handler.continuation)
            );
        }
    }
    if !surface.known_state_accesses.is_empty() {
        let _ = writeln!(
            out,
            "known state accesses [{}]",
            surface.known_state_accesses.len()
        );
        for access in &surface.known_state_accesses {
            let _ = writeln!(
                out,
                "  sv{} e{} apply e{} callee e{} arg e{} d{} {}",
                access.synthetic_var,
                access.operation_expr,
                access.apply,
                access.callee,
                access.arg,
                access.operation_def,
                format_known_state_access_role(access.role)
            );
        }
    }
    if !surface.static_routes.is_empty() {
        let _ = writeln!(out, "static routes [{}]", surface.static_routes.len());
        for route in &surface.static_routes {
            let _ = writeln!(
                out,
                "  e{} apply e{} callee e{} d{} {} -> {}",
                route.operation_expr,
                route.apply,
                route.callee,
                route.operation_def,
                route.family.join("::"),
                format_static_route_resolution(&route.resolution)
            );
        }
    }
    for task in &surface.tasks {
        let _ = writeln!(out, "{}", format_task_header(task));
        format_graph_summary(&mut out, &task.graph);
        format_nodes(&mut out, &task.nodes);
        format_sites(&mut out, &task.sites);
        for expr in &task.expr_types {
            let consumer = expr
                .consumer
                .as_ref()
                .map(mono::dump::dump_type)
                .unwrap_or_else(|| "_".to_string());
            let _ = writeln!(
                out,
                "  expr e{} actual {} consumer {} actual_slots [{}] consumer_slots [{}] stack_weights {}",
                expr.expr,
                mono::dump::dump_type(&expr.actual),
                consumer,
                format_slot_ids(&expr.actual_slots),
                format_slot_ids(&expr.consumer_slots),
                expr.stack_weights.len()
            );
            format_stack_weights(&mut out, &expr.stack_weights);
        }
        for signature in &task.ref_signatures {
            let _ = writeln!(
                out,
                "  ref e{} signature {} stack_weights {}",
                signature.expr,
                mono::dump::dump_type(&signature.ty),
                signature.stack_weights.len()
            );
            format_stack_weights(&mut out, &signature.stack_weights);
        }
        for signature in &task.select_signatures {
            let _ = writeln!(
                out,
                "  select e{} signature {} stack_weights {}",
                signature.expr,
                mono::dump::dump_type(&signature.ty),
                signature.stack_weights.len()
            );
            format_stack_weights(&mut out, &signature.stack_weights);
        }
        for signature in &task.pat_ref_signatures {
            let _ = writeln!(
                out,
                "  pat p{} signature {} stack_weights {}",
                signature.pat,
                mono::dump::dump_type(&signature.ty),
                signature.stack_weights.len()
            );
            format_stack_weights(&mut out, &signature.stack_weights);
        }
        for resolution in &task.typeclass_resolutions {
            let _ = writeln!(
                out,
                "  typeclass e{} -> d{} signature {} stack_weights {}",
                resolution.expr,
                resolution.implementation,
                mono::dump::dump_type(&resolution.signature),
                resolution.stack_weights.len()
            );
            format_stack_weights(&mut out, &resolution.stack_weights);
        }
        if !task.raw_thunk_computations.is_empty() {
            let raw = task
                .raw_thunk_computations
                .iter()
                .map(|expr| format!("e{expr}"))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(out, "  raw thunk computations [{raw}]");
        }
    }
    out
}

fn format_known_state_handler_source(
    source: RuntimeEvidenceKnownStateHandlerSource,
) -> &'static str {
    match source {
        RuntimeEvidenceKnownStateHandlerSource::CompilerLocalVar => "compiler-local-var",
    }
}

fn format_known_state_continuation(
    continuation: RuntimeEvidenceKnownStateContinuationSemantics,
) -> &'static str {
    match continuation {
        RuntimeEvidenceKnownStateContinuationSemantics::SnapshotFork => "snapshot-fork",
    }
}

fn format_known_state_access_role(role: RuntimeEvidenceKnownStateAccessRole) -> &'static str {
    match role {
        RuntimeEvidenceKnownStateAccessRole::StateGet => "state-get",
        RuntimeEvidenceKnownStateAccessRole::StateSet => "state-set",
    }
}

fn format_static_route_resolution(resolution: &RuntimeEvidenceStaticRouteResolution) -> String {
    match resolution {
        RuntimeEvidenceStaticRouteResolution::StaticHandler { handler_expr } => {
            format!("static-handler e{handler_expr}")
        }
        RuntimeEvidenceStaticRouteResolution::Dynamic(reason) => {
            format!("dynamic-{}", format_static_route_dynamic_reason(*reason))
        }
    }
}

fn format_static_route_dynamic_reason(
    reason: RuntimeEvidenceStaticRouteDynamicReason,
) -> &'static str {
    match reason {
        RuntimeEvidenceStaticRouteDynamicReason::OpenRow => "open-row",
        RuntimeEvidenceStaticRouteDynamicReason::MultipleCandidates => "multiple-candidates",
        RuntimeEvidenceStaticRouteDynamicReason::HygieneBarrier => "hygiene-barrier",
        RuntimeEvidenceStaticRouteDynamicReason::ProviderEnvDependent => "provider-env",
        RuntimeEvidenceStaticRouteDynamicReason::DelayedBoundary => "delayed-boundary",
        RuntimeEvidenceStaticRouteDynamicReason::HostEscape => "host-escape",
        RuntimeEvidenceStaticRouteDynamicReason::Unclassified => "unclassified",
    }
}

fn format_nodes(out: &mut String, nodes: &[RuntimeEvidenceNode]) {
    if nodes.is_empty() {
        return;
    }
    let _ = writeln!(out, "  nodes {}", nodes.len());
    for node in nodes {
        let _ = writeln!(
            out,
            "    n{} e{} {} slots [{}] weighted [{}] subtractions [{}]",
            node.id,
            node.expr,
            format_node_kind(&node.kind),
            format_slot_ids(&node.slots),
            format_slot_ids(&node.weighted_slots),
            format_slot_ids(&node.effect_subtraction_slots),
        );
        if !node.evidence_refs.is_empty() {
            let refs = node
                .evidence_refs
                .iter()
                .map(format_node_evidence_ref)
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(out, "      evidence [{refs}]");
        }
    }
}

fn format_node_kind(kind: &RuntimeEvidenceNodeKind) -> String {
    match kind {
        RuntimeEvidenceNodeKind::OperationValue { def, path } => {
            format!("operation-value d{def} {}", path.join("::"))
        }
        RuntimeEvidenceNodeKind::OperationCall {
            callee,
            arg,
            def,
            path,
        } => format!(
            "operation-call callee e{callee} arg e{arg} d{def} {}",
            path.join("::")
        ),
        RuntimeEvidenceNodeKind::Handler {
            body,
            handled_paths,
            value_arm_count,
        } => {
            let handled = handled_paths
                .iter()
                .map(|path| path.join("::"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("handler body e{body} handled [{handled}] value_arms {value_arm_count}")
        }
        RuntimeEvidenceNodeKind::Application {
            callee,
            arg,
            argument_contract,
        } => {
            format!("application callee e{callee} arg e{arg} argument_contract {argument_contract}")
        }
        RuntimeEvidenceNodeKind::FunctionValue {
            param,
            body,
            argument_contract,
        } => format!(
            "function-value param p{param} body e{body} argument_contract {argument_contract}"
        ),
        RuntimeEvidenceNodeKind::RefUpdate { reference, value } => {
            format!("ref-update reference e{reference} value e{value}")
        }
    }
}

fn format_node_evidence_ref(reference: &RuntimeEvidenceNodeEvidenceRef) -> String {
    match reference {
        RuntimeEvidenceNodeEvidenceRef::WeightedLower { slot, index } => {
            format!("t{slot}.weighted_lower#{index}")
        }
        RuntimeEvidenceNodeEvidenceRef::WeightedUpper { slot, index } => {
            format!("t{slot}.weighted_upper#{index}")
        }
        RuntimeEvidenceNodeEvidenceRef::WeightedSuccessor {
            slot,
            index,
            target,
        } => format!("t{slot}.weighted_successor#{index}->t{target}"),
        RuntimeEvidenceNodeEvidenceRef::WeightedPredecessor {
            slot,
            index,
            source,
        } => format!("t{slot}.weighted_predecessor#{index}<-t{source}"),
        RuntimeEvidenceNodeEvidenceRef::EffectSubtraction { slot, index } => {
            format!("t{slot}.effect_subtraction#{index}")
        }
    }
}

fn format_graph_summary(out: &mut String, graph: &RuntimeEvidenceGraph) {
    let _ = writeln!(
        out,
        "  graph slots {} value {} effect {} constraints {} weighted_constraints {} weighted_lower {} weighted_upper {} weighted_edges {} effect_subtractions {} row_residuals {}",
        graph.slot_count,
        graph.value_slot_count,
        graph.effect_slot_count,
        graph.queued_constraint_count,
        graph.weighted_constraint_count,
        graph.weighted_lower_count,
        graph.weighted_upper_count,
        graph.weighted_edge_count,
        graph.effect_subtraction_count,
        graph.row_residuals.len(),
    );
    for residual in &graph.row_residuals {
        let retained = residual
            .retained_families
            .iter()
            .map(format_effect_family)
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(
            out,
            "    row residual t{} -> t{} retained [{}] weight {:?}",
            residual.source, residual.residual, retained, residual.weight
        );
    }
    for slot in graph
        .slots
        .iter()
        .filter(|slot| slot.has_runtime_evidence())
    {
        let _ = writeln!(
            out,
            "    slot t{} {:?} lower {} upper {} successors {} predecessors {} weighted_lower {} weighted_upper {} weighted_successors {} weighted_predecessors {} effect_subtractions {}",
            slot.id,
            slot.kind,
            slot.lower_count,
            slot.upper_count,
            slot.successor_count,
            slot.predecessor_count,
            slot.weighted_lower.len(),
            slot.weighted_upper.len(),
            slot.weighted_successors.len(),
            slot.weighted_predecessors.len(),
            slot.effect_subtractions.len(),
        );
        for bound in &slot.weighted_lower {
            let _ = writeln!(
                out,
                "      weighted lower {} lower {:?} upper {:?}",
                mono::dump::dump_type(&bound.ty),
                bound.lower_weight,
                bound.upper_weight
            );
        }
        for bound in &slot.weighted_upper {
            let _ = writeln!(
                out,
                "      weighted upper {} lower {:?} upper {:?}",
                mono::dump::dump_type(&bound.ty),
                bound.lower_weight,
                bound.upper_weight
            );
        }
        for edge in &slot.weighted_successors {
            let _ = writeln!(
                out,
                "      weighted successor t{} lower {:?} upper {:?}",
                edge.slot, edge.lower_weight, edge.upper_weight
            );
        }
        for edge in &slot.weighted_predecessors {
            let _ = writeln!(
                out,
                "      weighted predecessor t{} lower {:?} upper {:?}",
                edge.slot, edge.lower_weight, edge.upper_weight
            );
        }
        for demand in &slot.effect_subtractions {
            let handled = demand
                .handled_items
                .iter()
                .map(mono::dump::dump_type)
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(
                out,
                "      subtract tail {} runtime {} handled [{}]",
                mono::dump::dump_type(&demand.tail),
                mono::dump::dump_type(&demand.runtime_effect),
                handled
            );
        }
    }
}

fn format_sites(out: &mut String, sites: &[RuntimeEvidenceSite]) {
    if sites.is_empty() {
        return;
    }
    let _ = writeln!(out, "  sites {}", sites.len());
    for site in sites {
        let _ = writeln!(out, "    e{} {}", site.expr, format_site_kind(&site.kind));
        if let Some(boundary) = &site.boundary {
            let _ = writeln!(
                out,
                "      boundary actual {} consumer {} function_like {} argument_contract {}",
                mono::dump::dump_type(&boundary.actual),
                mono::dump::dump_type(&boundary.consumer),
                boundary.function_like,
                boundary.argument_contract,
            );
            let _ = writeln!(
                out,
                "      slots actual [{}] consumer [{}]",
                format_slot_ids(&boundary.actual_slots),
                format_slot_ids(&boundary.consumer_slots)
            );
        }
    }
}

fn format_site_kind(kind: &RuntimeEvidenceSiteKind) -> String {
    match kind {
        RuntimeEvidenceSiteKind::OperationValue { def, path } => {
            format!("operation-value d{def} {}", path.join("::"))
        }
        RuntimeEvidenceSiteKind::OperationCall {
            callee,
            arg,
            def,
            path,
        } => format!(
            "operation-call callee e{callee} arg e{arg} d{def} {}",
            path.join("::")
        ),
        RuntimeEvidenceSiteKind::Catch {
            body,
            handled_paths,
            value_arm_count,
        } => {
            let handled = handled_paths
                .iter()
                .map(|path| path.join("::"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("catch body e{body} handled [{handled}] value_arms {value_arm_count}")
        }
        RuntimeEvidenceSiteKind::App {
            callee,
            arg,
            argument_contract,
        } => format!("app callee e{callee} arg e{arg} argument_contract {argument_contract}"),
        RuntimeEvidenceSiteKind::Lambda {
            param,
            body,
            argument_contract,
        } => format!("lambda param p{param} body e{body} argument_contract {argument_contract}"),
        RuntimeEvidenceSiteKind::RefSet { reference, value } => {
            format!("ref-set reference e{reference} value e{value}")
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RuntimeEvidenceTask {
    pub owner: RuntimeEvidenceTaskOwner,
    pub graph: RuntimeEvidenceGraph,
    pub nodes: Vec<RuntimeEvidenceNode>,
    pub sites: Vec<RuntimeEvidenceSite>,
    pub expr_types: Vec<RuntimeEvidenceExprType>,
    pub ref_signatures: Vec<RuntimeEvidenceTypeAtExpr>,
    pub select_signatures: Vec<RuntimeEvidenceTypeAtExpr>,
    pub pat_ref_signatures: Vec<RuntimeEvidenceTypeAtPat>,
    pub typeclass_resolutions: Vec<RuntimeEvidenceTypeclassResolution>,
    pub raw_thunk_computations: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceNode {
    pub id: u32,
    pub expr: u32,
    pub kind: RuntimeEvidenceNodeKind,
    pub slots: Vec<u32>,
    pub weighted_slots: Vec<u32>,
    pub effect_subtraction_slots: Vec<u32>,
    pub evidence_refs: Vec<RuntimeEvidenceNodeEvidenceRef>,
}

impl RuntimeEvidenceNode {
    fn from_site(
        id: u32,
        site: &RuntimeEvidenceSite,
        expr_types: &[RuntimeEvidenceExprType],
        graph: &RuntimeEvidenceGraph,
    ) -> Self {
        let slots = slots_for_site(site, expr_types);
        let weighted_slots = slots
            .iter()
            .copied()
            .filter(|slot| {
                graph
                    .slot(*slot)
                    .is_some_and(RuntimeEvidenceSlot::has_weighted_evidence)
            })
            .collect();
        let effect_subtraction_slots = slots
            .iter()
            .copied()
            .filter(|slot| {
                graph
                    .slot(*slot)
                    .is_some_and(RuntimeEvidenceSlot::has_effect_subtraction_evidence)
            })
            .collect();
        Self {
            id,
            expr: site.expr,
            kind: RuntimeEvidenceNodeKind::from_site_kind(&site.kind),
            evidence_refs: evidence_refs_for_slots(&slots, graph),
            slots,
            weighted_slots,
            effect_subtraction_slots,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceNodeEvidenceRef {
    WeightedLower { slot: u32, index: u32 },
    WeightedUpper { slot: u32, index: u32 },
    WeightedSuccessor { slot: u32, index: u32, target: u32 },
    WeightedPredecessor { slot: u32, index: u32, source: u32 },
    EffectSubtraction { slot: u32, index: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceNodeKind {
    OperationValue {
        def: u32,
        path: Vec<String>,
    },
    OperationCall {
        callee: u32,
        arg: u32,
        def: u32,
        path: Vec<String>,
    },
    Handler {
        body: u32,
        handled_paths: Vec<Vec<String>>,
        value_arm_count: u32,
    },
    Application {
        callee: u32,
        arg: u32,
        argument_contract: bool,
    },
    FunctionValue {
        param: u32,
        body: u32,
        argument_contract: bool,
    },
    RefUpdate {
        reference: u32,
        value: u32,
    },
}

impl RuntimeEvidenceNodeKind {
    fn from_site_kind(kind: &RuntimeEvidenceSiteKind) -> Self {
        match kind {
            RuntimeEvidenceSiteKind::OperationValue { def, path } => Self::OperationValue {
                def: *def,
                path: path.clone(),
            },
            RuntimeEvidenceSiteKind::OperationCall {
                callee,
                arg,
                def,
                path,
            } => Self::OperationCall {
                callee: *callee,
                arg: *arg,
                def: *def,
                path: path.clone(),
            },
            RuntimeEvidenceSiteKind::Catch {
                body,
                handled_paths,
                value_arm_count,
            } => Self::Handler {
                body: *body,
                handled_paths: handled_paths.clone(),
                value_arm_count: *value_arm_count,
            },
            RuntimeEvidenceSiteKind::App {
                callee,
                arg,
                argument_contract,
            } => Self::Application {
                callee: *callee,
                arg: *arg,
                argument_contract: *argument_contract,
            },
            RuntimeEvidenceSiteKind::Lambda {
                param,
                body,
                argument_contract,
            } => Self::FunctionValue {
                param: *param,
                body: *body,
                argument_contract: *argument_contract,
            },
            RuntimeEvidenceSiteKind::RefSet { reference, value } => Self::RefUpdate {
                reference: *reference,
                value: *value,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceSite {
    pub expr: u32,
    pub kind: RuntimeEvidenceSiteKind,
    pub boundary: Option<RuntimeEvidenceBoundaryCandidate>,
}

impl RuntimeEvidenceSite {
    fn from_expr(
        arena: &poly_expr::Arena,
        expr: poly_expr::ExprId,
        ty: &SolvedExprType,
    ) -> Option<Self> {
        let kind = match arena.expr(expr) {
            poly_expr::Expr::Var(ref_id) => {
                let (def, path) = effect_operation_for_ref(arena, *ref_id)?;
                RuntimeEvidenceSiteKind::OperationValue { def: def.0, path }
            }
            poly_expr::Expr::App(callee, arg) => {
                if let poly_expr::Expr::Var(ref_id) = arena.expr(*callee)
                    && let Some((def, path)) = effect_operation_for_ref(arena, *ref_id)
                {
                    RuntimeEvidenceSiteKind::OperationCall {
                        callee: callee.0,
                        arg: arg.0,
                        def: def.0,
                        path,
                    }
                } else {
                    RuntimeEvidenceSiteKind::App {
                        callee: callee.0,
                        arg: arg.0,
                        argument_contract: callee_has_argument_effect_contract(arena, *callee),
                    }
                }
            }
            poly_expr::Expr::Catch(body, arms) => {
                let handled_paths = arms
                    .iter()
                    .filter_map(|arm| {
                        arm.operation
                            .as_ref()
                            .map(|operation| operation.path.clone())
                    })
                    .collect::<Vec<_>>();
                let value_arm_count =
                    arms.iter().filter(|arm| arm.operation.is_none()).count() as u32;
                RuntimeEvidenceSiteKind::Catch {
                    body: body.0,
                    handled_paths,
                    value_arm_count,
                }
            }
            poly_expr::Expr::Lambda(param, body) => RuntimeEvidenceSiteKind::Lambda {
                param: param.0,
                body: body.0,
                argument_contract: lambda_param_has_effect_contract(arena, *param),
            },
            poly_expr::Expr::RefSet(reference, value) => RuntimeEvidenceSiteKind::RefSet {
                reference: reference.0,
                value: value.0,
            },
            _ => return None,
        };
        Some(Self {
            expr: expr.0,
            boundary: RuntimeEvidenceBoundaryCandidate::from_expr_type(arena, expr, ty),
            kind,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceSiteKind {
    OperationValue {
        def: u32,
        path: Vec<String>,
    },
    OperationCall {
        callee: u32,
        arg: u32,
        def: u32,
        path: Vec<String>,
    },
    Catch {
        body: u32,
        handled_paths: Vec<Vec<String>>,
        value_arm_count: u32,
    },
    App {
        callee: u32,
        arg: u32,
        argument_contract: bool,
    },
    Lambda {
        param: u32,
        body: u32,
        argument_contract: bool,
    },
    RefSet {
        reference: u32,
        value: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceBoundaryCandidate {
    pub actual: Type,
    pub consumer: Type,
    pub actual_slots: Vec<u32>,
    pub consumer_slots: Vec<u32>,
    pub function_like: bool,
    pub argument_contract: bool,
}

impl RuntimeEvidenceBoundaryCandidate {
    fn from_expr_type(
        arena: &poly_expr::Arena,
        expr: poly_expr::ExprId,
        ty: &SolvedExprType,
    ) -> Option<Self> {
        let consumer = ty.consumer.as_ref()?;
        let argument_contract = expr_has_effect_argument_contract(arena, expr);
        let function_like = type_is_function_like(&ty.actual) || type_is_function_like(consumer);
        if !argument_contract && !function_like {
            return None;
        }
        Some(Self {
            actual: ty.actual.clone(),
            consumer: consumer.clone(),
            actual_slots: ty.actual_slots.clone(),
            consumer_slots: ty.consumer_slots.clone(),
            function_like,
            argument_contract,
        })
    }
}

fn effect_operation_for_ref(
    arena: &poly_expr::Arena,
    ref_id: poly_expr::RefId,
) -> Option<(poly_expr::DefId, Vec<String>)> {
    let def = arena.ref_target(ref_id)?;
    let operation = arena.effect_operations.get(&def)?;
    Some((def, operation.path.clone()))
}

fn expr_has_effect_argument_contract(arena: &poly_expr::Arena, expr: poly_expr::ExprId) -> bool {
    match arena.expr(expr) {
        poly_expr::Expr::Lambda(param, _) => lambda_param_has_effect_contract(arena, *param),
        poly_expr::Expr::Var(ref_id) => {
            let Some(def) = arena.ref_target(*ref_id) else {
                return false;
            };
            def_lambda_param_has_effect_contract(arena, def, 0)
        }
        _ => false,
    }
}

fn callee_has_argument_effect_contract(
    arena: &poly_expr::Arena,
    callee: poly_expr::ExprId,
) -> bool {
    let (head, index) = call_spine_head_and_arg_index(arena, callee);
    match arena.expr(head) {
        poly_expr::Expr::Var(ref_id) => {
            let Some(def) = arena.ref_target(*ref_id) else {
                return false;
            };
            def_lambda_param_has_effect_contract(arena, def, index)
        }
        poly_expr::Expr::Lambda(param, body) => {
            lambda_chain_param_has_effect_contract(arena, *param, *body, index)
        }
        _ => false,
    }
}

fn call_spine_head_and_arg_index(
    arena: &poly_expr::Arena,
    mut callee: poly_expr::ExprId,
) -> (poly_expr::ExprId, usize) {
    let mut index = 0;
    while let poly_expr::Expr::App(next, _) = arena.expr(callee) {
        index += 1;
        callee = *next;
    }
    (callee, index)
}

fn def_lambda_param_has_effect_contract(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    index: usize,
) -> bool {
    let Some(poly_expr::Def::Let {
        body: Some(body), ..
    }) = arena.defs.get(def)
    else {
        return false;
    };
    let poly_expr::Expr::Lambda(param, body) = arena.expr(*body) else {
        return false;
    };
    lambda_chain_param_has_effect_contract(arena, *param, *body, index)
}

fn lambda_chain_param_has_effect_contract(
    arena: &poly_expr::Arena,
    param: poly_expr::PatId,
    body: poly_expr::ExprId,
    index: usize,
) -> bool {
    if index == 0 {
        return lambda_param_has_effect_contract(arena, param);
    }
    let poly_expr::Expr::Lambda(param, body) = arena.expr(body) else {
        return false;
    };
    lambda_chain_param_has_effect_contract(arena, *param, *body, index - 1)
}

fn lambda_param_has_effect_contract(arena: &poly_expr::Arena, pat: poly_expr::PatId) -> bool {
    let Some(def) = lambda_param_def(arena, pat) else {
        return false;
    };
    arena.arg_effect_contracts.contains_key(&def)
}

fn lambda_param_def(arena: &poly_expr::Arena, pat: poly_expr::PatId) -> Option<poly_expr::DefId> {
    match arena.pat(pat) {
        poly_expr::Pat::Var(def) => Some(*def),
        poly_expr::Pat::As(_, def) => Some(*def),
        _ => None,
    }
}

fn type_is_function_like(ty: &Type) -> bool {
    match ty {
        Type::Fun { .. } => true,
        Type::Stack { inner, .. } => type_is_function_like(inner),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_is_function_like(left) || type_is_function_like(right)
        }
        _ => false,
    }
}

impl RuntimeEvidenceTask {
    fn from_solved(
        arena: &poly_expr::Arena,
        owner: RuntimeEvidenceTaskOwner,
        solved: &SolvedTask,
    ) -> Self {
        let mut sites = solved
            .exprs
            .iter()
            .filter_map(|(expr, ty)| RuntimeEvidenceSite::from_expr(arena, *expr, ty))
            .collect::<Vec<_>>();
        sites.sort_by_key(|site| site.expr);

        let mut expr_types = solved
            .exprs
            .iter()
            .map(|(expr, ty)| RuntimeEvidenceExprType::new(*expr, ty))
            .collect::<Vec<_>>();
        expr_types.sort_by_key(|item| item.expr);
        let nodes = sites
            .iter()
            .enumerate()
            .map(|(id, site)| {
                RuntimeEvidenceNode::from_site(
                    id as u32,
                    site,
                    &expr_types,
                    &solved.runtime_evidence_graph,
                )
            })
            .collect();

        let mut ref_signatures = type_at_exprs(&solved.ref_signatures);
        let mut select_signatures = type_at_exprs(&solved.select_signatures);
        let mut pat_ref_signatures = solved
            .pat_ref_signatures
            .iter()
            .map(|(pat, ty)| RuntimeEvidenceTypeAtPat::new(*pat, ty))
            .collect::<Vec<_>>();
        let mut typeclass_resolutions = solved
            .typeclass_resolutions
            .iter()
            .map(|(expr, resolution)| RuntimeEvidenceTypeclassResolution::new(*expr, resolution))
            .collect::<Vec<_>>();
        let mut raw_thunk_computations = solved
            .raw_thunk_computations
            .iter()
            .map(|expr| expr.0)
            .collect::<Vec<_>>();

        ref_signatures.sort_by_key(|item| item.expr);
        select_signatures.sort_by_key(|item| item.expr);
        pat_ref_signatures.sort_by_key(|item| item.pat);
        typeclass_resolutions.sort_by_key(|item| item.expr);
        raw_thunk_computations.sort_unstable();

        Self {
            owner,
            graph: solved.runtime_evidence_graph.clone(),
            nodes,
            sites,
            expr_types,
            ref_signatures,
            select_signatures,
            pat_ref_signatures,
            typeclass_resolutions,
            raw_thunk_computations,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceGraph {
    pub slot_count: u32,
    pub value_slot_count: u32,
    pub effect_slot_count: u32,
    pub queued_constraint_count: u32,
    pub weighted_constraint_count: u32,
    pub weighted_lower_count: u32,
    pub weighted_upper_count: u32,
    pub weighted_edge_count: u32,
    pub effect_subtraction_count: u32,
    pub row_residuals: Vec<RuntimeEvidenceRowResidual>,
    pub slots: Vec<RuntimeEvidenceSlot>,
}

impl RuntimeEvidenceGraph {
    pub(super) fn from_type_graph(graph: &TypeGraph<'_>) -> Self {
        let mut value_slot_count = 0u32;
        let mut effect_slot_count = 0u32;
        let mut weighted_lower_count = 0u32;
        let mut weighted_upper_count = 0u32;
        let mut weighted_edge_count = 0u32;
        let mut effect_subtraction_count = 0u32;
        let slots = graph
            .slots
            .iter()
            .enumerate()
            .map(|(id, slot)| {
                match slot.kind {
                    TypeSlotKind::Value => value_slot_count += 1,
                    TypeSlotKind::Effect => effect_slot_count += 1,
                }
                weighted_lower_count += slot.weighted_lower.len() as u32;
                weighted_upper_count += slot.weighted_upper.len() as u32;
                weighted_edge_count += slot.weighted_successors.len() as u32;
                effect_subtraction_count += slot.effect_subtraction_consumers.len() as u32;
                RuntimeEvidenceSlot::from_slot(id as u32, slot)
            })
            .collect::<Vec<_>>();
        let weighted_constraint_count = graph
            .queued_constraints
            .iter()
            .filter(|constraint| {
                !stack_weight_is_empty(&constraint.lower_weight)
                    || !stack_weight_is_empty(&constraint.upper_weight)
            })
            .count() as u32;
        let mut row_residuals = graph
            .row_residuals
            .iter()
            .map(|(key, residual)| RuntimeEvidenceRowResidual {
                source: key.source,
                retained_families: key.retained_families.clone(),
                weight: key.weight.clone(),
                residual: *residual,
            })
            .collect::<Vec<_>>();
        row_residuals.sort_by(|left, right| {
            left.source
                .cmp(&right.source)
                .then_with(|| left.residual.cmp(&right.residual))
                .then_with(|| {
                    format!("{:?}", left.retained_families)
                        .cmp(&format!("{:?}", right.retained_families))
                })
                .then_with(|| format!("{:?}", left.weight).cmp(&format!("{:?}", right.weight)))
        });
        Self {
            slot_count: graph.slots.len() as u32,
            value_slot_count,
            effect_slot_count,
            queued_constraint_count: graph.queued_constraints.len() as u32,
            weighted_constraint_count,
            weighted_lower_count,
            weighted_upper_count,
            weighted_edge_count,
            effect_subtraction_count,
            row_residuals,
            slots,
        }
    }

    fn slot(&self, id: u32) -> Option<&RuntimeEvidenceSlot> {
        self.slots.get(id as usize).filter(|slot| slot.id == id)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceSlot {
    pub id: u32,
    pub kind: RuntimeEvidenceSlotKind,
    pub lower_count: u32,
    pub upper_count: u32,
    pub successor_count: u32,
    pub predecessor_count: u32,
    pub weighted_lower: Vec<RuntimeEvidenceWeightedTypeBound>,
    pub weighted_upper: Vec<RuntimeEvidenceWeightedTypeBound>,
    pub weighted_successors: Vec<RuntimeEvidenceWeightedSlotEdge>,
    pub weighted_predecessors: Vec<RuntimeEvidenceWeightedSlotEdge>,
    pub effect_subtractions: Vec<RuntimeEvidenceEffectSubtraction>,
}

impl RuntimeEvidenceSlot {
    fn from_slot(id: u32, slot: &TypeSlot) -> Self {
        Self {
            id,
            kind: RuntimeEvidenceSlotKind::from_kind(slot.kind),
            lower_count: slot.lower.len() as u32,
            upper_count: slot.upper.len() as u32,
            successor_count: slot.successors.len() as u32,
            predecessor_count: slot.predecessors.len() as u32,
            weighted_lower: weighted_type_bounds(&slot.weighted_lower),
            weighted_upper: weighted_type_bounds(&slot.weighted_upper),
            weighted_successors: weighted_slot_edges(&slot.weighted_successors),
            weighted_predecessors: weighted_slot_edges(&slot.weighted_predecessors),
            effect_subtractions: slot
                .effect_subtraction_consumers
                .iter()
                .map(RuntimeEvidenceEffectSubtraction::from_demand)
                .collect(),
        }
    }

    fn has_runtime_evidence(&self) -> bool {
        !self.weighted_lower.is_empty()
            || !self.weighted_upper.is_empty()
            || !self.weighted_successors.is_empty()
            || !self.weighted_predecessors.is_empty()
            || !self.effect_subtractions.is_empty()
    }

    fn has_weighted_evidence(&self) -> bool {
        !self.weighted_lower.is_empty()
            || !self.weighted_upper.is_empty()
            || !self.weighted_successors.is_empty()
            || !self.weighted_predecessors.is_empty()
    }

    fn has_effect_subtraction_evidence(&self) -> bool {
        !self.effect_subtractions.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceSlotKind {
    Value,
    Effect,
}

impl RuntimeEvidenceSlotKind {
    fn from_kind(kind: TypeSlotKind) -> Self {
        match kind {
            TypeSlotKind::Value => Self::Value,
            TypeSlotKind::Effect => Self::Effect,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceWeightedTypeBound {
    pub ty: Type,
    pub lower_weight: StackWeight,
    pub upper_weight: StackWeight,
}

impl RuntimeEvidenceWeightedTypeBound {
    fn from_bound(bound: &WeightedTypeBound) -> Self {
        Self {
            ty: bound.ty.clone(),
            lower_weight: bound.lower_weight.clone(),
            upper_weight: bound.upper_weight.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceWeightedSlotEdge {
    pub slot: u32,
    pub lower_weight: StackWeight,
    pub upper_weight: StackWeight,
}

impl RuntimeEvidenceWeightedSlotEdge {
    fn from_edge(edge: &WeightedSlotEdge) -> Self {
        Self {
            slot: edge.slot,
            lower_weight: edge.lower_weight.clone(),
            upper_weight: edge.upper_weight.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceEffectSubtraction {
    pub tail: Type,
    pub runtime_effect: Type,
    pub handled_items: Vec<Type>,
}

impl RuntimeEvidenceEffectSubtraction {
    fn from_demand(demand: &EffectSubtractionDemand) -> Self {
        Self {
            tail: demand.tail.clone(),
            runtime_effect: demand.runtime_effect.clone(),
            handled_items: demand.handled_items.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceRowResidual {
    pub source: u32,
    pub retained_families: Vec<EffectFamily>,
    pub weight: StackWeight,
    pub residual: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceTaskOwner {
    RootExpr { root_index: u32, expr: u32 },
    InstanceBody { instance: u32, def: u32, body: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceExprType {
    pub expr: u32,
    pub actual: Type,
    pub consumer: Option<Type>,
    pub actual_slots: Vec<u32>,
    pub consumer_slots: Vec<u32>,
    pub stack_weights: Vec<RuntimeEvidenceStackWeight>,
}

impl RuntimeEvidenceExprType {
    fn new(expr: poly_expr::ExprId, ty: &SolvedExprType) -> Self {
        let mut stack_weights = Vec::new();
        collect_stack_weights(
            RuntimeEvidenceTypeRole::Actual,
            &ty.actual,
            &mut Vec::new(),
            &mut stack_weights,
        );
        if let Some(consumer) = &ty.consumer {
            collect_stack_weights(
                RuntimeEvidenceTypeRole::Consumer,
                consumer,
                &mut Vec::new(),
                &mut stack_weights,
            );
        }
        Self {
            expr: expr.0,
            actual: ty.actual.clone(),
            consumer: ty.consumer.clone(),
            actual_slots: ty.actual_slots.clone(),
            consumer_slots: ty.consumer_slots.clone(),
            stack_weights,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceTypeAtExpr {
    pub expr: u32,
    pub ty: Type,
    pub stack_weights: Vec<RuntimeEvidenceStackWeight>,
}

impl RuntimeEvidenceTypeAtExpr {
    fn new(expr: poly_expr::ExprId, ty: &Type) -> Self {
        Self {
            expr: expr.0,
            ty: ty.clone(),
            stack_weights: stack_weights_for(RuntimeEvidenceTypeRole::Signature, ty),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceTypeAtPat {
    pub pat: u32,
    pub ty: Type,
    pub stack_weights: Vec<RuntimeEvidenceStackWeight>,
}

impl RuntimeEvidenceTypeAtPat {
    fn new(pat: poly_expr::PatId, ty: &Type) -> Self {
        Self {
            pat: pat.0,
            ty: ty.clone(),
            stack_weights: stack_weights_for(RuntimeEvidenceTypeRole::Signature, ty),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceTypeclassResolution {
    pub expr: u32,
    pub implementation: u32,
    pub signature: Type,
    pub stack_weights: Vec<RuntimeEvidenceStackWeight>,
}

impl RuntimeEvidenceTypeclassResolution {
    fn new(expr: poly_expr::ExprId, resolution: &TypeclassResolution) -> Self {
        Self {
            expr: expr.0,
            implementation: resolution.implementation.0,
            signature: resolution.signature.clone(),
            stack_weights: stack_weights_for(
                RuntimeEvidenceTypeRole::Signature,
                &resolution.signature,
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceStackWeight {
    pub role: RuntimeEvidenceTypeRole,
    pub path: Vec<RuntimeEvidenceTypePathStep>,
    pub weight: StackWeight,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceTypeRole {
    Actual,
    Consumer,
    Signature,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceTypePathStep {
    Inner,
    FunArg,
    FunArgEffect,
    FunRetEffect,
    FunRet,
    ThunkEffect,
    ThunkValue,
    RecordField { name: String },
    VariantPayload { name: String, index: u32 },
    TupleItem { index: u32 },
    EffectRowItem { index: u32 },
    UnionLeft,
    UnionRight,
    IntersectionLeft,
    IntersectionRight,
    ConArg { index: u32 },
}

fn type_at_exprs(
    types: &std::collections::HashMap<poly_expr::ExprId, Type>,
) -> Vec<RuntimeEvidenceTypeAtExpr> {
    types
        .iter()
        .map(|(expr, ty)| RuntimeEvidenceTypeAtExpr::new(*expr, ty))
        .collect()
}

fn slots_for_site(site: &RuntimeEvidenceSite, expr_types: &[RuntimeEvidenceExprType]) -> Vec<u32> {
    let mut slots = BTreeSet::new();
    insert_expr_slots(site.expr, expr_types, &mut slots);
    if let Some(boundary) = &site.boundary {
        slots.extend(boundary.actual_slots.iter().copied());
        slots.extend(boundary.consumer_slots.iter().copied());
    }
    for expr in site.kind.child_exprs() {
        insert_expr_slots(expr, expr_types, &mut slots);
    }
    slots.into_iter().collect()
}

fn insert_expr_slots(expr: u32, expr_types: &[RuntimeEvidenceExprType], slots: &mut BTreeSet<u32>) {
    let Some(ty) = expr_types.iter().find(|ty| ty.expr == expr) else {
        return;
    };
    slots.extend(ty.actual_slots.iter().copied());
    slots.extend(ty.consumer_slots.iter().copied());
}

fn evidence_refs_for_slots(
    slots: &[u32],
    graph: &RuntimeEvidenceGraph,
) -> Vec<RuntimeEvidenceNodeEvidenceRef> {
    let mut refs = Vec::new();
    for slot_id in slots {
        let Some(slot) = graph.slot(*slot_id) else {
            continue;
        };
        refs.extend(slot.weighted_lower.iter().enumerate().map(|(index, _)| {
            RuntimeEvidenceNodeEvidenceRef::WeightedLower {
                slot: *slot_id,
                index: index as u32,
            }
        }));
        refs.extend(slot.weighted_upper.iter().enumerate().map(|(index, _)| {
            RuntimeEvidenceNodeEvidenceRef::WeightedUpper {
                slot: *slot_id,
                index: index as u32,
            }
        }));
        refs.extend(
            slot.weighted_successors
                .iter()
                .enumerate()
                .map(
                    |(index, edge)| RuntimeEvidenceNodeEvidenceRef::WeightedSuccessor {
                        slot: *slot_id,
                        index: index as u32,
                        target: edge.slot,
                    },
                ),
        );
        refs.extend(
            slot.weighted_predecessors
                .iter()
                .enumerate()
                .map(
                    |(index, edge)| RuntimeEvidenceNodeEvidenceRef::WeightedPredecessor {
                        slot: *slot_id,
                        index: index as u32,
                        source: edge.slot,
                    },
                ),
        );
        refs.extend(
            slot.effect_subtractions
                .iter()
                .enumerate()
                .map(
                    |(index, _)| RuntimeEvidenceNodeEvidenceRef::EffectSubtraction {
                        slot: *slot_id,
                        index: index as u32,
                    },
                ),
        );
    }
    refs
}

impl RuntimeEvidenceSiteKind {
    fn child_exprs(&self) -> Vec<u32> {
        match self {
            RuntimeEvidenceSiteKind::OperationValue { .. } => Vec::new(),
            RuntimeEvidenceSiteKind::OperationCall { callee, arg, .. } => vec![*callee, *arg],
            RuntimeEvidenceSiteKind::Catch { body, .. } => vec![*body],
            RuntimeEvidenceSiteKind::App { callee, arg, .. } => vec![*callee, *arg],
            RuntimeEvidenceSiteKind::Lambda { body, .. } => vec![*body],
            RuntimeEvidenceSiteKind::RefSet { reference, value } => vec![*reference, *value],
        }
    }
}

fn weighted_type_bounds(bounds: &[WeightedTypeBound]) -> Vec<RuntimeEvidenceWeightedTypeBound> {
    bounds
        .iter()
        .map(RuntimeEvidenceWeightedTypeBound::from_bound)
        .collect()
}

fn weighted_slot_edges(edges: &[WeightedSlotEdge]) -> Vec<RuntimeEvidenceWeightedSlotEdge> {
    edges
        .iter()
        .map(RuntimeEvidenceWeightedSlotEdge::from_edge)
        .collect()
}

fn format_effect_family(family: &EffectFamily) -> String {
    if family.args.is_empty() {
        return family.path.join("::");
    }
    let args = family
        .args
        .iter()
        .map(mono::dump::dump_type)
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}({args})", family.path.join("::"))
}

fn format_slot_ids(slots: &[u32]) -> String {
    slots
        .iter()
        .map(|slot| format!("t{slot}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_task_header(task: &RuntimeEvidenceTask) -> String {
    match task.owner {
        RuntimeEvidenceTaskOwner::RootExpr { root_index, expr } => format!(
            "task root[{root_index}] expr e{expr} expr_types {} refs {} selects {} pats {} typeclasses {} raw_thunks {}",
            task.expr_types.len(),
            task.ref_signatures.len(),
            task.select_signatures.len(),
            task.pat_ref_signatures.len(),
            task.typeclass_resolutions.len(),
            task.raw_thunk_computations.len(),
        ),
        RuntimeEvidenceTaskOwner::InstanceBody {
            instance,
            def,
            body,
        } => format!(
            "task instance m{instance} def d{def} body e{body} expr_types {} refs {} selects {} pats {} typeclasses {} raw_thunks {}",
            task.expr_types.len(),
            task.ref_signatures.len(),
            task.select_signatures.len(),
            task.pat_ref_signatures.len(),
            task.typeclass_resolutions.len(),
            task.raw_thunk_computations.len(),
        ),
    }
}

fn format_stack_weights(out: &mut String, weights: &[RuntimeEvidenceStackWeight]) {
    for weight in weights {
        let path = weight
            .path
            .iter()
            .map(format_path_step)
            .collect::<Vec<_>>()
            .join(".");
        let path = if path.is_empty() {
            "<root>".to_string()
        } else {
            path
        };
        let _ = writeln!(
            out,
            "    stack {:?} at {}: {:?}",
            weight.role, path, weight.weight
        );
    }
}

fn format_path_step(step: &RuntimeEvidenceTypePathStep) -> String {
    match step {
        RuntimeEvidenceTypePathStep::Inner => "inner".to_string(),
        RuntimeEvidenceTypePathStep::FunArg => "fun.arg".to_string(),
        RuntimeEvidenceTypePathStep::FunArgEffect => "fun.arg_effect".to_string(),
        RuntimeEvidenceTypePathStep::FunRetEffect => "fun.ret_effect".to_string(),
        RuntimeEvidenceTypePathStep::FunRet => "fun.ret".to_string(),
        RuntimeEvidenceTypePathStep::ThunkEffect => "thunk.effect".to_string(),
        RuntimeEvidenceTypePathStep::ThunkValue => "thunk.value".to_string(),
        RuntimeEvidenceTypePathStep::RecordField { name } => format!("record.{name}"),
        RuntimeEvidenceTypePathStep::VariantPayload { name, index } => {
            format!("variant.{name}.{index}")
        }
        RuntimeEvidenceTypePathStep::TupleItem { index } => format!("tuple.{index}"),
        RuntimeEvidenceTypePathStep::EffectRowItem { index } => format!("effect.{index}"),
        RuntimeEvidenceTypePathStep::UnionLeft => "union.left".to_string(),
        RuntimeEvidenceTypePathStep::UnionRight => "union.right".to_string(),
        RuntimeEvidenceTypePathStep::IntersectionLeft => "intersection.left".to_string(),
        RuntimeEvidenceTypePathStep::IntersectionRight => "intersection.right".to_string(),
        RuntimeEvidenceTypePathStep::ConArg { index } => format!("con.{index}"),
    }
}

fn stack_weights_for(role: RuntimeEvidenceTypeRole, ty: &Type) -> Vec<RuntimeEvidenceStackWeight> {
    let mut out = Vec::new();
    collect_stack_weights(role, ty, &mut Vec::new(), &mut out);
    out
}

fn collect_stack_weights(
    role: RuntimeEvidenceTypeRole,
    ty: &Type,
    path: &mut Vec<RuntimeEvidenceTypePathStep>,
    out: &mut Vec<RuntimeEvidenceStackWeight>,
) {
    match ty {
        Type::Stack { inner, weight } => {
            out.push(RuntimeEvidenceStackWeight {
                role,
                path: path.clone(),
                weight: weight.clone(),
            });
            path.push(RuntimeEvidenceTypePathStep::Inner);
            collect_stack_weights(role, inner, path, out);
            path.pop();
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            with_path(path, RuntimeEvidenceTypePathStep::FunArg, |path| {
                collect_stack_weights(role, arg, path, out)
            });
            with_path(path, RuntimeEvidenceTypePathStep::FunArgEffect, |path| {
                collect_stack_weights(role, arg_effect, path, out)
            });
            with_path(path, RuntimeEvidenceTypePathStep::FunRetEffect, |path| {
                collect_stack_weights(role, ret_effect, path, out)
            });
            with_path(path, RuntimeEvidenceTypePathStep::FunRet, |path| {
                collect_stack_weights(role, ret, path, out)
            });
        }
        Type::Thunk { effect, value } => {
            with_path(path, RuntimeEvidenceTypePathStep::ThunkEffect, |path| {
                collect_stack_weights(role, effect, path, out)
            });
            with_path(path, RuntimeEvidenceTypePathStep::ThunkValue, |path| {
                collect_stack_weights(role, value, path, out)
            });
        }
        Type::Record(fields) => {
            for field in fields {
                with_path(
                    path,
                    RuntimeEvidenceTypePathStep::RecordField {
                        name: field.name.clone(),
                    },
                    |path| collect_stack_weights(role, &field.value, path, out),
                );
            }
        }
        Type::PolyVariant(variants) => {
            for variant in variants {
                for (index, payload) in variant.payloads.iter().enumerate() {
                    with_path(
                        path,
                        RuntimeEvidenceTypePathStep::VariantPayload {
                            name: variant.name.clone(),
                            index: index as u32,
                        },
                        |path| collect_stack_weights(role, payload, path, out),
                    );
                }
            }
        }
        Type::Tuple(items) => {
            for (index, item) in items.iter().enumerate() {
                with_path(
                    path,
                    RuntimeEvidenceTypePathStep::TupleItem {
                        index: index as u32,
                    },
                    |path| collect_stack_weights(role, item, path, out),
                );
            }
        }
        Type::EffectRow(items) => {
            for (index, item) in items.iter().enumerate() {
                with_path(
                    path,
                    RuntimeEvidenceTypePathStep::EffectRowItem {
                        index: index as u32,
                    },
                    |path| collect_stack_weights(role, item, path, out),
                );
            }
        }
        Type::Union(left, right) => {
            with_path(path, RuntimeEvidenceTypePathStep::UnionLeft, |path| {
                collect_stack_weights(role, left, path, out)
            });
            with_path(path, RuntimeEvidenceTypePathStep::UnionRight, |path| {
                collect_stack_weights(role, right, path, out)
            });
        }
        Type::Intersection(left, right) => {
            with_path(
                path,
                RuntimeEvidenceTypePathStep::IntersectionLeft,
                |path| collect_stack_weights(role, left, path, out),
            );
            with_path(
                path,
                RuntimeEvidenceTypePathStep::IntersectionRight,
                |path| collect_stack_weights(role, right, path, out),
            );
        }
        Type::Con { args, .. } => {
            for (index, arg) in args.iter().enumerate() {
                with_path(
                    path,
                    RuntimeEvidenceTypePathStep::ConArg {
                        index: index as u32,
                    },
                    |path| collect_stack_weights(role, arg, path, out),
                );
            }
        }
        Type::Any | Type::Never | Type::OpenVar(_) => {}
    }
}

fn with_path(
    path: &mut Vec<RuntimeEvidenceTypePathStep>,
    step: RuntimeEvidenceTypePathStep,
    f: impl FnOnce(&mut Vec<RuntimeEvidenceTypePathStep>),
) {
    path.push(step);
    f(path);
    path.pop();
}
