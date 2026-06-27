use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

use control_vm::{
    Block, ControlEffectUseKind, ControlEvidenceProgram, ControlEvidenceRoute, DefId, Expr, ExprId,
    Program, RecordSpread, Root, Stmt,
};
use specialize::{
    RuntimeEvidenceNode, RuntimeEvidenceNodeKind, RuntimeEvidenceSurface, RuntimeEvidenceTaskOwner,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmPlan {
    pub(crate) summary: EvidenceVmSummary,
    pub(crate) handlers: Vec<EvidenceVmHandlerPlan>,
    pub(crate) operations: Vec<EvidenceVmOperationPlan>,
    pub(crate) functions: Vec<EvidenceVmFunctionPlan>,
    pub(crate) values: Vec<EvidenceVmValueEnvPlan>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct EvidenceVmSummary {
    pub(crate) handlers: usize,
    pub(crate) operations: usize,
    pub(crate) direct_operations: usize,
    pub(crate) direct_abortive_operations: usize,
    pub(crate) direct_resumptive_operations: usize,
    pub(crate) lexical_candidate_operations: usize,
    pub(crate) delayed_lexical_candidate_operations: usize,
    pub(crate) blocked_operations: usize,
    pub(crate) unhandled_operations: usize,
    pub(crate) adapter_boundaries: usize,
    pub(crate) delayed_boundaries: usize,
    pub(crate) generic_fallbacks: usize,
    pub(crate) evidence_param_functions: usize,
    pub(crate) evidence_params: usize,
    pub(crate) evidence_arg_calls: usize,
    pub(crate) evidence_slot_keys: usize,
    pub(crate) evidence_env_values: usize,
    pub(crate) evidence_env_captures: usize,
    pub(crate) runtime_tasks: usize,
    pub(crate) runtime_nodes: usize,
    pub(crate) runtime_evidence_refs: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmHandlerPlan {
    pub(crate) expr: ExprId,
    pub(crate) body: ExprId,
    pub(crate) arms: Vec<EvidenceVmHandlerArmPlan>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmHandlerArmPlan {
    pub(crate) path: Option<Vec<String>>,
    pub(crate) resumptive: bool,
    pub(crate) guarded: bool,
    pub(crate) classification: EvidenceVmHandlerArmClass,
    pub(crate) body: ExprId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmHandlerArmClass {
    Value,
    Abortive,
    TailResumptive,
    MayYield,
    Fallback,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmOperationPlan {
    pub(crate) expr: ExprId,
    pub(crate) path: Vec<String>,
    pub(crate) slot: EvidenceVmSlotKey,
    pub(crate) kind: EvidenceVmOperationKind,
    pub(crate) lowering: EvidenceVmOperationLowering,
    pub(crate) runtime_nodes: Vec<u32>,
    pub(crate) runtime_evidence_refs: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmOperationKind {
    Value,
    Call { apply: ExprId, callee: ExprId },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EvidenceVmOperationLowering {
    DirectHandlerCall {
        handler: ExprId,
        resumptive: bool,
        handler_known: bool,
    },
    LexicalHandlerCandidate {
        handler: ExprId,
        resumptive: bool,
        delayed_boundary: bool,
    },
    HygieneFallback {
        handler: ExprId,
        resumptive: bool,
        callback_boundary: bool,
        delayed_boundary: bool,
    },
    GenericFallback,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmFunctionPlan {
    pub(crate) owner: RuntimeEvidenceTaskOwner,
    pub(crate) signature: EvidenceVmFunctionSignature,
    pub(crate) node_count: usize,
    pub(crate) evidence_ref_count: usize,
    pub(crate) required_evidence: Vec<EvidenceVmEvidenceRequirement>,
    pub(crate) provided_evidence_paths: Vec<Vec<String>>,
    pub(crate) calls_needing_evidence: Vec<EvidenceVmCallPlan>,
    pub(crate) operation_exprs: Vec<u32>,
    pub(crate) handler_exprs: Vec<u32>,
    pub(crate) fallback_exprs: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmEvidenceRequirement {
    pub(crate) slot: EvidenceVmSlotKey,
    pub(crate) operation_exprs: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmCallPlan {
    pub(crate) apply: ExprId,
    pub(crate) callee_instance: u32,
    pub(crate) required_evidence_slots: Vec<EvidenceVmSlotKey>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmValueEnvPlan {
    pub(crate) expr: ExprId,
    pub(crate) kind: EvidenceVmValueEnvKind,
    pub(crate) signature: EvidenceVmValueEnvSignature,
    pub(crate) captured_evidence: Vec<EvidenceVmEvidenceRequirement>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmFunctionSignature {
    pub(crate) params: Vec<EvidenceVmSlotKey>,
    pub(crate) provides: Vec<EvidenceVmSlotKey>,
    pub(crate) value_env: Vec<EvidenceVmSlotKey>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmValueEnvSignature {
    pub(crate) captures: Vec<EvidenceVmSlotKey>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct EvidenceVmSlotKey {
    pub(crate) family: Vec<String>,
    pub(crate) route: EvidenceVmSlotRouteKey,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum EvidenceVmSlotRouteKey {
    Positive,
    Blocked,
    UnknownFallback,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EvidenceVmValueEnvKind {
    Lambda {
        body: ExprId,
    },
    Thunk {
        body: ExprId,
    },
    FunctionAdapter {
        function: ExprId,
        creates_callback_boundary: bool,
        body_marker_count: usize,
        arg_marker_count: usize,
        ret_marker_count: usize,
    },
}

pub(crate) fn build_plan(program: &Program, surface: &RuntimeEvidenceSurface) -> EvidenceVmPlan {
    let control = ControlEvidenceProgram::from_program(program);
    build_plan_from_evidence(program, &control, surface)
}

fn build_plan_from_evidence(
    program: &Program,
    control: &ControlEvidenceProgram,
    surface: &RuntimeEvidenceSurface,
) -> EvidenceVmPlan {
    let runtime_nodes = RuntimeNodeIndex::new(surface);
    let lexical_handlers = LexicalHandlerIndex::new(program, control);
    let handler_exprs = control
        .handlers
        .iter()
        .map(|handler| handler.expr)
        .collect::<HashSet<_>>();

    let handlers = control
        .handlers
        .iter()
        .map(|handler| EvidenceVmHandlerPlan {
            expr: handler.expr,
            body: handler.body,
            arms: handler
                .arms
                .iter()
                .enumerate()
                .map(|(index, arm)| EvidenceVmHandlerArmPlan {
                    path: arm.operation_path.clone(),
                    resumptive: arm.resumptive,
                    guarded: arm.guarded,
                    classification: classify_handler_arm(program, handler.expr, index, arm),
                    body: arm.body,
                })
                .collect(),
        })
        .collect::<Vec<_>>();

    let operations = control
        .effects
        .iter()
        .map(|effect| {
            let nodes = runtime_nodes.nodes_for_expr(effect.expr.0);
            let lowering = operation_lowering(
                effect.expr,
                &effect.route,
                &handler_exprs,
                &lexical_handlers,
            );
            EvidenceVmOperationPlan {
                expr: effect.expr,
                path: effect.path.clone(),
                slot: slot_for_operation_lowering(&effect.path, &lowering),
                kind: operation_kind(effect.kind),
                lowering,
                runtime_evidence_refs: nodes
                    .iter()
                    .map(|node| node.evidence_refs.len())
                    .sum::<usize>(),
                runtime_nodes: nodes.iter().map(|node| node.id).collect(),
            }
        })
        .collect::<Vec<_>>();

    let mut functions = surface
        .tasks
        .iter()
        .map(|task| function_plan(control, task))
        .collect::<Vec<_>>();
    attach_evidence_call_plans(program, &mut functions);
    let values = collect_value_env_plans(program, control);

    let summary = summarize_plan(control, surface, &operations, &functions, &values);
    EvidenceVmPlan {
        summary,
        handlers,
        operations,
        functions,
        values,
    }
}

pub(crate) fn format_plan(plan: &EvidenceVmPlan) -> String {
    let mut out = String::new();
    let summary = plan.summary;
    writeln!(&mut out, "evidence vm plan:").unwrap();
    writeln!(&mut out, "  handlers: {}", summary.handlers).unwrap();
    writeln!(&mut out, "  operations: {}", summary.operations).unwrap();
    writeln!(
        &mut out,
        "  direct_operations: {} abortive {} resumptive {}",
        summary.direct_operations,
        summary.direct_abortive_operations,
        summary.direct_resumptive_operations
    )
    .unwrap();
    writeln!(
        &mut out,
        "  lexical_candidate_operations: {} delayed {}",
        summary.lexical_candidate_operations, summary.delayed_lexical_candidate_operations
    )
    .unwrap();
    writeln!(
        &mut out,
        "  blocked_operations: {} unhandled_operations: {}",
        summary.blocked_operations, summary.unhandled_operations
    )
    .unwrap();
    writeln!(
        &mut out,
        "  adapter_boundaries: {} delayed_boundaries: {} generic_fallbacks: {}",
        summary.adapter_boundaries, summary.delayed_boundaries, summary.generic_fallbacks
    )
    .unwrap();
    writeln!(
        &mut out,
        "  evidence_param_functions: {} evidence_params: {} evidence_arg_calls: {}",
        summary.evidence_param_functions, summary.evidence_params, summary.evidence_arg_calls
    )
    .unwrap();
    writeln!(
        &mut out,
        "  evidence_slot_keys: {}",
        summary.evidence_slot_keys
    )
    .unwrap();
    writeln!(
        &mut out,
        "  evidence_env_values: {} evidence_env_captures: {}",
        summary.evidence_env_values, summary.evidence_env_captures
    )
    .unwrap();
    writeln!(
        &mut out,
        "  runtime_tasks: {} runtime_nodes: {} runtime_evidence_refs: {}",
        summary.runtime_tasks, summary.runtime_nodes, summary.runtime_evidence_refs
    )
    .unwrap();
    format_handlers(&mut out, &plan.handlers);
    format_operations(&mut out, &plan.operations);
    format_functions(&mut out, &plan.functions);
    format_value_envs(&mut out, &plan.values);
    out
}

fn summarize_plan(
    control: &ControlEvidenceProgram,
    surface: &RuntimeEvidenceSurface,
    operations: &[EvidenceVmOperationPlan],
    functions: &[EvidenceVmFunctionPlan],
    values: &[EvidenceVmValueEnvPlan],
) -> EvidenceVmSummary {
    let mut summary = EvidenceVmSummary {
        handlers: control.handlers.len(),
        operations: operations.len(),
        adapter_boundaries: control
            .adapters
            .iter()
            .filter(|adapter| adapter.creates_callback_boundary)
            .count(),
        delayed_boundaries: control.delayed_boundaries.len(),
        generic_fallbacks: control.fallbacks.len(),
        evidence_param_functions: functions
            .iter()
            .filter(|function| !function.required_evidence.is_empty())
            .count(),
        evidence_params: functions
            .iter()
            .map(|function| function.required_evidence.len())
            .sum(),
        evidence_arg_calls: functions
            .iter()
            .map(|function| function.calls_needing_evidence.len())
            .sum(),
        evidence_slot_keys: distinct_evidence_slot_count(operations, functions, values),
        evidence_env_values: values.len(),
        evidence_env_captures: values
            .iter()
            .map(|value| value.captured_evidence.len())
            .sum(),
        runtime_tasks: surface.tasks.len(),
        runtime_nodes: surface.tasks.iter().map(|task| task.nodes.len()).sum(),
        runtime_evidence_refs: surface
            .tasks
            .iter()
            .flat_map(|task| &task.nodes)
            .map(|node| node.evidence_refs.len())
            .sum(),
        ..EvidenceVmSummary::default()
    };
    for operation in operations {
        match operation.lowering {
            EvidenceVmOperationLowering::DirectHandlerCall {
                resumptive: false, ..
            } => {
                summary.direct_operations += 1;
                summary.direct_abortive_operations += 1;
            }
            EvidenceVmOperationLowering::DirectHandlerCall {
                resumptive: true, ..
            } => {
                summary.direct_operations += 1;
                summary.direct_resumptive_operations += 1;
            }
            EvidenceVmOperationLowering::LexicalHandlerCandidate {
                delayed_boundary, ..
            } => {
                summary.lexical_candidate_operations += 1;
                if delayed_boundary {
                    summary.delayed_lexical_candidate_operations += 1;
                }
            }
            EvidenceVmOperationLowering::HygieneFallback { .. } => {
                summary.blocked_operations += 1;
            }
            EvidenceVmOperationLowering::GenericFallback => {
                summary.unhandled_operations += 1;
            }
        }
    }
    summary
}

fn function_plan(
    control: &ControlEvidenceProgram,
    task: &specialize::RuntimeEvidenceTask,
) -> EvidenceVmFunctionPlan {
    let provided_evidence_paths = provided_paths_for_nodes(&task.nodes);
    let required_evidence = required_evidence_for_nodes(&task.nodes, &provided_evidence_paths);
    let signature = EvidenceVmFunctionSignature {
        params: requirement_slots(&required_evidence),
        provides: provided_evidence_paths
            .iter()
            .map(|path| positive_slot(path.clone()))
            .collect(),
        value_env: Vec::new(),
    };
    EvidenceVmFunctionPlan {
        owner: task.owner,
        signature,
        node_count: task.nodes.len(),
        evidence_ref_count: task
            .nodes
            .iter()
            .map(|node| node.evidence_refs.len())
            .sum::<usize>(),
        required_evidence,
        provided_evidence_paths,
        calls_needing_evidence: Vec::new(),
        operation_exprs: task
            .nodes
            .iter()
            .filter_map(|node| {
                matches!(node.kind, RuntimeEvidenceNodeKind::OperationCall { .. })
                    .then_some(node.expr)
            })
            .collect(),
        handler_exprs: task
            .nodes
            .iter()
            .filter_map(|node| {
                matches!(node.kind, RuntimeEvidenceNodeKind::Handler { .. }).then_some(node.expr)
            })
            .collect(),
        fallback_exprs: generic_fallback_exprs(control, task.nodes.iter().map(|node| node.expr)),
    }
}

fn attach_evidence_call_plans(program: &Program, functions: &mut [EvidenceVmFunctionPlan]) {
    let requirements_by_instance = functions
        .iter()
        .filter_map(|function| {
            let RuntimeEvidenceTaskOwner::InstanceBody { instance, .. } = function.owner else {
                return None;
            };
            (!function.required_evidence.is_empty())
                .then(|| (instance, function.signature.params.clone()))
        })
        .collect::<HashMap<_, _>>();
    if requirements_by_instance.is_empty() {
        return;
    }
    for function in functions {
        let Some(body) = function_body(function.owner) else {
            continue;
        };
        let mut visited = HashSet::new();
        collect_evidence_arg_calls(
            program,
            ExprId(body),
            &requirements_by_instance,
            &mut visited,
            &mut function.calls_needing_evidence,
        );
    }
}

fn function_body(owner: RuntimeEvidenceTaskOwner) -> Option<u32> {
    match owner {
        RuntimeEvidenceTaskOwner::RootExpr { expr, .. } => Some(expr),
        RuntimeEvidenceTaskOwner::InstanceBody { body, .. } => Some(body),
    }
}

fn collect_evidence_arg_calls(
    program: &Program,
    expr: ExprId,
    requirements_by_instance: &HashMap<u32, Vec<EvidenceVmSlotKey>>,
    visited: &mut HashSet<ExprId>,
    out: &mut Vec<EvidenceVmCallPlan>,
) {
    if !visited.insert(expr) {
        return;
    }
    let Some(node) = control_expr(program, expr) else {
        return;
    };
    match node {
        Expr::Apply { callee, arg } => {
            if let Some(instance) = instance_ref(program, *callee)
                && let Some(required_evidence_slots) = requirements_by_instance.get(&instance.0)
            {
                out.push(EvidenceVmCallPlan {
                    apply: expr,
                    callee_instance: instance.0,
                    required_evidence_slots: required_evidence_slots.clone(),
                });
            }
            collect_evidence_arg_calls(program, *callee, requirements_by_instance, visited, out);
            collect_evidence_arg_calls(program, *arg, requirements_by_instance, visited, out);
        }
        Expr::Coerce { expr, .. }
        | Expr::ForceThunk { thunk: expr, .. }
        | Expr::FunctionAdapter { function: expr, .. }
        | Expr::MarkerFrame { body: expr, .. }
        | Expr::MakeThunk { body: expr, .. }
        | Expr::Lambda { body: expr, .. }
        | Expr::Select { base: expr, .. } => {
            collect_evidence_arg_calls(program, *expr, requirements_by_instance, visited, out);
        }
        Expr::RefSet { reference, value } => {
            collect_evidence_arg_calls(program, *reference, requirements_by_instance, visited, out);
            collect_evidence_arg_calls(program, *value, requirements_by_instance, visited, out);
        }
        Expr::Tuple(items) => {
            for item in items {
                collect_evidence_arg_calls(program, *item, requirements_by_instance, visited, out);
            }
        }
        Expr::Record { fields, spread } => {
            for field in fields {
                collect_evidence_arg_calls(
                    program,
                    field.value,
                    requirements_by_instance,
                    visited,
                    out,
                );
            }
            match spread {
                RecordSpread::None => {}
                RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                    collect_evidence_arg_calls(
                        program,
                        *expr,
                        requirements_by_instance,
                        visited,
                        out,
                    );
                }
            }
        }
        Expr::PolyVariant { payloads, .. } => {
            for payload in payloads {
                collect_evidence_arg_calls(
                    program,
                    *payload,
                    requirements_by_instance,
                    visited,
                    out,
                );
            }
        }
        Expr::Case { scrutinee, arms } => {
            collect_evidence_arg_calls(program, *scrutinee, requirements_by_instance, visited, out);
            for arm in arms {
                if let Some(guard) = arm.guard {
                    collect_evidence_arg_calls(
                        program,
                        guard,
                        requirements_by_instance,
                        visited,
                        out,
                    );
                }
                collect_evidence_arg_calls(
                    program,
                    arm.body,
                    requirements_by_instance,
                    visited,
                    out,
                );
            }
        }
        Expr::Catch { body, arms } => {
            collect_evidence_arg_calls(program, *body, requirements_by_instance, visited, out);
            for arm in arms {
                if let Some(guard) = arm.guard {
                    collect_evidence_arg_calls(
                        program,
                        guard,
                        requirements_by_instance,
                        visited,
                        out,
                    );
                }
                collect_evidence_arg_calls(
                    program,
                    arm.body,
                    requirements_by_instance,
                    visited,
                    out,
                );
            }
        }
        Expr::Block(block) => {
            collect_block_evidence_arg_calls(
                program,
                block,
                requirements_by_instance,
                visited,
                out,
            );
        }
        Expr::Lit(_)
        | Expr::PrimitiveOp { .. }
        | Expr::Constructor { .. }
        | Expr::EffectOp { .. }
        | Expr::Local(_)
        | Expr::InstanceRef(_) => {}
    }
}

fn collect_block_evidence_arg_calls(
    program: &Program,
    block: &Block,
    requirements_by_instance: &HashMap<u32, Vec<EvidenceVmSlotKey>>,
    visited: &mut HashSet<ExprId>,
    out: &mut Vec<EvidenceVmCallPlan>,
) {
    for stmt in &block.stmts {
        collect_stmt_evidence_arg_calls(program, stmt, requirements_by_instance, visited, out);
    }
    if let Some(tail) = block.tail {
        collect_evidence_arg_calls(program, tail, requirements_by_instance, visited, out);
    }
}

fn collect_stmt_evidence_arg_calls(
    program: &Program,
    stmt: &Stmt,
    requirements_by_instance: &HashMap<u32, Vec<EvidenceVmSlotKey>>,
    visited: &mut HashSet<ExprId>,
    out: &mut Vec<EvidenceVmCallPlan>,
) {
    match stmt {
        Stmt::Let(_, _, expr) | Stmt::Expr(expr) => {
            collect_evidence_arg_calls(program, *expr, requirements_by_instance, visited, out);
        }
        Stmt::Module(_, stmts) => {
            for stmt in stmts {
                collect_stmt_evidence_arg_calls(
                    program,
                    stmt,
                    requirements_by_instance,
                    visited,
                    out,
                );
            }
        }
    }
}

fn collect_value_env_plans(
    program: &Program,
    control: &ControlEvidenceProgram,
) -> Vec<EvidenceVmValueEnvPlan> {
    let adapters = control
        .adapters
        .iter()
        .map(|adapter| (adapter.expr, adapter))
        .collect::<HashMap<_, _>>();
    let mut values = Vec::new();
    for (index, expr) in program.exprs.iter().enumerate() {
        let id = ExprId(index as u32);
        match expr {
            Expr::Lambda { body, .. } => {
                let captured_evidence = requirements_in_expr(program, *body);
                if captured_evidence.is_empty() {
                    continue;
                }
                values.push(EvidenceVmValueEnvPlan {
                    expr: id,
                    kind: EvidenceVmValueEnvKind::Lambda { body: *body },
                    signature: value_env_signature(&captured_evidence),
                    captured_evidence,
                });
            }
            Expr::MakeThunk { body, .. } => {
                let captured_evidence = requirements_in_expr(program, *body);
                if captured_evidence.is_empty() {
                    continue;
                }
                values.push(EvidenceVmValueEnvPlan {
                    expr: id,
                    kind: EvidenceVmValueEnvKind::Thunk { body: *body },
                    signature: value_env_signature(&captured_evidence),
                    captured_evidence,
                });
            }
            Expr::FunctionAdapter { function, .. } => {
                let adapter = adapters.get(&id).copied();
                let captured_evidence = requirements_for_value_expr(program, *function);
                let kind = EvidenceVmValueEnvKind::FunctionAdapter {
                    function: *function,
                    creates_callback_boundary: adapter
                        .is_some_and(|adapter| adapter.creates_callback_boundary),
                    body_marker_count: adapter.map_or(0, |adapter| adapter.body_markers.len()),
                    arg_marker_count: adapter.map_or(0, |adapter| adapter.arg_markers.len()),
                    ret_marker_count: adapter.map_or(0, |adapter| adapter.ret_markers.len()),
                };
                if captured_evidence.is_empty() && !value_env_kind_has_boundary(&kind) {
                    continue;
                }
                values.push(EvidenceVmValueEnvPlan {
                    expr: id,
                    kind,
                    signature: value_env_signature(&captured_evidence),
                    captured_evidence,
                });
            }
            _ => {}
        }
    }
    values
}

fn value_env_kind_has_boundary(kind: &EvidenceVmValueEnvKind) -> bool {
    match kind {
        EvidenceVmValueEnvKind::Lambda { .. } | EvidenceVmValueEnvKind::Thunk { .. } => false,
        EvidenceVmValueEnvKind::FunctionAdapter {
            creates_callback_boundary,
            body_marker_count,
            arg_marker_count,
            ret_marker_count,
            ..
        } => {
            *creates_callback_boundary
                || *body_marker_count > 0
                || *arg_marker_count > 0
                || *ret_marker_count > 0
        }
    }
}

fn requirements_for_value_expr(
    program: &Program,
    expr: ExprId,
) -> Vec<EvidenceVmEvidenceRequirement> {
    let mut active = HashSet::new();
    requirements_for_value_expr_inner(program, expr, &mut active)
}

fn requirements_for_value_expr_inner(
    program: &Program,
    expr: ExprId,
    active: &mut HashSet<ExprId>,
) -> Vec<EvidenceVmEvidenceRequirement> {
    if !active.insert(expr) {
        return Vec::new();
    }
    let requirements = match control_expr(program, expr) {
        Some(Expr::Lambda { body, .. }) | Some(Expr::MakeThunk { body, .. }) => {
            requirements_in_expr(program, *body)
        }
        Some(Expr::FunctionAdapter { function, .. }) => {
            requirements_for_value_expr_inner(program, *function, active)
        }
        Some(Expr::Coerce { expr, .. })
        | Some(Expr::MarkerFrame { body: expr, .. })
        | Some(Expr::Select { base: expr, .. }) => {
            requirements_for_value_expr_inner(program, *expr, active)
        }
        Some(_) | None => requirements_in_expr(program, expr),
    };
    active.remove(&expr);
    requirements
}

fn requirements_in_expr(program: &Program, root: ExprId) -> Vec<EvidenceVmEvidenceRequirement> {
    let mut collector = RequirementCollector::default();
    let mut context = RequirementContext::default();
    let mut active = HashSet::new();
    collector.visit_expr(program, root, &mut context, &mut active);
    collector.finish()
}

#[derive(Default)]
struct RequirementCollector {
    by_slot: BTreeMap<EvidenceVmSlotKey, BTreeSet<u32>>,
}

impl RequirementCollector {
    fn record(&mut self, path: &[String], operation_expr: ExprId) {
        self.by_slot
            .entry(fallback_slot(path.to_vec()))
            .or_default()
            .insert(operation_expr.0);
    }

    fn finish(self) -> Vec<EvidenceVmEvidenceRequirement> {
        self.by_slot
            .into_iter()
            .map(|(slot, operation_exprs)| EvidenceVmEvidenceRequirement {
                slot,
                operation_exprs: operation_exprs.into_iter().collect(),
            })
            .collect()
    }

    fn visit_expr(
        &mut self,
        program: &Program,
        id: ExprId,
        context: &mut RequirementContext,
        active: &mut HashSet<ExprId>,
    ) {
        if !active.insert(id) {
            return;
        }
        let Some(expr) = control_expr(program, id) else {
            active.remove(&id);
            return;
        };
        match expr {
            Expr::Apply { callee, arg } => {
                if let Some(path) = effect_op_path(program, *callee)
                    && !context.handles(path)
                {
                    self.record(path, id);
                }
                self.visit_expr(program, *callee, context, active);
                self.visit_expr(program, *arg, context, active);
            }
            Expr::Catch { body, arms } => {
                let handled_paths = arms
                    .iter()
                    .filter_map(|arm| arm.operation_path.clone())
                    .collect::<Vec<_>>();
                context.with_handled_paths(&handled_paths, |context| {
                    self.visit_expr(program, *body, context, active);
                });
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr(program, guard, context, active);
                    }
                    self.visit_expr(program, arm.body, context, active);
                }
            }
            Expr::Coerce { expr, .. }
            | Expr::ForceThunk { thunk: expr, .. }
            | Expr::MarkerFrame { body: expr, .. }
            | Expr::Select { base: expr, .. } => {
                self.visit_expr(program, *expr, context, active);
            }
            Expr::RefSet { reference, value } => {
                self.visit_expr(program, *reference, context, active);
                self.visit_expr(program, *value, context, active);
            }
            Expr::Tuple(items) => {
                for item in items {
                    self.visit_expr(program, *item, context, active);
                }
            }
            Expr::Record { fields, spread } => {
                for field in fields {
                    self.visit_expr(program, field.value, context, active);
                }
                self.visit_spread(program, spread, context, active);
            }
            Expr::PolyVariant { payloads, .. } => {
                for payload in payloads {
                    self.visit_expr(program, *payload, context, active);
                }
            }
            Expr::Case { scrutinee, arms } => {
                self.visit_expr(program, *scrutinee, context, active);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr(program, guard, context, active);
                    }
                    self.visit_expr(program, arm.body, context, active);
                }
            }
            Expr::Block(block) => self.visit_block(program, block, context, active),
            Expr::Lambda { .. } | Expr::MakeThunk { .. } | Expr::FunctionAdapter { .. } => {}
            Expr::Lit(_)
            | Expr::PrimitiveOp { .. }
            | Expr::Constructor { .. }
            | Expr::EffectOp { .. }
            | Expr::Local(_)
            | Expr::InstanceRef(_) => {}
        }
        active.remove(&id);
    }

    fn visit_spread(
        &mut self,
        program: &Program,
        spread: &RecordSpread<ExprId>,
        context: &mut RequirementContext,
        active: &mut HashSet<ExprId>,
    ) {
        match spread {
            RecordSpread::None => {}
            RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                self.visit_expr(program, *expr, context, active);
            }
        }
    }

    fn visit_block(
        &mut self,
        program: &Program,
        block: &Block,
        context: &mut RequirementContext,
        active: &mut HashSet<ExprId>,
    ) {
        for stmt in &block.stmts {
            self.visit_stmt(program, stmt, context, active);
        }
        if let Some(tail) = block.tail {
            self.visit_expr(program, tail, context, active);
        }
    }

    fn visit_stmt(
        &mut self,
        program: &Program,
        stmt: &Stmt,
        context: &mut RequirementContext,
        active: &mut HashSet<ExprId>,
    ) {
        match stmt {
            Stmt::Let(_, _, expr) | Stmt::Expr(expr) => {
                self.visit_expr(program, *expr, context, active);
            }
            Stmt::Module(_, stmts) => {
                for stmt in stmts {
                    self.visit_stmt(program, stmt, context, active);
                }
            }
        }
    }
}

#[derive(Debug, Default)]
struct RequirementContext {
    handled_paths: Vec<Vec<String>>,
}

impl RequirementContext {
    fn handles(&self, path: &[String]) -> bool {
        self.handled_paths
            .iter()
            .rev()
            .any(|handled_path| handled_path == path)
    }

    fn with_handled_paths(&mut self, paths: &[Vec<String>], f: impl FnOnce(&mut Self)) {
        let start = self.handled_paths.len();
        self.handled_paths.extend(paths.iter().cloned());
        f(self);
        self.handled_paths.truncate(start);
    }
}

fn effect_op_path(program: &Program, expr: ExprId) -> Option<&[String]> {
    match control_expr(program, expr)? {
        Expr::EffectOp { path } => Some(path),
        _ => None,
    }
}

fn instance_ref(program: &Program, expr: ExprId) -> Option<control_vm::InstanceId> {
    match control_expr(program, expr)? {
        Expr::InstanceRef(instance) => Some(*instance),
        _ => None,
    }
}

fn provided_paths_for_nodes(nodes: &[RuntimeEvidenceNode]) -> Vec<Vec<String>> {
    let mut paths = BTreeSet::new();
    for node in nodes {
        if let RuntimeEvidenceNodeKind::Handler { handled_paths, .. } = &node.kind {
            for path in handled_paths {
                paths.insert(path.clone());
            }
        }
    }
    paths.into_iter().collect()
}

fn required_evidence_for_nodes(
    nodes: &[RuntimeEvidenceNode],
    provided_paths: &[Vec<String>],
) -> Vec<EvidenceVmEvidenceRequirement> {
    let provided = provided_paths.iter().collect::<BTreeSet<_>>();
    let mut by_slot = BTreeMap::<EvidenceVmSlotKey, Vec<u32>>::new();
    for node in nodes {
        if let RuntimeEvidenceNodeKind::OperationCall { path, .. } = &node.kind
            && !provided.contains(path)
        {
            by_slot
                .entry(fallback_slot(path.clone()))
                .or_default()
                .push(node.expr);
        }
    }
    by_slot
        .into_iter()
        .map(|(slot, operation_exprs)| EvidenceVmEvidenceRequirement {
            slot,
            operation_exprs,
        })
        .collect()
}

fn positive_slot(family: Vec<String>) -> EvidenceVmSlotKey {
    EvidenceVmSlotKey {
        family,
        route: EvidenceVmSlotRouteKey::Positive,
    }
}

fn blocked_slot(family: Vec<String>) -> EvidenceVmSlotKey {
    EvidenceVmSlotKey {
        family,
        route: EvidenceVmSlotRouteKey::Blocked,
    }
}

fn fallback_slot(family: Vec<String>) -> EvidenceVmSlotKey {
    EvidenceVmSlotKey {
        family,
        route: EvidenceVmSlotRouteKey::UnknownFallback,
    }
}

fn slot_for_operation_lowering(
    path: &[String],
    lowering: &EvidenceVmOperationLowering,
) -> EvidenceVmSlotKey {
    match lowering {
        EvidenceVmOperationLowering::DirectHandlerCall { .. } => positive_slot(path.to_vec()),
        EvidenceVmOperationLowering::HygieneFallback { .. } => blocked_slot(path.to_vec()),
        EvidenceVmOperationLowering::LexicalHandlerCandidate { .. }
        | EvidenceVmOperationLowering::GenericFallback => fallback_slot(path.to_vec()),
    }
}

fn requirement_slots(requirements: &[EvidenceVmEvidenceRequirement]) -> Vec<EvidenceVmSlotKey> {
    requirements
        .iter()
        .map(|requirement| requirement.slot.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn value_env_signature(captures: &[EvidenceVmEvidenceRequirement]) -> EvidenceVmValueEnvSignature {
    EvidenceVmValueEnvSignature {
        captures: requirement_slots(captures),
    }
}

fn distinct_evidence_slot_count(
    operations: &[EvidenceVmOperationPlan],
    functions: &[EvidenceVmFunctionPlan],
    values: &[EvidenceVmValueEnvPlan],
) -> usize {
    let mut slots = BTreeSet::new();
    for operation in operations {
        slots.insert(operation.slot.clone());
    }
    for function in functions {
        slots.extend(function.signature.params.iter().cloned());
        slots.extend(function.signature.provides.iter().cloned());
        slots.extend(function.signature.value_env.iter().cloned());
    }
    for value in values {
        slots.extend(value.signature.captures.iter().cloned());
    }
    slots.len()
}

fn operation_kind(kind: ControlEffectUseKind) -> EvidenceVmOperationKind {
    match kind {
        ControlEffectUseKind::OperationValue => EvidenceVmOperationKind::Value,
        ControlEffectUseKind::OperationCall { apply, callee } => {
            EvidenceVmOperationKind::Call { apply, callee }
        }
    }
}

fn operation_lowering(
    expr: ExprId,
    route: &ControlEvidenceRoute,
    handler_exprs: &HashSet<ExprId>,
    lexical_handlers: &LexicalHandlerIndex,
) -> EvidenceVmOperationLowering {
    match route {
        ControlEvidenceRoute::Direct {
            handler,
            resumptive,
        } => EvidenceVmOperationLowering::DirectHandlerCall {
            handler: *handler,
            resumptive: *resumptive,
            handler_known: handler_exprs.contains(handler),
        },
        ControlEvidenceRoute::Blocked {
            handler,
            resumptive,
            callback_boundary,
            delayed_boundary,
        } => EvidenceVmOperationLowering::HygieneFallback {
            handler: *handler,
            resumptive: *resumptive,
            callback_boundary: *callback_boundary,
            delayed_boundary: *delayed_boundary,
        },
        ControlEvidenceRoute::Unhandled => lexical_handlers
            .candidate_for(expr)
            .map(
                |candidate| EvidenceVmOperationLowering::LexicalHandlerCandidate {
                    handler: candidate.handler,
                    resumptive: candidate.resumptive,
                    delayed_boundary: candidate.delayed_boundary,
                },
            )
            .unwrap_or(EvidenceVmOperationLowering::GenericFallback),
    }
}

fn classify_handler_arm(
    program: &Program,
    handler_expr: ExprId,
    arm_index: usize,
    arm: &control_vm::ControlHandlerArmEvidence,
) -> EvidenceVmHandlerArmClass {
    if arm.operation_path.is_none() {
        return EvidenceVmHandlerArmClass::Value;
    }
    if !arm.resumptive {
        return EvidenceVmHandlerArmClass::Abortive;
    }
    if arm.guarded {
        return EvidenceVmHandlerArmClass::Fallback;
    }
    let Some(continuation) = source_handler_arm(program, handler_expr, arm_index)
        .and_then(|source_arm| source_arm.continuation.as_ref())
        .and_then(continuation_def)
    else {
        return EvidenceVmHandlerArmClass::MayYield;
    };
    if body_tail_resumes(program, arm.body, continuation) {
        EvidenceVmHandlerArmClass::TailResumptive
    } else {
        EvidenceVmHandlerArmClass::MayYield
    }
}

fn source_handler_arm(
    program: &Program,
    handler_expr: ExprId,
    arm_index: usize,
) -> Option<&control_vm::CatchArm> {
    let Expr::Catch { arms, .. } = control_expr(program, handler_expr)? else {
        return None;
    };
    arms.get(arm_index)
}

fn continuation_def(pat: &control_vm::Pat) -> Option<DefId> {
    match pat {
        control_vm::Pat::Var(def) | control_vm::Pat::As(_, def) => Some(*def),
        _ => None,
    }
}

fn body_tail_resumes(program: &Program, body: ExprId, continuation: DefId) -> bool {
    tail_resume_arg(program, body, continuation)
        .is_some_and(|arg| !expr_contains_local(program, arg, continuation))
}

fn tail_resume_arg(program: &Program, expr: ExprId, continuation: DefId) -> Option<ExprId> {
    match control_expr(program, expr)? {
        Expr::Apply { callee, arg } if expr_is_local(program, *callee, continuation) => Some(*arg),
        Expr::Coerce { expr, .. }
        | Expr::MarkerFrame { body: expr, .. }
        | Expr::Select { base: expr, .. } => tail_resume_arg(program, *expr, continuation),
        Expr::Block(block) => {
            if block
                .stmts
                .iter()
                .any(|stmt| stmt_contains_local(program, stmt, continuation))
            {
                return None;
            }
            tail_resume_arg(program, block.tail?, continuation)
        }
        _ => None,
    }
}

fn expr_is_local(program: &Program, expr: ExprId, def: DefId) -> bool {
    matches!(control_expr(program, expr), Some(Expr::Local(local)) if *local == def)
}

fn expr_contains_local(program: &Program, expr: ExprId, def: DefId) -> bool {
    let mut visited = HashSet::new();
    expr_contains_local_inner(program, expr, def, &mut visited)
}

fn expr_contains_local_inner(
    program: &Program,
    expr: ExprId,
    def: DefId,
    visited: &mut HashSet<ExprId>,
) -> bool {
    if !visited.insert(expr) {
        return false;
    }
    let Some(node) = control_expr(program, expr) else {
        return false;
    };
    match node {
        Expr::Local(local) => *local == def,
        Expr::Coerce { expr, .. }
        | Expr::ForceThunk { thunk: expr, .. }
        | Expr::FunctionAdapter { function: expr, .. }
        | Expr::MarkerFrame { body: expr, .. }
        | Expr::MakeThunk { body: expr, .. }
        | Expr::Lambda { body: expr, .. }
        | Expr::Select { base: expr, .. } => {
            expr_contains_local_inner(program, *expr, def, visited)
        }
        Expr::Apply { callee, arg }
        | Expr::RefSet {
            reference: callee,
            value: arg,
        } => {
            expr_contains_local_inner(program, *callee, def, visited)
                || expr_contains_local_inner(program, *arg, def, visited)
        }
        Expr::Tuple(items) => items
            .iter()
            .any(|item| expr_contains_local_inner(program, *item, def, visited)),
        Expr::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| expr_contains_local_inner(program, field.value, def, visited))
                || spread_contains_local(program, spread, def, visited)
        }
        Expr::PolyVariant { payloads, .. } => payloads
            .iter()
            .any(|payload| expr_contains_local_inner(program, *payload, def, visited)),
        Expr::Case { scrutinee, arms } => {
            expr_contains_local_inner(program, *scrutinee, def, visited)
                || arms.iter().any(|arm| {
                    arm.guard.is_some_and(|guard| {
                        expr_contains_local_inner(program, guard, def, visited)
                    }) || expr_contains_local_inner(program, arm.body, def, visited)
                })
        }
        Expr::Catch { body, arms } => {
            expr_contains_local_inner(program, *body, def, visited)
                || arms.iter().any(|arm| {
                    arm.guard.is_some_and(|guard| {
                        expr_contains_local_inner(program, guard, def, visited)
                    }) || expr_contains_local_inner(program, arm.body, def, visited)
                })
        }
        Expr::Block(block) => {
            block
                .stmts
                .iter()
                .any(|stmt| stmt_contains_local(program, stmt, def))
                || block
                    .tail
                    .is_some_and(|tail| expr_contains_local_inner(program, tail, def, visited))
        }
        Expr::Lit(_)
        | Expr::PrimitiveOp { .. }
        | Expr::Constructor { .. }
        | Expr::EffectOp { .. }
        | Expr::InstanceRef(_) => false,
    }
}

fn spread_contains_local(
    program: &Program,
    spread: &RecordSpread<ExprId>,
    def: DefId,
    visited: &mut HashSet<ExprId>,
) -> bool {
    match spread {
        RecordSpread::None => false,
        RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
            expr_contains_local_inner(program, *expr, def, visited)
        }
    }
}

fn stmt_contains_local(program: &Program, stmt: &Stmt, def: DefId) -> bool {
    match stmt {
        Stmt::Let(_, _, expr) | Stmt::Expr(expr) => expr_contains_local(program, *expr, def),
        Stmt::Module(_, stmts) => stmts
            .iter()
            .any(|stmt| stmt_contains_local(program, stmt, def)),
    }
}

fn generic_fallback_exprs(
    control: &ControlEvidenceProgram,
    exprs: impl Iterator<Item = u32>,
) -> Vec<u32> {
    let exprs = exprs.collect::<BTreeSet<_>>();
    control
        .fallbacks
        .iter()
        .filter_map(|fallback| exprs.contains(&fallback.expr.0).then_some(fallback.expr.0))
        .collect()
}

fn format_handlers(out: &mut String, handlers: &[EvidenceVmHandlerPlan]) {
    if handlers.is_empty() {
        return;
    }
    writeln!(out, "handlers:").unwrap();
    for handler in handlers {
        writeln!(
            out,
            "  e{} handler body e{} arms {}",
            handler.expr.0,
            handler.body.0,
            handler.arms.len()
        )
        .unwrap();
        for arm in &handler.arms {
            let path = arm
                .path
                .as_deref()
                .map(format_path)
                .unwrap_or_else(|| "value".to_string());
            let mode = if arm.resumptive {
                "resumptive"
            } else {
                "abortive"
            };
            let guarded = if arm.guarded { " guarded" } else { "" };
            writeln!(
                out,
                "    {path} {mode}{guarded} class {} body e{}",
                format_handler_arm_class(arm.classification),
                arm.body.0
            )
            .unwrap();
        }
    }
}

fn format_operations(out: &mut String, operations: &[EvidenceVmOperationPlan]) {
    if operations.is_empty() {
        return;
    }
    writeln!(out, "operations:").unwrap();
    for operation in operations {
        writeln!(
            out,
            "  e{} {} {} slot {} {} runtime_nodes [{}] evidence_refs {}",
            operation.expr.0,
            format_operation_kind(operation.kind),
            format_path(&operation.path),
            format_slot_key(&operation.slot),
            format_operation_lowering(&operation.lowering),
            operation
                .runtime_nodes
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(", "),
            operation.runtime_evidence_refs
        )
        .unwrap();
    }
}

fn format_functions(out: &mut String, functions: &[EvidenceVmFunctionPlan]) {
    if functions.is_empty() {
        return;
    }
    writeln!(out, "functions:").unwrap();
    for function in functions {
        writeln!(
            out,
            "  {} nodes {} evidence_refs {} signature params [{}] provides [{}] value_env [{}] requires [{}] evidence_calls [{}] operations [{}] handlers [{}] fallbacks [{}]",
            format_task_owner(function.owner),
            function.node_count,
            function.evidence_ref_count,
            format_slot_keys(&function.signature.params),
            format_slot_keys(&function.signature.provides),
            format_slot_keys(&function.signature.value_env),
            format_requirements(&function.required_evidence),
            format_call_plans(&function.calls_needing_evidence),
            format_u32_list(&function.operation_exprs),
            format_u32_list(&function.handler_exprs),
            format_u32_list(&function.fallback_exprs)
        )
        .unwrap();
    }
}

fn format_value_envs(out: &mut String, values: &[EvidenceVmValueEnvPlan]) {
    if values.is_empty() {
        return;
    }
    writeln!(out, "values:").unwrap();
    for value in values {
        writeln!(
            out,
            "  e{} {} signature captures [{}] captures [{}]",
            value.expr.0,
            format_value_env_kind(&value.kind),
            format_slot_keys(&value.signature.captures),
            format_requirements(&value.captured_evidence)
        )
        .unwrap();
    }
}

fn format_value_env_kind(kind: &EvidenceVmValueEnvKind) -> String {
    match kind {
        EvidenceVmValueEnvKind::Lambda { body } => format!("lambda body e{}", body.0),
        EvidenceVmValueEnvKind::Thunk { body } => format!("thunk body e{}", body.0),
        EvidenceVmValueEnvKind::FunctionAdapter {
            function,
            creates_callback_boundary,
            body_marker_count,
            arg_marker_count,
            ret_marker_count,
        } => format!(
            "adapter function e{} callback_boundary={} markers body:{} arg:{} ret:{}",
            function.0,
            creates_callback_boundary,
            body_marker_count,
            arg_marker_count,
            ret_marker_count
        ),
    }
}

fn format_handler_arm_class(classification: EvidenceVmHandlerArmClass) -> &'static str {
    match classification {
        EvidenceVmHandlerArmClass::Value => "value",
        EvidenceVmHandlerArmClass::Abortive => "abortive",
        EvidenceVmHandlerArmClass::TailResumptive => "tail-resumptive",
        EvidenceVmHandlerArmClass::MayYield => "may-yield",
        EvidenceVmHandlerArmClass::Fallback => "fallback",
    }
}

fn format_operation_kind(kind: EvidenceVmOperationKind) -> String {
    match kind {
        EvidenceVmOperationKind::Value => "op-value".to_string(),
        EvidenceVmOperationKind::Call { apply, callee } => {
            format!("op-call apply e{} callee e{}", apply.0, callee.0)
        }
    }
}

fn format_operation_lowering(lowering: &EvidenceVmOperationLowering) -> String {
    match lowering {
        EvidenceVmOperationLowering::DirectHandlerCall {
            handler,
            resumptive,
            handler_known,
        } => {
            let mode = if *resumptive {
                "resumptive"
            } else {
                "abortive"
            };
            format!("direct-handler e{} {mode} known={handler_known}", handler.0)
        }
        EvidenceVmOperationLowering::LexicalHandlerCandidate {
            handler,
            resumptive,
            delayed_boundary,
        } => {
            let mode = if *resumptive {
                "resumptive"
            } else {
                "abortive"
            };
            format!(
                "lexical-handler-candidate e{} {mode} delayed_boundary={delayed_boundary}",
                handler.0
            )
        }
        EvidenceVmOperationLowering::HygieneFallback {
            handler,
            resumptive,
            callback_boundary,
            delayed_boundary,
        } => {
            let mode = if *resumptive {
                "resumptive"
            } else {
                "abortive"
            };
            format!(
                "hygiene-fallback e{} {mode} callback_boundary={} delayed_boundary={}",
                handler.0, callback_boundary, delayed_boundary
            )
        }
        EvidenceVmOperationLowering::GenericFallback => "generic-fallback".to_string(),
    }
}

fn format_task_owner(owner: RuntimeEvidenceTaskOwner) -> String {
    match owner {
        RuntimeEvidenceTaskOwner::RootExpr { root_index, expr } => {
            format!("root#{root_index} e{expr}")
        }
        RuntimeEvidenceTaskOwner::InstanceBody {
            instance,
            def,
            body,
        } => format!("instance i{instance} d{def} e{body}"),
    }
}

fn format_path(path: &[String]) -> String {
    path.join("::")
}

fn format_slot_key(slot: &EvidenceVmSlotKey) -> String {
    format!(
        "{}:{}",
        format_slot_route_key(slot.route),
        format_path(&slot.family)
    )
}

fn format_slot_route_key(route: EvidenceVmSlotRouteKey) -> &'static str {
    match route {
        EvidenceVmSlotRouteKey::Positive => "positive",
        EvidenceVmSlotRouteKey::Blocked => "blocked",
        EvidenceVmSlotRouteKey::UnknownFallback => "fallback",
    }
}

fn format_slot_keys(slots: &[EvidenceVmSlotKey]) -> String {
    slots
        .iter()
        .map(format_slot_key)
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_requirements(requirements: &[EvidenceVmEvidenceRequirement]) -> String {
    requirements
        .iter()
        .map(|requirement| {
            format!(
                "{}@e{}",
                format_slot_key(&requirement.slot),
                format_u32_list(&requirement.operation_exprs)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_call_plans(calls: &[EvidenceVmCallPlan]) -> String {
    calls
        .iter()
        .map(|call| {
            format!(
                "e{}->i{}({})",
                call.apply.0,
                call.callee_instance,
                format_slot_keys(&call.required_evidence_slots)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_u32_list(values: &[u32]) -> String {
    values
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

#[derive(Debug, Clone, Copy)]
struct LexicalHandlerCandidate {
    handler: ExprId,
    resumptive: bool,
    delayed_boundary: bool,
}

struct LexicalHandlerIndex {
    by_operation_expr: HashMap<ExprId, LexicalHandlerCandidate>,
}

impl LexicalHandlerIndex {
    fn new(program: &Program, control: &ControlEvidenceProgram) -> Self {
        let handler_arms = control
            .handlers
            .iter()
            .map(|handler| {
                let arms = handler
                    .arms
                    .iter()
                    .filter_map(|arm| {
                        let path = arm.operation_path.clone()?;
                        Some((path, arm.resumptive))
                    })
                    .collect::<Vec<_>>();
                (handler.expr, arms)
            })
            .collect::<HashMap<_, _>>();
        let mut index = Self {
            by_operation_expr: HashMap::new(),
        };
        let mut context = LexicalHandlerContext::default();
        for root in &program.roots {
            match root {
                Root::Instance(_) | Root::EvalInstance(_) => {}
                Root::Expr(expr) => index.visit_expr(*expr, program, &handler_arms, &mut context),
            }
        }
        for instance in &program.instances {
            index.visit_expr(instance.entry, program, &handler_arms, &mut context);
        }
        index
    }

    fn candidate_for(&self, expr: ExprId) -> Option<LexicalHandlerCandidate> {
        self.by_operation_expr.get(&expr).copied()
    }

    fn visit_expr(
        &mut self,
        id: ExprId,
        program: &Program,
        handler_arms: &HashMap<ExprId, Vec<(Vec<String>, bool)>>,
        context: &mut LexicalHandlerContext,
    ) {
        let Some(expr) = control_expr(program, id) else {
            return;
        };
        match expr {
            Expr::EffectOp { path } => {
                if let Some(candidate) = context.candidate_for(path) {
                    self.by_operation_expr.entry(id).or_insert(candidate);
                }
            }
            Expr::Coerce { expr, .. }
            | Expr::ForceThunk { thunk: expr, .. }
            | Expr::FunctionAdapter { function: expr, .. }
            | Expr::MarkerFrame { body: expr, .. }
            | Expr::Select { base: expr, .. } => {
                self.visit_expr(*expr, program, handler_arms, context);
            }
            Expr::MakeThunk { body, .. } => {
                context.with_delayed_boundary(true, |context| {
                    self.visit_expr(*body, program, handler_arms, context);
                });
            }
            Expr::Apply { callee, arg }
            | Expr::RefSet {
                reference: callee,
                value: arg,
            } => {
                self.visit_expr(*callee, program, handler_arms, context);
                self.visit_expr(*arg, program, handler_arms, context);
            }
            Expr::Lambda { body, .. } => {
                context.with_delayed_boundary(true, |context| {
                    self.visit_expr(*body, program, handler_arms, context);
                });
            }
            Expr::Tuple(items) => {
                for item in items {
                    self.visit_expr(*item, program, handler_arms, context);
                }
            }
            Expr::Record { fields, spread } => {
                for field in fields {
                    self.visit_expr(field.value, program, handler_arms, context);
                }
                match spread {
                    RecordSpread::None => {}
                    RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                        self.visit_expr(*expr, program, handler_arms, context);
                    }
                }
            }
            Expr::PolyVariant { payloads, .. } => {
                for payload in payloads {
                    self.visit_expr(*payload, program, handler_arms, context);
                }
            }
            Expr::Case { scrutinee, arms } => {
                self.visit_expr(*scrutinee, program, handler_arms, context);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr(guard, program, handler_arms, context);
                    }
                    self.visit_expr(arm.body, program, handler_arms, context);
                }
            }
            Expr::Catch { body, arms } => {
                let pushed = handler_arms.get(&id).and_then(|arms| {
                    (!arms.is_empty()).then(|| LexicalHandlerFrame {
                        handler: id,
                        arms: arms.clone(),
                    })
                });
                if let Some(frame) = pushed {
                    context.handlers.push(frame);
                    self.visit_expr(*body, program, handler_arms, context);
                    context.handlers.pop();
                } else {
                    self.visit_expr(*body, program, handler_arms, context);
                }
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr(guard, program, handler_arms, context);
                    }
                    self.visit_expr(arm.body, program, handler_arms, context);
                }
            }
            Expr::Block(block) => self.visit_block(block, program, handler_arms, context),
            Expr::Lit(_)
            | Expr::PrimitiveOp { .. }
            | Expr::Constructor { .. }
            | Expr::Local(_)
            | Expr::InstanceRef(_) => {}
        }
    }

    fn visit_block(
        &mut self,
        block: &Block,
        program: &Program,
        handler_arms: &HashMap<ExprId, Vec<(Vec<String>, bool)>>,
        context: &mut LexicalHandlerContext,
    ) {
        for stmt in &block.stmts {
            self.visit_stmt(stmt, program, handler_arms, context);
        }
        if let Some(tail) = block.tail {
            self.visit_expr(tail, program, handler_arms, context);
        }
    }

    fn visit_stmt(
        &mut self,
        stmt: &Stmt,
        program: &Program,
        handler_arms: &HashMap<ExprId, Vec<(Vec<String>, bool)>>,
        context: &mut LexicalHandlerContext,
    ) {
        match stmt {
            Stmt::Let(_, _, expr) | Stmt::Expr(expr) => {
                self.visit_expr(*expr, program, handler_arms, context);
            }
            Stmt::Module(_, stmts) => {
                for stmt in stmts {
                    self.visit_stmt(stmt, program, handler_arms, context);
                }
            }
        }
    }
}

#[derive(Debug, Default)]
struct LexicalHandlerContext {
    handlers: Vec<LexicalHandlerFrame>,
    delayed_boundary_depth: usize,
}

impl LexicalHandlerContext {
    fn candidate_for(&self, path: &[String]) -> Option<LexicalHandlerCandidate> {
        self.handlers.iter().rev().find_map(|handler| {
            handler
                .arms
                .iter()
                .find(|(handled_path, _)| handled_path == path)
                .map(|(_, resumptive)| LexicalHandlerCandidate {
                    handler: handler.handler,
                    resumptive: *resumptive,
                    delayed_boundary: self.delayed_boundary_depth > 0,
                })
        })
    }

    fn with_delayed_boundary(&mut self, enabled: bool, f: impl FnOnce(&mut Self)) {
        if enabled {
            self.delayed_boundary_depth += 1;
        }
        f(self);
        if enabled {
            self.delayed_boundary_depth -= 1;
        }
    }
}

#[derive(Debug)]
struct LexicalHandlerFrame {
    handler: ExprId,
    arms: Vec<(Vec<String>, bool)>,
}

fn control_expr(program: &Program, id: ExprId) -> Option<&Expr> {
    program.exprs.get(id.0 as usize)
}

struct RuntimeNodeIndex<'a> {
    by_expr: BTreeMap<u32, Vec<&'a RuntimeEvidenceNode>>,
}

impl<'a> RuntimeNodeIndex<'a> {
    fn new(surface: &'a RuntimeEvidenceSurface) -> Self {
        let mut by_expr: BTreeMap<u32, Vec<&'a RuntimeEvidenceNode>> = BTreeMap::new();
        for task in &surface.tasks {
            for node in &task.nodes {
                by_expr.entry(node.expr).or_default().push(node);
            }
        }
        Self { by_expr }
    }

    fn nodes_for_expr(&self, expr: u32) -> Vec<&'a RuntimeEvidenceNode> {
        self.by_expr.get(&expr).cloned().unwrap_or_default()
    }
}
