use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

use control_vm::{
    Block, ControlEffectUseKind, ControlEvidenceProgram, ControlEvidenceRoute, Expr, ExprId,
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
    pub(crate) body: ExprId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmOperationPlan {
    pub(crate) expr: ExprId,
    pub(crate) path: Vec<String>,
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
    pub(crate) path: Vec<String>,
    pub(crate) operation_exprs: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmCallPlan {
    pub(crate) apply: ExprId,
    pub(crate) callee_instance: u32,
    pub(crate) required_evidence_paths: Vec<Vec<String>>,
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
                .map(|arm| EvidenceVmHandlerArmPlan {
                    path: arm.operation_path.clone(),
                    resumptive: arm.resumptive,
                    guarded: arm.guarded,
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
            EvidenceVmOperationPlan {
                expr: effect.expr,
                path: effect.path.clone(),
                kind: operation_kind(effect.kind),
                lowering: operation_lowering(
                    effect.expr,
                    &effect.route,
                    &handler_exprs,
                    &lexical_handlers,
                ),
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

    let summary = summarize_plan(control, surface, &operations, &functions);
    EvidenceVmPlan {
        summary,
        handlers,
        operations,
        functions,
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
        "  runtime_tasks: {} runtime_nodes: {} runtime_evidence_refs: {}",
        summary.runtime_tasks, summary.runtime_nodes, summary.runtime_evidence_refs
    )
    .unwrap();
    format_handlers(&mut out, &plan.handlers);
    format_operations(&mut out, &plan.operations);
    format_functions(&mut out, &plan.functions);
    out
}

fn summarize_plan(
    control: &ControlEvidenceProgram,
    surface: &RuntimeEvidenceSurface,
    operations: &[EvidenceVmOperationPlan],
    functions: &[EvidenceVmFunctionPlan],
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
    EvidenceVmFunctionPlan {
        owner: task.owner,
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
            (!function.required_evidence.is_empty()).then(|| {
                (
                    instance,
                    function
                        .required_evidence
                        .iter()
                        .map(|requirement| requirement.path.clone())
                        .collect::<Vec<_>>(),
                )
            })
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
    requirements_by_instance: &HashMap<u32, Vec<Vec<String>>>,
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
                && let Some(required_evidence_paths) = requirements_by_instance.get(&instance.0)
            {
                out.push(EvidenceVmCallPlan {
                    apply: expr,
                    callee_instance: instance.0,
                    required_evidence_paths: required_evidence_paths.clone(),
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
    requirements_by_instance: &HashMap<u32, Vec<Vec<String>>>,
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
    requirements_by_instance: &HashMap<u32, Vec<Vec<String>>>,
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
    let mut by_path = BTreeMap::<Vec<String>, Vec<u32>>::new();
    for node in nodes {
        if let RuntimeEvidenceNodeKind::OperationCall { path, .. } = &node.kind
            && !provided.contains(path)
        {
            by_path.entry(path.clone()).or_default().push(node.expr);
        }
    }
    by_path
        .into_iter()
        .map(|(path, operation_exprs)| EvidenceVmEvidenceRequirement {
            path,
            operation_exprs,
        })
        .collect()
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
            writeln!(out, "    {path} {mode}{guarded} body e{}", arm.body.0).unwrap();
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
            "  e{} {} {} {} runtime_nodes [{}] evidence_refs {}",
            operation.expr.0,
            format_operation_kind(operation.kind),
            format_path(&operation.path),
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
            "  {} nodes {} evidence_refs {} requires [{}] provides [{}] evidence_calls [{}] operations [{}] handlers [{}] fallbacks [{}]",
            format_task_owner(function.owner),
            function.node_count,
            function.evidence_ref_count,
            format_requirements(&function.required_evidence),
            format_paths(&function.provided_evidence_paths),
            format_call_plans(&function.calls_needing_evidence),
            format_u32_list(&function.operation_exprs),
            format_u32_list(&function.handler_exprs),
            format_u32_list(&function.fallback_exprs)
        )
        .unwrap();
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

fn format_paths(paths: &[Vec<String>]) -> String {
    paths
        .iter()
        .map(|path| format_path(path))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_requirements(requirements: &[EvidenceVmEvidenceRequirement]) -> String {
    requirements
        .iter()
        .map(|requirement| {
            format!(
                "{}@e{}",
                format_path(&requirement.path),
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
                format_paths(&call.required_evidence_paths)
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
