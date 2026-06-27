use mono::{Program, StackWeight, Type};
use poly::expr as poly_expr;
use serde::{Deserialize, Serialize};
use std::fmt::Write as _;

use super::{SolvedTask, TypeclassResolution};

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct SpecializeOutput {
    pub program: Program,
    pub runtime_evidence: RuntimeEvidenceSurface,
}

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct RuntimeEvidenceSurface {
    pub tasks: Vec<RuntimeEvidenceTask>,
}

impl RuntimeEvidenceSurface {
    pub(super) fn push_solved_task(
        &mut self,
        owner: RuntimeEvidenceTaskOwner,
        solved: &SolvedTask,
    ) {
        self.tasks
            .push(RuntimeEvidenceTask::from_solved(owner, solved));
    }
}

pub fn format_runtime_evidence_surface(surface: &RuntimeEvidenceSurface) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "runtime evidence tasks [{}]", surface.tasks.len());
    for task in &surface.tasks {
        let _ = writeln!(out, "{}", format_task_header(task));
        for expr in &task.expr_types {
            let consumer = expr
                .consumer
                .as_ref()
                .map(mono::dump::dump_type)
                .unwrap_or_else(|| "_".to_string());
            let _ = writeln!(
                out,
                "  expr e{} actual {} consumer {} stack_weights {}",
                expr.expr,
                mono::dump::dump_type(&expr.actual),
                consumer,
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

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RuntimeEvidenceTask {
    pub owner: RuntimeEvidenceTaskOwner,
    pub expr_types: Vec<RuntimeEvidenceExprType>,
    pub ref_signatures: Vec<RuntimeEvidenceTypeAtExpr>,
    pub select_signatures: Vec<RuntimeEvidenceTypeAtExpr>,
    pub pat_ref_signatures: Vec<RuntimeEvidenceTypeAtPat>,
    pub typeclass_resolutions: Vec<RuntimeEvidenceTypeclassResolution>,
    pub raw_thunk_computations: Vec<u32>,
}

impl RuntimeEvidenceTask {
    fn from_solved(owner: RuntimeEvidenceTaskOwner, solved: &SolvedTask) -> Self {
        let mut expr_types = solved
            .exprs
            .iter()
            .map(|(expr, ty)| RuntimeEvidenceExprType::new(*expr, &ty.actual, ty.consumer.as_ref()))
            .collect::<Vec<_>>();
        expr_types.sort_by_key(|item| item.expr);

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
            expr_types,
            ref_signatures,
            select_signatures,
            pat_ref_signatures,
            typeclass_resolutions,
            raw_thunk_computations,
        }
    }
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
    pub stack_weights: Vec<RuntimeEvidenceStackWeight>,
}

impl RuntimeEvidenceExprType {
    fn new(expr: poly_expr::ExprId, actual: &Type, consumer: Option<&Type>) -> Self {
        let mut stack_weights = Vec::new();
        collect_stack_weights(
            RuntimeEvidenceTypeRole::Actual,
            actual,
            &mut Vec::new(),
            &mut stack_weights,
        );
        if let Some(consumer) = consumer {
            collect_stack_weights(
                RuntimeEvidenceTypeRole::Consumer,
                consumer,
                &mut Vec::new(),
                &mut stack_weights,
            );
        }
        Self {
            expr: expr.0,
            actual: actual.clone(),
            consumer: consumer.cloned(),
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
