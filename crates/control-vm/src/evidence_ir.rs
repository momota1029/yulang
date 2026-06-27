//! Evidence-oriented view of the lowered control IR.
//!
//! This pass does not execute or rewrite the program.  It records the static
//! evidence that a handler-passing backend would need before it can replace the
//! generic control VM for a local region.

use std::collections::HashSet;
use std::fmt::Write;

use mono::{FunctionAdapterHygiene, GuardMarker};
use serde::{Deserialize, Serialize};

use crate::ir::{
    Block, CatchArm, Expr, ExprId, InstanceId, Pat, Program, RecordSpread, Root, Stmt,
};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ControlEvidenceProgram {
    pub roots: Vec<Root>,
    pub instances: Vec<ControlEvidenceInstance>,
    pub handlers: Vec<ControlHandlerEvidence>,
    pub effects: Vec<ControlEffectEvidence>,
    pub adapters: Vec<ControlAdapterEvidence>,
    pub delayed_boundaries: Vec<ControlDelayedBoundary>,
    pub fallbacks: Vec<ControlFallbackEvidence>,
}

impl ControlEvidenceProgram {
    pub fn from_program(program: &Program) -> Self {
        ControlEvidenceBuilder::new(program).finish()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ControlEvidenceInstance {
    pub instance: InstanceId,
    pub entry: ExprId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ControlHandlerEvidence {
    pub expr: ExprId,
    pub body: ExprId,
    pub arms: Vec<ControlHandlerArmEvidence>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ControlHandlerArmEvidence {
    pub operation_path: Option<Vec<String>>,
    pub resumptive: bool,
    pub guarded: bool,
    pub body: ExprId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ControlEffectEvidence {
    pub expr: ExprId,
    pub path: Vec<String>,
    pub kind: ControlEffectUseKind,
    pub route: ControlEvidenceRoute,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ControlEffectUseKind {
    OperationValue,
    OperationCall { apply: ExprId, callee: ExprId },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ControlEvidenceRoute {
    Direct {
        handler: ExprId,
        resumptive: bool,
    },
    Blocked {
        handler: ExprId,
        resumptive: bool,
        callback_boundary: bool,
        delayed_boundary: bool,
    },
    Unhandled,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ControlAdapterEvidence {
    pub expr: ExprId,
    pub function: ExprId,
    pub body_markers: Vec<GuardMarker>,
    pub arg_markers: Vec<GuardMarker>,
    pub ret_markers: Vec<GuardMarker>,
    pub creates_callback_boundary: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ControlDelayedBoundary {
    pub expr: ExprId,
    pub body: ExprId,
    pub kind: ControlDelayedBoundaryKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ControlDelayedBoundaryKind {
    Lambda,
    Thunk,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ControlFallbackEvidence {
    pub expr: ExprId,
    pub kind: ControlFallbackKind,
    pub under_handler: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ControlFallbackKind {
    DynamicCall,
    DynamicForce,
    MissingExprRef,
    CycleExprRef,
    MissingInstanceRef,
    CycleInstanceRef,
}

pub fn format_control_evidence_program(program: &ControlEvidenceProgram) -> String {
    let mut out = String::new();
    writeln!(
        &mut out,
        "control evidence roots {}",
        format_roots(&program.roots)
    )
    .unwrap();
    if !program.instances.is_empty() {
        writeln!(&mut out, "instances:").unwrap();
        for instance in &program.instances {
            writeln!(
                &mut out,
                "  i{} entry e{}",
                instance.instance.0, instance.entry.0
            )
            .unwrap();
        }
    }
    if !program.handlers.is_empty() {
        writeln!(&mut out, "handlers:").unwrap();
        for handler in &program.handlers {
            writeln!(
                &mut out,
                "  e{} catch body e{}",
                handler.expr.0, handler.body.0
            )
            .unwrap();
            for arm in &handler.arms {
                let path = arm
                    .operation_path
                    .as_deref()
                    .map(format_path)
                    .unwrap_or_else(|| "value".to_string());
                let resume = if arm.resumptive {
                    "resumptive"
                } else {
                    "abortive"
                };
                let guard = if arm.guarded { " guarded" } else { "" };
                writeln!(
                    &mut out,
                    "    arm {path} {resume}{guard} body e{}",
                    arm.body.0
                )
                .unwrap();
            }
        }
    }
    if !program.effects.is_empty() {
        writeln!(&mut out, "effects:").unwrap();
        for effect in &program.effects {
            writeln!(
                &mut out,
                "  e{} {} {} {}",
                effect.expr.0,
                format_effect_kind(effect.kind),
                format_path(&effect.path),
                format_route(&effect.route)
            )
            .unwrap();
        }
    }
    if !program.adapters.is_empty() {
        writeln!(&mut out, "adapters:").unwrap();
        for adapter in &program.adapters {
            writeln!(
                &mut out,
                "  e{} adapter function e{} boundary={} body={} arg={} ret={}",
                adapter.expr.0,
                adapter.function.0,
                adapter.creates_callback_boundary,
                adapter.body_markers.len(),
                adapter.arg_markers.len(),
                adapter.ret_markers.len()
            )
            .unwrap();
            format_markers(&mut out, "body", &adapter.body_markers);
            format_markers(&mut out, "arg", &adapter.arg_markers);
            format_markers(&mut out, "ret", &adapter.ret_markers);
        }
    }
    if !program.delayed_boundaries.is_empty() {
        writeln!(&mut out, "delayed boundaries:").unwrap();
        for boundary in &program.delayed_boundaries {
            let kind = match boundary.kind {
                ControlDelayedBoundaryKind::Lambda => "lambda",
                ControlDelayedBoundaryKind::Thunk => "thunk",
            };
            writeln!(
                &mut out,
                "  e{} {kind} body e{}",
                boundary.expr.0, boundary.body.0
            )
            .unwrap();
        }
    }
    if !program.fallbacks.is_empty() {
        writeln!(&mut out, "fallbacks:").unwrap();
        for fallback in &program.fallbacks {
            writeln!(
                &mut out,
                "  e{} {:?} under_handler={}",
                fallback.expr.0, fallback.kind, fallback.under_handler
            )
            .unwrap();
        }
    }
    out
}

struct ControlEvidenceBuilder<'a> {
    program: &'a Program,
    evidence: ControlEvidenceProgram,
    recorded_handlers: HashSet<ExprId>,
    recorded_adapters: HashSet<ExprId>,
    recorded_delayed_boundaries: HashSet<ExprId>,
    recorded_effects: HashSet<ControlEffectEvidence>,
    recorded_fallbacks: HashSet<ControlFallbackEvidence>,
    active_exprs: HashSet<ExprId>,
    active_instances: HashSet<InstanceId>,
}

impl<'a> ControlEvidenceBuilder<'a> {
    fn new(program: &'a Program) -> Self {
        Self {
            program,
            evidence: ControlEvidenceProgram {
                roots: program.roots.clone(),
                instances: Vec::new(),
                handlers: Vec::new(),
                effects: Vec::new(),
                adapters: Vec::new(),
                delayed_boundaries: Vec::new(),
                fallbacks: Vec::new(),
            },
            recorded_handlers: HashSet::new(),
            recorded_adapters: HashSet::new(),
            recorded_delayed_boundaries: HashSet::new(),
            recorded_effects: HashSet::new(),
            recorded_fallbacks: HashSet::new(),
            active_exprs: HashSet::new(),
            active_instances: HashSet::new(),
        }
    }

    fn finish(mut self) -> ControlEvidenceProgram {
        self.evidence.instances = self
            .program
            .instances
            .iter()
            .map(|instance| ControlEvidenceInstance {
                instance: instance.id,
                entry: instance.entry,
            })
            .collect();
        let mut context = EvidenceContext::default();
        for root in &self.program.roots {
            match root {
                Root::Instance(instance) | Root::EvalInstance(instance) => {
                    self.visit_instance_entry(*instance, &mut context)
                }
                Root::Expr(expr) => self.visit_expr_id(*expr, &mut context),
            }
        }
        self.evidence
    }

    fn visit_expr_id(&mut self, id: ExprId, context: &mut EvidenceContext) {
        let Some(expr) = self.program.exprs.get(id.0 as usize) else {
            self.record_fallback(id, ControlFallbackKind::MissingExprRef, context);
            return;
        };
        if !self.active_exprs.insert(id) {
            self.record_fallback(id, ControlFallbackKind::CycleExprRef, context);
            return;
        }
        self.visit_expr(id, expr, context);
        self.active_exprs.remove(&id);
    }

    fn visit_expr(&mut self, id: ExprId, expr: &Expr, context: &mut EvidenceContext) {
        match expr {
            Expr::EffectOp { path } => {
                self.record_effect(id, path, ControlEffectUseKind::OperationValue, context)
            }
            Expr::Coerce { expr, .. } => self.visit_expr_id(*expr, context),
            Expr::MakeThunk { body, .. } => {
                self.record_delayed_boundary(id, *body, ControlDelayedBoundaryKind::Thunk, context)
            }
            Expr::ForceThunk { thunk, .. } => {
                self.visit_expr_id(*thunk, context);
                if !self.visit_known_force_site(*thunk, context) {
                    self.record_fallback(id, ControlFallbackKind::DynamicForce, context);
                }
            }
            Expr::FunctionAdapter {
                function, hygiene, ..
            } => self.visit_function_adapter(id, *function, hygiene, context),
            Expr::MarkerFrame { body, .. } => self.visit_expr_id(*body, context),
            Expr::Apply { callee, arg } => {
                self.visit_expr_id(*callee, context);
                self.visit_expr_id(*arg, context);
                if !self.visit_known_call_site(id, *callee, context) {
                    self.record_fallback(id, ControlFallbackKind::DynamicCall, context);
                }
            }
            Expr::RefSet { reference, value } => {
                self.visit_expr_id(*reference, context);
                self.visit_expr_id(*value, context);
            }
            Expr::Lambda { param, body } => {
                self.visit_pat(param, context);
                self.record_delayed_boundary(
                    id,
                    *body,
                    ControlDelayedBoundaryKind::Lambda,
                    context,
                );
            }
            Expr::Tuple(items) => self.visit_expr_ids(items, context),
            Expr::Record { fields, spread } => {
                for field in fields {
                    self.visit_expr_id(field.value, context);
                }
                self.visit_expr_spread(spread, context);
            }
            Expr::PolyVariant { payloads, .. } => self.visit_expr_ids(payloads, context),
            Expr::Select { base, .. } => self.visit_expr_id(*base, context),
            Expr::Case { scrutinee, arms } => {
                self.visit_expr_id(*scrutinee, context);
                for arm in arms {
                    self.visit_pat(&arm.pat, context);
                    if let Some(guard) = arm.guard {
                        self.visit_expr_id(guard, context);
                    }
                    self.visit_expr_id(arm.body, context);
                }
            }
            Expr::Catch { body, arms } => self.visit_catch(id, *body, arms, context),
            Expr::Block(block) => self.visit_block(block, context),
            Expr::InstanceRef(instance) => self.visit_instance_entry(*instance, context),
            Expr::Lit(_) | Expr::PrimitiveOp { .. } | Expr::Constructor { .. } | Expr::Local(_) => {
            }
        }
    }

    fn visit_expr_ids(&mut self, ids: &[ExprId], context: &mut EvidenceContext) {
        for id in ids {
            self.visit_expr_id(*id, context);
        }
    }

    fn visit_expr_spread(&mut self, spread: &RecordSpread<ExprId>, context: &mut EvidenceContext) {
        match spread {
            RecordSpread::None => {}
            RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                self.visit_expr_id(*expr, context)
            }
        }
    }

    fn visit_catch(
        &mut self,
        id: ExprId,
        body: ExprId,
        arms: &[CatchArm],
        context: &mut EvidenceContext,
    ) {
        if self.recorded_handlers.insert(id) {
            self.evidence.handlers.push(ControlHandlerEvidence {
                expr: id,
                body,
                arms: arms
                    .iter()
                    .map(|arm| ControlHandlerArmEvidence {
                        operation_path: arm.operation_path.clone(),
                        resumptive: arm.continuation.is_some(),
                        guarded: arm.guard.is_some(),
                        body: arm.body,
                    })
                    .collect(),
            });
        }

        if let Some(frame) = EvidenceHandlerFrame::from_arms(
            id,
            arms,
            context.callback_boundary_depth,
            context.delayed_boundary_depth,
        ) {
            context.handlers.push(frame);
            self.visit_expr_id(body, context);
            context.handlers.pop();
        } else {
            self.visit_expr_id(body, context);
        }

        for arm in arms {
            self.visit_pat(&arm.pat, context);
            if let Some(continuation) = &arm.continuation {
                self.visit_pat(continuation, context);
            }
            if let Some(guard) = arm.guard {
                self.visit_expr_id(guard, context);
            }
            self.visit_expr_id(arm.body, context);
        }
    }

    fn visit_function_adapter(
        &mut self,
        id: ExprId,
        function: ExprId,
        hygiene: &FunctionAdapterHygiene,
        context: &mut EvidenceContext,
    ) {
        let creates_callback_boundary = hygiene_has_boundary_markers(hygiene);
        if self.recorded_adapters.insert(id) {
            self.evidence.adapters.push(ControlAdapterEvidence {
                expr: id,
                function,
                body_markers: hygiene.markers.clone(),
                arg_markers: hygiene.arg_markers.clone(),
                ret_markers: hygiene.ret_markers.clone(),
                creates_callback_boundary,
            });
        }
        if creates_callback_boundary {
            context.callback_boundary_depth += 1;
            self.visit_expr_id(function, context);
            context.callback_boundary_depth -= 1;
        } else {
            self.visit_expr_id(function, context);
        }
    }

    fn record_delayed_boundary(
        &mut self,
        id: ExprId,
        body: ExprId,
        kind: ControlDelayedBoundaryKind,
        context: &mut EvidenceContext,
    ) {
        if self.recorded_delayed_boundaries.insert(id) {
            self.evidence
                .delayed_boundaries
                .push(ControlDelayedBoundary {
                    expr: id,
                    body,
                    kind,
                });
        }
        context.delayed_boundary_depth += 1;
        self.visit_expr_id(body, context);
        context.delayed_boundary_depth -= 1;
    }

    fn visit_known_call_site(
        &mut self,
        apply: ExprId,
        callee: ExprId,
        context: &mut EvidenceContext,
    ) -> bool {
        let Some(expr) = self.program.exprs.get(callee.0 as usize) else {
            self.record_fallback(callee, ControlFallbackKind::MissingExprRef, context);
            return false;
        };
        match expr {
            Expr::EffectOp { path } => {
                self.record_effect(
                    callee,
                    path,
                    ControlEffectUseKind::OperationCall { apply, callee },
                    context,
                );
                true
            }
            Expr::Lambda { param, body } => {
                self.visit_pat(param, context);
                self.visit_expr_id(*body, context);
                true
            }
            Expr::InstanceRef(instance) => {
                self.visit_known_instance_call_site(apply, *instance, context)
            }
            Expr::PrimitiveOp { .. } | Expr::Constructor { .. } => true,
            _ => false,
        }
    }

    fn visit_known_instance_call_site(
        &mut self,
        apply: ExprId,
        instance: InstanceId,
        context: &mut EvidenceContext,
    ) -> bool {
        let Some(entry) = self.instance_entry(instance) else {
            self.record_fallback(
                ExprId(instance.0),
                ControlFallbackKind::MissingInstanceRef,
                context,
            );
            return false;
        };
        if !self.active_instances.insert(instance) {
            self.record_fallback(
                ExprId(instance.0),
                ControlFallbackKind::CycleInstanceRef,
                context,
            );
            return false;
        }
        let known = self.visit_known_callee_entry(apply, entry, context);
        self.active_instances.remove(&instance);
        known
    }

    fn visit_known_callee_entry(
        &mut self,
        apply: ExprId,
        entry: ExprId,
        context: &mut EvidenceContext,
    ) -> bool {
        let Some(expr) = self.program.exprs.get(entry.0 as usize) else {
            self.record_fallback(entry, ControlFallbackKind::MissingExprRef, context);
            return false;
        };
        match expr {
            Expr::EffectOp { path } => {
                self.record_effect(
                    entry,
                    path,
                    ControlEffectUseKind::OperationCall {
                        apply,
                        callee: entry,
                    },
                    context,
                );
                true
            }
            Expr::Lambda { param, body } => {
                self.visit_pat(param, context);
                self.visit_expr_id(*body, context);
                true
            }
            Expr::PrimitiveOp { .. } | Expr::Constructor { .. } => true,
            _ => false,
        }
    }

    fn visit_known_force_site(&mut self, thunk: ExprId, context: &mut EvidenceContext) -> bool {
        let Some(expr) = self.program.exprs.get(thunk.0 as usize) else {
            self.record_fallback(thunk, ControlFallbackKind::MissingExprRef, context);
            return false;
        };
        match expr {
            Expr::MakeThunk { body, .. } => {
                self.visit_expr_id(*body, context);
                true
            }
            Expr::InstanceRef(instance) => self.visit_known_instance_force_site(*instance, context),
            _ => false,
        }
    }

    fn visit_known_instance_force_site(
        &mut self,
        instance: InstanceId,
        context: &mut EvidenceContext,
    ) -> bool {
        let Some(entry) = self.instance_entry(instance) else {
            self.record_fallback(
                ExprId(instance.0),
                ControlFallbackKind::MissingInstanceRef,
                context,
            );
            return false;
        };
        if !self.active_instances.insert(instance) {
            self.record_fallback(
                ExprId(instance.0),
                ControlFallbackKind::CycleInstanceRef,
                context,
            );
            return false;
        }
        let known = self.visit_known_force_entry(entry, context);
        self.active_instances.remove(&instance);
        known
    }

    fn visit_known_force_entry(&mut self, entry: ExprId, context: &mut EvidenceContext) -> bool {
        let Some(expr) = self.program.exprs.get(entry.0 as usize) else {
            self.record_fallback(entry, ControlFallbackKind::MissingExprRef, context);
            return false;
        };
        match expr {
            Expr::MakeThunk { body, .. } => {
                self.visit_expr_id(*body, context);
                true
            }
            _ => false,
        }
    }

    fn visit_instance_entry(&mut self, instance: InstanceId, context: &mut EvidenceContext) {
        let Some(entry) = self.instance_entry(instance) else {
            self.record_fallback(
                ExprId(instance.0),
                ControlFallbackKind::MissingInstanceRef,
                context,
            );
            return;
        };
        if !self.active_instances.insert(instance) {
            self.record_fallback(
                ExprId(instance.0),
                ControlFallbackKind::CycleInstanceRef,
                context,
            );
            return;
        }
        self.visit_expr_id(entry, context);
        self.active_instances.remove(&instance);
    }

    fn instance_entry(&self, instance: InstanceId) -> Option<ExprId> {
        self.program
            .instances
            .get(instance.0 as usize)
            .map(|instance| instance.entry)
    }

    fn visit_block(&mut self, block: &Block, context: &mut EvidenceContext) {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let(_, pat, expr) => {
                    self.visit_expr_id(*expr, context);
                    self.visit_pat(pat, context);
                }
                Stmt::Expr(expr) => self.visit_expr_id(*expr, context),
                Stmt::Module(_, stmts) => self.visit_stmts(stmts, context),
            }
        }
        if let Some(tail) = block.tail {
            self.visit_expr_id(tail, context);
        }
    }

    fn visit_stmts(&mut self, stmts: &[Stmt], context: &mut EvidenceContext) {
        for stmt in stmts {
            match stmt {
                Stmt::Let(_, pat, expr) => {
                    self.visit_expr_id(*expr, context);
                    self.visit_pat(pat, context);
                }
                Stmt::Expr(expr) => self.visit_expr_id(*expr, context),
                Stmt::Module(_, nested) => self.visit_stmts(nested, context),
            }
        }
    }

    fn visit_pat(&mut self, pat: &Pat, context: &mut EvidenceContext) {
        match pat {
            Pat::Tuple(items) => {
                for item in items {
                    self.visit_pat(item, context);
                }
            }
            Pat::List {
                prefix,
                spread,
                suffix,
            } => {
                for item in prefix {
                    self.visit_pat(item, context);
                }
                if let Some(spread) = spread {
                    self.visit_pat(spread, context);
                }
                for item in suffix {
                    self.visit_pat(item, context);
                }
            }
            Pat::Record { fields, .. } => {
                for field in fields {
                    self.visit_pat(&field.pat, context);
                    if let Some(default) = field.default {
                        self.visit_expr_id(default, context);
                    }
                }
            }
            Pat::PolyVariant(_, payloads) | Pat::Con(_, payloads) => {
                for payload in payloads {
                    self.visit_pat(payload, context);
                }
            }
            Pat::Or(left, right) => {
                self.visit_pat(left, context);
                self.visit_pat(right, context);
            }
            Pat::As(inner, _) => self.visit_pat(inner, context),
            Pat::Wild | Pat::Lit(_) | Pat::Ref(_) | Pat::Var(_) => {}
        }
    }

    fn record_effect(
        &mut self,
        expr: ExprId,
        path: &[String],
        kind: ControlEffectUseKind,
        context: &EvidenceContext,
    ) {
        let evidence = ControlEffectEvidence {
            expr,
            path: path.to_vec(),
            kind,
            route: classify_route(path, context),
        };
        if self.recorded_effects.insert(evidence.clone()) {
            self.evidence.effects.push(evidence);
        }
    }

    fn record_fallback(
        &mut self,
        expr: ExprId,
        kind: ControlFallbackKind,
        context: &EvidenceContext,
    ) {
        let evidence = ControlFallbackEvidence {
            expr,
            kind,
            under_handler: context.has_handler(),
        };
        if self.recorded_fallbacks.insert(evidence) {
            self.evidence.fallbacks.push(evidence);
        }
    }
}

#[derive(Default)]
struct EvidenceContext {
    handlers: Vec<EvidenceHandlerFrame>,
    callback_boundary_depth: u32,
    delayed_boundary_depth: u32,
}

impl EvidenceContext {
    fn has_handler(&self) -> bool {
        !self.handlers.is_empty()
    }

    fn nearest_handler(&self, path: &[String]) -> Option<EvidenceHandlerMatch> {
        for frame in self.handlers.iter().rev() {
            if let Some(resumptive) = frame.resumptive_for(path) {
                return Some(EvidenceHandlerMatch {
                    handler: frame.expr,
                    resumptive,
                    callback_boundary_depth_at_entry: frame.callback_boundary_depth_at_entry,
                    delayed_boundary_depth_at_entry: frame.delayed_boundary_depth_at_entry,
                });
            }
        }
        None
    }
}

fn classify_route(path: &[String], context: &EvidenceContext) -> ControlEvidenceRoute {
    let Some(handler) = context.nearest_handler(path) else {
        return ControlEvidenceRoute::Unhandled;
    };
    let callback_boundary =
        context.callback_boundary_depth > handler.callback_boundary_depth_at_entry;
    let delayed_boundary = context.delayed_boundary_depth > handler.delayed_boundary_depth_at_entry;
    if callback_boundary || delayed_boundary {
        ControlEvidenceRoute::Blocked {
            handler: handler.handler,
            resumptive: handler.resumptive,
            callback_boundary,
            delayed_boundary,
        }
    } else {
        ControlEvidenceRoute::Direct {
            handler: handler.handler,
            resumptive: handler.resumptive,
        }
    }
}

struct EvidenceHandlerFrame {
    expr: ExprId,
    arms: Vec<EvidenceHandlerArmShape>,
    callback_boundary_depth_at_entry: u32,
    delayed_boundary_depth_at_entry: u32,
}

impl EvidenceHandlerFrame {
    fn from_arms(
        expr: ExprId,
        arms: &[CatchArm],
        callback_boundary_depth_at_entry: u32,
        delayed_boundary_depth_at_entry: u32,
    ) -> Option<Self> {
        let arms = arms
            .iter()
            .filter_map(|arm| {
                arm.operation_path
                    .as_ref()
                    .map(|path| EvidenceHandlerArmShape {
                        path: path.clone(),
                        resumptive: arm.continuation.is_some(),
                    })
            })
            .collect::<Vec<_>>();
        (!arms.is_empty()).then_some(Self {
            expr,
            arms,
            callback_boundary_depth_at_entry,
            delayed_boundary_depth_at_entry,
        })
    }

    fn resumptive_for(&self, path: &[String]) -> Option<bool> {
        let mut found = false;
        let mut resumptive = false;
        for arm in &self.arms {
            if arm.path == path {
                found = true;
                resumptive |= arm.resumptive;
            }
        }
        found.then_some(resumptive)
    }
}

struct EvidenceHandlerArmShape {
    path: Vec<String>,
    resumptive: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EvidenceHandlerMatch {
    handler: ExprId,
    resumptive: bool,
    callback_boundary_depth_at_entry: u32,
    delayed_boundary_depth_at_entry: u32,
}

fn hygiene_has_boundary_markers(hygiene: &FunctionAdapterHygiene) -> bool {
    !hygiene.markers.is_empty()
        || !hygiene.arg_markers.is_empty()
        || !hygiene.ret_markers.is_empty()
}

fn format_roots(roots: &[Root]) -> String {
    let mut parts = Vec::new();
    for root in roots {
        let part = match root {
            Root::Instance(instance) => format!("instance i{}", instance.0),
            Root::EvalInstance(instance) => format!("eval i{}", instance.0),
            Root::Expr(expr) => format!("expr e{}", expr.0),
        };
        parts.push(part);
    }
    format!("[{}]", parts.join(", "))
}

fn format_path(path: &[String]) -> String {
    path.join("::")
}

fn format_effect_kind(kind: ControlEffectUseKind) -> String {
    match kind {
        ControlEffectUseKind::OperationValue => "op-value".to_string(),
        ControlEffectUseKind::OperationCall { apply, callee } => {
            format!("op-call apply=e{} callee=e{}", apply.0, callee.0)
        }
    }
}

fn format_route(route: &ControlEvidenceRoute) -> String {
    match route {
        ControlEvidenceRoute::Direct {
            handler,
            resumptive,
        } => format!("direct handler=e{} resumptive={resumptive}", handler.0),
        ControlEvidenceRoute::Blocked {
            handler,
            resumptive,
            callback_boundary,
            delayed_boundary,
        } => format!(
            "blocked handler=e{} resumptive={resumptive} callback={callback_boundary} delayed={delayed_boundary}",
            handler.0
        ),
        ControlEvidenceRoute::Unhandled => "unhandled".to_string(),
    }
}

fn format_markers(out: &mut String, label: &str, markers: &[GuardMarker]) {
    for marker in markers {
        writeln!(
            out,
            "    {label} {} depth={} own={} foreign={} resume={}",
            format_path(&marker.path),
            marker.depth,
            marker.guard_own_path,
            marker.guard_foreign_path,
            marker.preserve_own_on_resume
        )
        .unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{CatchArm, Expr, Pat, Program};

    #[test]
    fn records_direct_blocked_and_unhandled_effect_routes() {
        let program = Program {
            roots: vec![
                Root::Expr(ExprId(1)),
                Root::Expr(ExprId(4)),
                Root::Expr(ExprId(7)),
                Root::Expr(ExprId(8)),
            ],
            instances: Vec::new(),
            exprs: vec![
                Expr::EffectOp {
                    path: vec!["flip".into(), "coin".into()],
                },
                Expr::Catch {
                    body: ExprId(0),
                    arms: vec![handler_arm(false, 9)],
                },
                Expr::EffectOp {
                    path: vec!["flip".into(), "coin".into()],
                },
                Expr::Lambda {
                    param: Pat::Wild,
                    body: ExprId(2),
                },
                Expr::Catch {
                    body: ExprId(3),
                    arms: vec![handler_arm(false, 9)],
                },
                Expr::EffectOp {
                    path: vec!["flip".into(), "coin".into()],
                },
                Expr::FunctionAdapter {
                    source: mono::Type::unit(),
                    target: mono::Type::unit(),
                    function: ExprId(5),
                    hygiene: FunctionAdapterHygiene {
                        markers: vec![GuardMarker {
                            path: vec!["flip".into()],
                            depth: 0,
                            guard_own_path: true,
                            guard_foreign_path: true,
                            preserve_own_on_resume: false,
                        }],
                        arg_markers: Vec::new(),
                        ret_markers: Vec::new(),
                    },
                },
                Expr::Catch {
                    body: ExprId(6),
                    arms: vec![handler_arm(true, 9)],
                },
                Expr::EffectOp {
                    path: vec!["host".into(), "print".into()],
                },
                Expr::Lit(mono::Lit::Unit),
            ],
        };

        let evidence = ControlEvidenceProgram::from_program(&program);

        assert_eq!(evidence.handlers.len(), 3);
        assert_eq!(evidence.adapters.len(), 1);
        assert_eq!(evidence.delayed_boundaries.len(), 1);
        assert_eq!(evidence.effects.len(), 4);
        assert!(matches!(
            evidence.effects[0].route,
            ControlEvidenceRoute::Direct {
                handler: ExprId(1),
                resumptive: false,
            }
        ));
        assert!(matches!(
            evidence.effects[1].route,
            ControlEvidenceRoute::Blocked {
                handler: ExprId(4),
                callback_boundary: false,
                delayed_boundary: true,
                ..
            }
        ));
        assert!(matches!(
            evidence.effects[2].route,
            ControlEvidenceRoute::Blocked {
                handler: ExprId(7),
                callback_boundary: true,
                delayed_boundary: false,
                resumptive: true,
            }
        ));
        assert!(matches!(
            evidence.effects[3].route,
            ControlEvidenceRoute::Unhandled
        ));
    }

    #[test]
    fn records_known_effect_call_sites_as_operation_calls() {
        let program = Program {
            roots: vec![Root::Expr(ExprId(3))],
            instances: Vec::new(),
            exprs: vec![
                Expr::EffectOp {
                    path: vec!["flip".into(), "coin".into()],
                },
                Expr::Lit(mono::Lit::Unit),
                Expr::Apply {
                    callee: ExprId(0),
                    arg: ExprId(1),
                },
                Expr::Catch {
                    body: ExprId(2),
                    arms: vec![handler_arm(true, 1)],
                },
            ],
        };

        let evidence = ControlEvidenceProgram::from_program(&program);

        assert!(evidence.effects.iter().any(|effect| matches!(
            effect.kind,
            ControlEffectUseKind::OperationCall {
                apply: ExprId(2),
                callee: ExprId(0),
            }
        )));
    }

    fn handler_arm(resumptive: bool, body: u32) -> CatchArm {
        CatchArm {
            operation_path: Some(vec!["flip".into(), "coin".into()]),
            pat: Pat::Wild,
            continuation: resumptive.then_some(Pat::Wild),
            guard: None,
            body: ExprId(body),
        }
    }
}
