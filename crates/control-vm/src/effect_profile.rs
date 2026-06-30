//! Static effect-shape profile for the lowered control IR.
//!
//! This is intentionally a coarse metrics pass.  It does not prove a nearest
//! handler or change execution; it only records how much effect-shaped syntax is
//! present before the runtime decides to use the generic control VM.

use std::collections::HashSet;

use mono::FunctionAdapterHygiene;

use crate::ir::{
    Block, CatchArm, Expr, ExprId, InstanceId, Pat, Program, RecordSpread, Root, Stmt,
};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct ControlEffectProfile {
    pub(super) effect_ops: u64,
    pub(super) effect_op_families: u64,
    pub(super) effect_ops_with_handler_arm: u64,
    pub(super) effect_ops_without_handler_arm: u64,
    pub(super) marker_frames: u64,
    pub(super) marker_frame_families: u64,
    pub(super) catches: u64,
    pub(super) handler_arms: u64,
    pub(super) handler_arm_families: u64,
    pub(super) value_arms: u64,
    pub(super) continuation_arms: u64,
    pub(super) function_adapters: u64,
    pub(super) ref_sets: u64,
    pub(super) scoped_effect_op_visits: u64,
    pub(super) scoped_unique_effect_ops: u64,
    pub(super) scoped_unvisited_effect_ops: u64,
    pub(super) scoped_effect_ops_with_nearest_handler: u64,
    pub(super) scoped_effect_ops_without_nearest_handler: u64,
    pub(super) scoped_effect_ops_with_direct_handler_candidate: u64,
    pub(super) scoped_effect_ops_blocked_by_callback_boundary: u64,
    pub(super) scoped_effect_ops_blocked_by_delayed_boundary: u64,
    pub(super) scoped_effect_ops_with_resumptive_handler: u64,
    pub(super) scoped_effect_ops_with_abortive_handler: u64,
    pub(super) scoped_effect_call_sites: u64,
    pub(super) scoped_effect_call_sites_with_nearest_handler: u64,
    pub(super) scoped_effect_call_sites_without_nearest_handler: u64,
    pub(super) scoped_effect_call_sites_with_direct_handler_candidate: u64,
    pub(super) scoped_effect_call_sites_blocked_by_callback_boundary: u64,
    pub(super) scoped_effect_call_sites_blocked_by_delayed_boundary: u64,
    pub(super) scoped_effect_call_sites_with_resumptive_handler: u64,
    pub(super) scoped_effect_call_sites_with_abortive_handler: u64,
    pub(super) scoped_known_function_call_sites: u64,
    pub(super) scoped_known_instance_call_sites: u64,
    pub(super) scoped_dynamic_call_sites: u64,
    pub(super) scoped_dynamic_call_sites_under_handler: u64,
    pub(super) scoped_known_thunk_force_sites: u64,
    pub(super) scoped_dynamic_force_sites: u64,
    pub(super) scoped_dynamic_force_sites_under_handler: u64,
    pub(super) scoped_callback_boundaries: u64,
    pub(super) scoped_delayed_boundaries: u64,
    pub(super) scoped_max_handler_depth: u64,
    pub(super) scoped_missing_instance_refs: u64,
    pub(super) scoped_cycle_instance_refs: u64,
    pub(super) scoped_missing_expr_refs: u64,
    pub(super) scoped_cycle_expr_refs: u64,
}

impl ControlEffectProfile {
    pub(super) fn from_program(program: &Program) -> Self {
        let mut builder = ControlEffectProfileBuilder::default();
        for expr in &program.exprs {
            builder.visit_expr(expr);
        }
        let scoped = ScopedEffectProfileBuilder::new(program).finish();
        builder.finish(scoped)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{CatchArm, Expr, ExprId, Instance, InstanceId, Pat, Program, Root};

    #[test]
    fn profiles_effect_shapes_without_running_program() {
        let program = Program {
            roots: Vec::new(),
            instances: Vec::new(),
            exprs: vec![
                Expr::EffectOp {
                    def: None,
                    path: vec!["flip".into(), "coin".into()],
                },
                Expr::EffectOp {
                    def: None,
                    path: vec!["host".into(), "print".into()],
                },
                Expr::MarkerFrame {
                    path: vec!["flip".into()],
                    body: ExprId(0),
                },
                Expr::Catch {
                    body: ExprId(0),
                    arms: vec![
                        CatchArm {
                            operation_path: Some(vec!["flip".into(), "coin".into()]),
                            pat: Pat::Wild,
                            continuation: Some(Pat::Wild),
                            guard: None,
                            body: ExprId(0),
                        },
                        CatchArm {
                            operation_path: None,
                            pat: Pat::Wild,
                            continuation: None,
                            guard: None,
                            body: ExprId(0),
                        },
                    ],
                },
                Expr::RefSet {
                    reference: ExprId(0),
                    value: ExprId(1),
                },
            ],
        };

        let profile = ControlEffectProfile::from_program(&program);

        assert_eq!(profile.effect_ops, 2);
        assert_eq!(profile.effect_op_families, 2);
        assert_eq!(profile.effect_ops_with_handler_arm, 1);
        assert_eq!(profile.effect_ops_without_handler_arm, 1);
        assert_eq!(profile.marker_frames, 1);
        assert_eq!(profile.marker_frame_families, 1);
        assert_eq!(profile.catches, 1);
        assert_eq!(profile.handler_arms, 1);
        assert_eq!(profile.handler_arm_families, 1);
        assert_eq!(profile.value_arms, 1);
        assert_eq!(profile.continuation_arms, 1);
        assert_eq!(profile.ref_sets, 1);
        assert_eq!(profile.scoped_effect_op_visits, 0);
        assert_eq!(profile.scoped_unique_effect_ops, 0);
        assert_eq!(profile.scoped_unvisited_effect_ops, 2);
    }

    #[test]
    fn profiles_scoped_handler_candidates() {
        let program = Program {
            roots: vec![
                Root::Expr(ExprId(1)),
                Root::Expr(ExprId(4)),
                Root::Expr(ExprId(7)),
            ],
            instances: Vec::new(),
            exprs: vec![
                Expr::EffectOp {
                    def: None,
                    path: vec!["flip".into(), "coin".into()],
                },
                Expr::Catch {
                    body: ExprId(0),
                    arms: vec![handler_arm(false, 8)],
                },
                Expr::EffectOp {
                    def: None,
                    path: vec!["flip".into(), "coin".into()],
                },
                Expr::Lambda {
                    param: Pat::Wild,
                    body: ExprId(2),
                },
                Expr::Catch {
                    body: ExprId(3),
                    arms: vec![handler_arm(false, 8)],
                },
                Expr::EffectOp {
                    def: None,
                    path: vec!["flip".into(), "coin".into()],
                },
                Expr::FunctionAdapter {
                    source: mono::Type::unit(),
                    target: mono::Type::unit(),
                    function: ExprId(5),
                    hygiene: mono::FunctionAdapterHygiene {
                        markers: vec![mono::GuardMarker {
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
                    arms: vec![handler_arm(true, 8)],
                },
                Expr::Lit(mono::Lit::Unit),
            ],
        };

        let profile = ControlEffectProfile::from_program(&program);

        assert_eq!(profile.scoped_effect_op_visits, 3);
        assert_eq!(profile.scoped_unique_effect_ops, 3);
        assert_eq!(profile.scoped_unvisited_effect_ops, 0);
        assert_eq!(profile.scoped_effect_ops_with_nearest_handler, 3);
        assert_eq!(profile.scoped_effect_ops_without_nearest_handler, 0);
        assert_eq!(profile.scoped_effect_ops_with_direct_handler_candidate, 1);
        assert_eq!(profile.scoped_effect_ops_blocked_by_delayed_boundary, 1);
        assert_eq!(profile.scoped_effect_ops_blocked_by_callback_boundary, 1);
        assert_eq!(profile.scoped_effect_ops_with_abortive_handler, 2);
        assert_eq!(profile.scoped_effect_ops_with_resumptive_handler, 1);
        assert_eq!(profile.scoped_effect_call_sites, 0);
        assert_eq!(profile.scoped_callback_boundaries, 1);
        assert_eq!(profile.scoped_delayed_boundaries, 1);
        assert_eq!(profile.scoped_max_handler_depth, 1);
    }

    #[test]
    fn profiles_known_effect_call_sites_under_scoped_handler() {
        let program = Program {
            roots: vec![Root::Expr(ExprId(4))],
            instances: vec![Instance {
                id: InstanceId(0),
                source: mono::InstanceSource::Def(mono::DefId(0)),
                signature: mono::Signature {
                    ty: mono::Type::unit(),
                },
                entry: ExprId(0),
            }],
            exprs: vec![
                Expr::EffectOp {
                    def: None,
                    path: vec!["flip".into(), "coin".into()],
                },
                Expr::InstanceRef(InstanceId(0)),
                Expr::Lit(mono::Lit::Unit),
                Expr::Apply {
                    callee: ExprId(1),
                    arg: ExprId(2),
                },
                Expr::Catch {
                    body: ExprId(3),
                    arms: vec![handler_arm(true, 5)],
                },
                Expr::Lit(mono::Lit::Unit),
            ],
        };

        let profile = ControlEffectProfile::from_program(&program);

        assert_eq!(profile.scoped_effect_call_sites, 1);
        assert_eq!(profile.scoped_effect_call_sites_with_nearest_handler, 1);
        assert_eq!(
            profile.scoped_effect_call_sites_with_direct_handler_candidate,
            1
        );
        assert_eq!(profile.scoped_effect_call_sites_with_resumptive_handler, 1);
        assert_eq!(profile.scoped_known_instance_call_sites, 1);
        assert_eq!(profile.scoped_dynamic_call_sites, 0);
        assert_eq!(profile.scoped_dynamic_call_sites_under_handler, 0);
        assert_eq!(profile.scoped_missing_instance_refs, 0);
        assert_eq!(profile.scoped_cycle_instance_refs, 0);
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

#[derive(Default)]
struct ControlEffectProfileBuilder {
    profile: ControlEffectProfile,
    effect_op_paths: Vec<Vec<String>>,
    effect_op_families: HashSet<Vec<String>>,
    marker_frame_families: HashSet<Vec<String>>,
    handler_arm_families: HashSet<Vec<String>>,
}

impl ControlEffectProfileBuilder {
    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::EffectOp { path, .. } => {
                self.profile.effect_ops += 1;
                self.effect_op_paths.push(path.clone());
                self.effect_op_families.insert(path.clone());
            }
            Expr::MarkerFrame { path, .. } => {
                self.profile.marker_frames += 1;
                self.marker_frame_families.insert(path.clone());
            }
            Expr::Catch { arms, .. } => {
                self.profile.catches += 1;
                for arm in arms {
                    if let Some(path) = &arm.operation_path {
                        self.profile.handler_arms += 1;
                        self.handler_arm_families.insert(path.clone());
                    } else {
                        self.profile.value_arms += 1;
                    }
                    if arm.continuation.is_some() {
                        self.profile.continuation_arms += 1;
                    }
                }
            }
            Expr::FunctionAdapter { .. } => {
                self.profile.function_adapters += 1;
            }
            Expr::RefSet { .. } => {
                self.profile.ref_sets += 1;
            }
            Expr::Lit(_)
            | Expr::PrimitiveOp { .. }
            | Expr::Constructor { .. }
            | Expr::Local(_)
            | Expr::InstanceRef(_)
            | Expr::Coerce { .. }
            | Expr::MakeThunk { .. }
            | Expr::ForceThunk { .. }
            | Expr::Apply { .. }
            | Expr::Lambda { .. }
            | Expr::Tuple(_)
            | Expr::Record { .. }
            | Expr::PolyVariant { .. }
            | Expr::Select { .. }
            | Expr::Case { .. }
            | Expr::Block(_) => {}
        }
    }

    fn finish(mut self, scoped: ScopedEffectProfile) -> ControlEffectProfile {
        for path in &self.effect_op_paths {
            if self.handler_arm_families.contains(path) {
                self.profile.effect_ops_with_handler_arm += 1;
            } else {
                self.profile.effect_ops_without_handler_arm += 1;
            }
        }
        self.profile.effect_op_families = self.effect_op_families.len() as u64;
        self.profile.marker_frame_families = self.marker_frame_families.len() as u64;
        self.profile.handler_arm_families = self.handler_arm_families.len() as u64;
        self.profile.scoped_effect_op_visits = scoped.effect_op_visits;
        self.profile.scoped_unique_effect_ops = scoped.unique_effect_ops;
        self.profile.scoped_unvisited_effect_ops = self
            .profile
            .effect_ops
            .saturating_sub(self.profile.scoped_unique_effect_ops);
        self.profile.scoped_effect_ops_with_nearest_handler =
            scoped.effect_ops_with_nearest_handler;
        self.profile.scoped_effect_ops_without_nearest_handler =
            scoped.effect_ops_without_nearest_handler;
        self.profile.scoped_effect_ops_with_direct_handler_candidate =
            scoped.effect_ops_with_direct_handler_candidate;
        self.profile.scoped_effect_ops_blocked_by_callback_boundary =
            scoped.effect_ops_blocked_by_callback_boundary;
        self.profile.scoped_effect_ops_blocked_by_delayed_boundary =
            scoped.effect_ops_blocked_by_delayed_boundary;
        self.profile.scoped_effect_ops_with_resumptive_handler =
            scoped.effect_ops_with_resumptive_handler;
        self.profile.scoped_effect_ops_with_abortive_handler =
            scoped.effect_ops_with_abortive_handler;
        self.profile.scoped_effect_call_sites = scoped.effect_call_sites;
        self.profile.scoped_effect_call_sites_with_nearest_handler =
            scoped.effect_call_sites_with_nearest_handler;
        self.profile
            .scoped_effect_call_sites_without_nearest_handler =
            scoped.effect_call_sites_without_nearest_handler;
        self.profile
            .scoped_effect_call_sites_with_direct_handler_candidate =
            scoped.effect_call_sites_with_direct_handler_candidate;
        self.profile
            .scoped_effect_call_sites_blocked_by_callback_boundary =
            scoped.effect_call_sites_blocked_by_callback_boundary;
        self.profile
            .scoped_effect_call_sites_blocked_by_delayed_boundary =
            scoped.effect_call_sites_blocked_by_delayed_boundary;
        self.profile
            .scoped_effect_call_sites_with_resumptive_handler =
            scoped.effect_call_sites_with_resumptive_handler;
        self.profile.scoped_effect_call_sites_with_abortive_handler =
            scoped.effect_call_sites_with_abortive_handler;
        self.profile.scoped_known_function_call_sites = scoped.known_function_call_sites;
        self.profile.scoped_known_instance_call_sites = scoped.known_instance_call_sites;
        self.profile.scoped_dynamic_call_sites = scoped.dynamic_call_sites;
        self.profile.scoped_dynamic_call_sites_under_handler =
            scoped.dynamic_call_sites_under_handler;
        self.profile.scoped_known_thunk_force_sites = scoped.known_thunk_force_sites;
        self.profile.scoped_dynamic_force_sites = scoped.dynamic_force_sites;
        self.profile.scoped_dynamic_force_sites_under_handler =
            scoped.dynamic_force_sites_under_handler;
        self.profile.scoped_callback_boundaries = scoped.callback_boundaries;
        self.profile.scoped_delayed_boundaries = scoped.delayed_boundaries;
        self.profile.scoped_max_handler_depth = scoped.max_handler_depth;
        self.profile.scoped_missing_instance_refs = scoped.missing_instance_refs;
        self.profile.scoped_cycle_instance_refs = scoped.cycle_instance_refs;
        self.profile.scoped_missing_expr_refs = scoped.missing_expr_refs;
        self.profile.scoped_cycle_expr_refs = scoped.cycle_expr_refs;
        self.profile
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct ScopedEffectProfile {
    effect_op_visits: u64,
    unique_effect_ops: u64,
    effect_ops_with_nearest_handler: u64,
    effect_ops_without_nearest_handler: u64,
    effect_ops_with_direct_handler_candidate: u64,
    effect_ops_blocked_by_callback_boundary: u64,
    effect_ops_blocked_by_delayed_boundary: u64,
    effect_ops_with_resumptive_handler: u64,
    effect_ops_with_abortive_handler: u64,
    effect_call_sites: u64,
    effect_call_sites_with_nearest_handler: u64,
    effect_call_sites_without_nearest_handler: u64,
    effect_call_sites_with_direct_handler_candidate: u64,
    effect_call_sites_blocked_by_callback_boundary: u64,
    effect_call_sites_blocked_by_delayed_boundary: u64,
    effect_call_sites_with_resumptive_handler: u64,
    effect_call_sites_with_abortive_handler: u64,
    known_function_call_sites: u64,
    known_instance_call_sites: u64,
    dynamic_call_sites: u64,
    dynamic_call_sites_under_handler: u64,
    known_thunk_force_sites: u64,
    dynamic_force_sites: u64,
    dynamic_force_sites_under_handler: u64,
    callback_boundaries: u64,
    delayed_boundaries: u64,
    max_handler_depth: u64,
    missing_instance_refs: u64,
    cycle_instance_refs: u64,
    missing_expr_refs: u64,
    cycle_expr_refs: u64,
}

struct ScopedEffectProfileBuilder<'a> {
    program: &'a Program,
    profile: ScopedEffectProfile,
    visited_effect_ops: HashSet<ExprId>,
    active_exprs: HashSet<ExprId>,
    active_instances: HashSet<InstanceId>,
}

impl<'a> ScopedEffectProfileBuilder<'a> {
    fn new(program: &'a Program) -> Self {
        Self {
            program,
            profile: ScopedEffectProfile::default(),
            visited_effect_ops: HashSet::new(),
            active_exprs: HashSet::new(),
            active_instances: HashSet::new(),
        }
    }

    fn finish(mut self) -> ScopedEffectProfile {
        let mut context = ScopedContext::default();
        for root in &self.program.roots {
            match root {
                Root::Instance(instance) | Root::EvalInstance(instance) => {
                    self.visit_instance_entry(*instance, &mut context);
                }
                Root::Expr(expr) => self.visit_expr_id(*expr, &mut context),
            }
        }
        self.profile.unique_effect_ops = self.visited_effect_ops.len() as u64;
        self.profile
    }

    fn visit_expr_id(&mut self, id: ExprId, context: &mut ScopedContext) {
        let Some(expr) = self.program.exprs.get(id.0 as usize) else {
            self.profile.missing_expr_refs += 1;
            return;
        };
        if !self.active_exprs.insert(id) {
            self.profile.cycle_expr_refs += 1;
            return;
        }
        self.visit_expr(id, expr, context);
        self.active_exprs.remove(&id);
    }

    fn visit_expr(&mut self, id: ExprId, expr: &Expr, context: &mut ScopedContext) {
        match expr {
            Expr::EffectOp { path, .. } => self.record_effect_op(id, path, context),
            Expr::Coerce { expr, .. } => self.visit_expr_id(*expr, context),
            Expr::MakeThunk { body, .. } => self.visit_delayed_boundary(*body, context),
            Expr::ForceThunk { thunk, .. } => {
                self.visit_expr_id(*thunk, context);
                if !self.visit_known_force_site(*thunk, context) {
                    self.profile.dynamic_force_sites += 1;
                    if context.has_handler() {
                        self.profile.dynamic_force_sites_under_handler += 1;
                    }
                }
            }
            Expr::FunctionAdapter {
                function, hygiene, ..
            } => self.visit_function_adapter(*function, hygiene, context),
            Expr::MarkerFrame { body, .. } => self.visit_expr_id(*body, context),
            Expr::Apply { callee, arg } => {
                self.visit_expr_id(*callee, context);
                self.visit_expr_id(*arg, context);
                if !self.visit_known_call_site(*callee, context) {
                    self.profile.dynamic_call_sites += 1;
                    if context.has_handler() {
                        self.profile.dynamic_call_sites_under_handler += 1;
                    }
                }
            }
            Expr::RefSet { reference, value } => {
                self.visit_expr_id(*reference, context);
                self.visit_expr_id(*value, context);
            }
            Expr::Lambda { param, body } => {
                self.visit_pat(param, context);
                self.visit_delayed_boundary(*body, context);
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
            Expr::Catch { body, arms } => self.visit_catch(*body, arms, context),
            Expr::Block(block) => self.visit_block(block, context),
            Expr::InstanceRef(instance) => self.visit_instance_entry(*instance, context),
            Expr::Lit(_) | Expr::PrimitiveOp { .. } | Expr::Constructor { .. } | Expr::Local(_) => {
            }
        }
    }

    fn visit_expr_ids(&mut self, ids: &[ExprId], context: &mut ScopedContext) {
        for id in ids {
            self.visit_expr_id(*id, context);
        }
    }

    fn visit_expr_spread(&mut self, spread: &RecordSpread<ExprId>, context: &mut ScopedContext) {
        match spread {
            RecordSpread::None => {}
            RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                self.visit_expr_id(*expr, context)
            }
        }
    }

    fn visit_catch(&mut self, body: ExprId, arms: &[CatchArm], context: &mut ScopedContext) {
        let frame = HandlerFrame::from_arms(
            arms,
            context.callback_boundary_depth,
            context.delayed_boundary_depth,
        );
        if let Some(frame) = frame {
            context.handlers.push(frame);
            self.profile.max_handler_depth = self
                .profile
                .max_handler_depth
                .max(context.handlers.len() as u64);
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
        function: ExprId,
        hygiene: &FunctionAdapterHygiene,
        context: &mut ScopedContext,
    ) {
        if hygiene_has_boundary_markers(hygiene) {
            self.profile.callback_boundaries += 1;
            context.callback_boundary_depth += 1;
            self.visit_expr_id(function, context);
            context.callback_boundary_depth -= 1;
        } else {
            self.visit_expr_id(function, context);
        }
    }

    fn visit_delayed_boundary(&mut self, body: ExprId, context: &mut ScopedContext) {
        self.profile.delayed_boundaries += 1;
        context.delayed_boundary_depth += 1;
        self.visit_expr_id(body, context);
        context.delayed_boundary_depth -= 1;
    }

    fn visit_known_call_site(&mut self, callee: ExprId, context: &mut ScopedContext) -> bool {
        let Some(expr) = self.program.exprs.get(callee.0 as usize) else {
            self.profile.missing_expr_refs += 1;
            return false;
        };
        match expr {
            Expr::EffectOp { path, .. } => {
                self.record_effect_call_site(path, context);
                true
            }
            Expr::Lambda { param, body } => {
                self.profile.known_function_call_sites += 1;
                self.visit_pat(param, context);
                self.visit_expr_id(*body, context);
                true
            }
            Expr::InstanceRef(instance) => self.visit_known_instance_call_site(*instance, context),
            Expr::PrimitiveOp { .. } | Expr::Constructor { .. } => true,
            _ => false,
        }
    }

    fn visit_known_instance_call_site(
        &mut self,
        instance: InstanceId,
        context: &mut ScopedContext,
    ) -> bool {
        let Some(entry) = self.instance_entry(instance) else {
            self.profile.missing_instance_refs += 1;
            return false;
        };
        if !self.active_instances.insert(instance) {
            self.profile.cycle_instance_refs += 1;
            return false;
        }
        self.profile.known_instance_call_sites += 1;
        let known = self.visit_known_callee_entry(entry, context);
        self.active_instances.remove(&instance);
        known
    }

    fn visit_known_callee_entry(&mut self, entry: ExprId, context: &mut ScopedContext) -> bool {
        let Some(expr) = self.program.exprs.get(entry.0 as usize) else {
            self.profile.missing_expr_refs += 1;
            return false;
        };
        match expr {
            Expr::EffectOp { path, .. } => {
                self.record_effect_call_site(path, context);
                true
            }
            Expr::Lambda { param, body } => {
                self.profile.known_function_call_sites += 1;
                self.visit_pat(param, context);
                self.visit_expr_id(*body, context);
                true
            }
            Expr::PrimitiveOp { .. } | Expr::Constructor { .. } => true,
            _ => false,
        }
    }

    fn visit_known_force_site(&mut self, thunk: ExprId, context: &mut ScopedContext) -> bool {
        let Some(expr) = self.program.exprs.get(thunk.0 as usize) else {
            self.profile.missing_expr_refs += 1;
            return false;
        };
        match expr {
            Expr::MakeThunk { body, .. } => {
                self.profile.known_thunk_force_sites += 1;
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
        context: &mut ScopedContext,
    ) -> bool {
        let Some(entry) = self.instance_entry(instance) else {
            self.profile.missing_instance_refs += 1;
            return false;
        };
        if !self.active_instances.insert(instance) {
            self.profile.cycle_instance_refs += 1;
            return false;
        }
        let known = self.visit_known_force_entry(entry, context);
        self.active_instances.remove(&instance);
        known
    }

    fn visit_known_force_entry(&mut self, entry: ExprId, context: &mut ScopedContext) -> bool {
        let Some(expr) = self.program.exprs.get(entry.0 as usize) else {
            self.profile.missing_expr_refs += 1;
            return false;
        };
        match expr {
            Expr::MakeThunk { body, .. } => {
                self.profile.known_thunk_force_sites += 1;
                self.visit_expr_id(*body, context);
                true
            }
            _ => false,
        }
    }

    fn visit_instance_entry(&mut self, instance: InstanceId, context: &mut ScopedContext) {
        let Some(entry) = self.instance_entry(instance) else {
            self.profile.missing_instance_refs += 1;
            return;
        };
        if !self.active_instances.insert(instance) {
            self.profile.cycle_instance_refs += 1;
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

    fn visit_block(&mut self, block: &Block, context: &mut ScopedContext) {
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

    fn visit_stmts(&mut self, stmts: &[Stmt], context: &mut ScopedContext) {
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

    fn visit_pat(&mut self, pat: &Pat, context: &mut ScopedContext) {
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

    fn record_effect_op(&mut self, id: ExprId, path: &[String], context: &ScopedContext) {
        self.profile.effect_op_visits += 1;
        self.visited_effect_ops.insert(id);
        let classification = classify_handler_candidate(path, context);
        record_effect_op_classification(&mut self.profile, classification);
    }

    fn record_effect_call_site(&mut self, path: &[String], context: &ScopedContext) {
        self.profile.effect_call_sites += 1;
        let classification = classify_handler_candidate(path, context);
        record_effect_call_site_classification(&mut self.profile, classification);
    }
}

#[derive(Default)]
struct ScopedContext {
    handlers: Vec<HandlerFrame>,
    callback_boundary_depth: u32,
    delayed_boundary_depth: u32,
}

impl ScopedContext {
    fn has_handler(&self) -> bool {
        !self.handlers.is_empty()
    }

    fn nearest_handler(&self, path: &[String]) -> Option<HandlerMatch> {
        for frame in self.handlers.iter().rev() {
            if let Some(resumptive) = frame.resumptive_for(path) {
                return Some(HandlerMatch {
                    resumptive,
                    callback_boundary_depth_at_entry: frame.callback_boundary_depth_at_entry,
                    delayed_boundary_depth_at_entry: frame.delayed_boundary_depth_at_entry,
                });
            }
        }
        None
    }
}

fn classify_handler_candidate(
    path: &[String],
    context: &ScopedContext,
) -> HandlerCandidateClassification {
    let Some(handler) = context.nearest_handler(path) else {
        return HandlerCandidateClassification::NoHandler;
    };
    let crosses_callback =
        context.callback_boundary_depth > handler.callback_boundary_depth_at_entry;
    let crosses_delayed = context.delayed_boundary_depth > handler.delayed_boundary_depth_at_entry;
    HandlerCandidateClassification::Handled {
        resumptive: handler.resumptive,
        crosses_callback,
        crosses_delayed,
    }
}

fn record_effect_op_classification(
    profile: &mut ScopedEffectProfile,
    classification: HandlerCandidateClassification,
) {
    match classification {
        HandlerCandidateClassification::NoHandler => {
            profile.effect_ops_without_nearest_handler += 1;
        }
        HandlerCandidateClassification::Handled {
            resumptive,
            crosses_callback,
            crosses_delayed,
        } => {
            profile.effect_ops_with_nearest_handler += 1;
            if resumptive {
                profile.effect_ops_with_resumptive_handler += 1;
            } else {
                profile.effect_ops_with_abortive_handler += 1;
            }
            if crosses_callback {
                profile.effect_ops_blocked_by_callback_boundary += 1;
            }
            if crosses_delayed {
                profile.effect_ops_blocked_by_delayed_boundary += 1;
            }
            if !crosses_callback && !crosses_delayed {
                profile.effect_ops_with_direct_handler_candidate += 1;
            }
        }
    }
}

fn record_effect_call_site_classification(
    profile: &mut ScopedEffectProfile,
    classification: HandlerCandidateClassification,
) {
    match classification {
        HandlerCandidateClassification::NoHandler => {
            profile.effect_call_sites_without_nearest_handler += 1;
        }
        HandlerCandidateClassification::Handled {
            resumptive,
            crosses_callback,
            crosses_delayed,
        } => {
            profile.effect_call_sites_with_nearest_handler += 1;
            if resumptive {
                profile.effect_call_sites_with_resumptive_handler += 1;
            } else {
                profile.effect_call_sites_with_abortive_handler += 1;
            }
            if crosses_callback {
                profile.effect_call_sites_blocked_by_callback_boundary += 1;
            }
            if crosses_delayed {
                profile.effect_call_sites_blocked_by_delayed_boundary += 1;
            }
            if !crosses_callback && !crosses_delayed {
                profile.effect_call_sites_with_direct_handler_candidate += 1;
            }
        }
    }
}

struct HandlerFrame {
    arms: Vec<HandlerArmShape>,
    callback_boundary_depth_at_entry: u32,
    delayed_boundary_depth_at_entry: u32,
}

impl HandlerFrame {
    fn from_arms(
        arms: &[CatchArm],
        callback_boundary_depth_at_entry: u32,
        delayed_boundary_depth_at_entry: u32,
    ) -> Option<Self> {
        let arms = arms
            .iter()
            .filter_map(|arm| {
                arm.operation_path.as_ref().map(|path| HandlerArmShape {
                    path: path.clone(),
                    resumptive: arm.continuation.is_some(),
                })
            })
            .collect::<Vec<_>>();
        (!arms.is_empty()).then_some(Self {
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

struct HandlerArmShape {
    path: Vec<String>,
    resumptive: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct HandlerMatch {
    resumptive: bool,
    callback_boundary_depth_at_entry: u32,
    delayed_boundary_depth_at_entry: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HandlerCandidateClassification {
    NoHandler,
    Handled {
        resumptive: bool,
        crosses_callback: bool,
        crosses_delayed: bool,
    },
}

fn hygiene_has_boundary_markers(hygiene: &FunctionAdapterHygiene) -> bool {
    !hygiene.markers.is_empty()
        || !hygiene.arg_markers.is_empty()
        || !hygiene.ret_markers.is_empty()
}
