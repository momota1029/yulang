//! Static effect-shape profile for the lowered control IR.
//!
//! This is intentionally a coarse metrics pass.  It does not prove a nearest
//! handler or change execution; it only records how much effect-shaped syntax is
//! present before the runtime decides to use the generic control VM.

use std::collections::HashSet;

use crate::ir::{Expr, Program};

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
}

impl ControlEffectProfile {
    pub(super) fn from_program(program: &Program) -> Self {
        let mut builder = ControlEffectProfileBuilder::default();
        for expr in &program.exprs {
            builder.visit_expr(expr);
        }
        builder.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{CatchArm, Expr, ExprId, Pat, Program};

    #[test]
    fn profiles_effect_shapes_without_running_program() {
        let program = Program {
            roots: Vec::new(),
            instances: Vec::new(),
            exprs: vec![
                Expr::EffectOp {
                    path: vec!["flip".into(), "coin".into()],
                },
                Expr::EffectOp {
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
            Expr::EffectOp { path } => {
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

    fn finish(mut self) -> ControlEffectProfile {
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
        self.profile
    }
}
