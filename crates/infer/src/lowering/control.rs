//! `case` / `catch` の lowering と、catch handler coverage 判定。

use super::pattern::{PatternItem, pattern_path, pattern_payloads, single_pattern_item};
use super::*;

impl<'a> ExprLowerer<'a> {
    pub(super) fn lower_case(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let scrutinee_node =
            case_like_scrutinee_expr(node).ok_or(LoweringError::MissingCaseScrutinee)?;
        let scrutinee = self.lower_expr(&scrutinee_node)?;
        let value = self.fresh_type_var();
        let effect = self.fresh_type_var();
        self.subtype_var_to_var(scrutinee.effect, effect);

        let mut arms = Vec::new();
        for arm in case_arm_nodes(node) {
            let before_locals = self.locals.len();
            let lowered = self.lower_case_arm(&arm, scrutinee.value, value, effect);
            self.locals.truncate(before_locals);
            let (pat, body) = lowered?;
            arms.push((pat, body));
        }

        let expr = self.session.poly.add_expr(Expr::Case(scrutinee.expr, arms));
        Ok(Computation::new(
            expr,
            value,
            effect,
            Evaluation::Computation,
        ))
    }

    fn lower_case_arm(
        &mut self,
        arm: &Cst,
        scrutinee_value: TypeVar,
        result_value: TypeVar,
        result_effect: TypeVar,
    ) -> Result<(PatId, poly::expr::ExprId), LoweringError> {
        if arm
            .children()
            .any(|child| child.kind() == SyntaxKind::CaseGuard)
        {
            return Err(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::CaseGuard,
            });
        }
        let pattern = arm_pattern(arm).ok_or(LoweringError::MissingCaseArmPattern)?;
        let pattern_value = self.fresh_type_var();
        let pat = self.lower_match_pattern(&pattern, pattern_value)?;
        self.subtype_var_to_var(scrutinee_value, pattern_value);
        self.subtype_var_to_var(pattern_value, scrutinee_value);

        let body_node = arm_body_expr(arm).ok_or(LoweringError::MissingCaseArmBody)?;
        let body = self.lower_expr(&body_node)?;
        self.subtype_var_to_var(body.value, result_value);
        self.subtype_var_to_var(body.effect, result_effect);
        Ok((pat, body.expr))
    }

    pub(super) fn lower_catch(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let scrutinee_node =
            case_like_scrutinee_expr(node).ok_or(LoweringError::MissingCatchScrutinee)?;
        let scrutinee = self.lower_expr(&scrutinee_node)?;
        let value = self.fresh_type_var();
        let effect = self.fresh_type_var();
        let rest_effect = self.fresh_type_var();

        let mut arms = Vec::new();
        let mut handled = CatchHandledEffects::new();
        let mut saw_value_arm = false;
        let mut saw_effect_arm = false;
        for arm in catch_arm_nodes(node) {
            let before_locals = self.locals.len();
            let lowered = self.lower_catch_arm(
                &arm,
                scrutinee.value,
                scrutinee.effect,
                value,
                effect,
                &mut handled,
            );
            self.locals.truncate(before_locals);
            let lowered = lowered?;
            saw_value_arm |= matches!(lowered.kind, LoweredCatchArmKind::Value);
            saw_effect_arm |= matches!(lowered.kind, LoweredCatchArmKind::Effect);
            arms.push((lowered.pat, lowered.continuation, lowered.body));
        }

        if handled.is_empty() {
            self.subtype_var_to_var(scrutinee.effect, effect);
        } else {
            let tail = self.alloc_neg(Neg::Var(rest_effect));
            let row = self.alloc_neg(Neg::Row(handled.row_items(), tail));
            self.subtype(Pos::Var(scrutinee.effect), row);
            if handled.is_complete(self.modules, self.module, self.site) {
                self.subtype_var_to_var(rest_effect, effect);
            } else {
                self.subtype_var_to_var(scrutinee.effect, effect);
            }
        }
        if !saw_value_arm {
            self.subtype_var_to_var(scrutinee.value, value);
            self.subtype_var_to_var(value, scrutinee.value);
        }
        if !saw_value_arm && !saw_effect_arm {
            self.subtype_var_to_var(scrutinee.effect, effect);
        }

        let expr = self
            .session
            .poly
            .add_expr(Expr::Catch(scrutinee.expr, arms));
        Ok(Computation::new(
            expr,
            value,
            effect,
            Evaluation::Computation,
        ))
    }

    fn lower_catch_arm(
        &mut self,
        arm: &Cst,
        scrutinee_value: TypeVar,
        scrutinee_effect: TypeVar,
        result_value: TypeVar,
        result_effect: TypeVar,
        handled: &mut CatchHandledEffects,
    ) -> Result<LoweredCatchArm, LoweringError> {
        if arm
            .children()
            .any(|child| child.kind() == SyntaxKind::CatchGuard)
        {
            return Err(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::CatchGuard,
            });
        }
        let patterns = arm_patterns(arm);
        let body_node = arm_body_expr(arm).ok_or(LoweringError::MissingCatchArmBody)?;
        match patterns.as_slice() {
            [value_pattern] => {
                let pattern_value = self.fresh_type_var();
                let pat = self.lower_match_pattern(value_pattern, pattern_value)?;
                self.subtype_var_to_var(scrutinee_value, pattern_value);
                let body = self.lower_expr(&body_node)?;
                self.subtype_var_to_var(body.value, result_value);
                self.subtype_var_to_var(body.effect, result_effect);
                Ok(LoweredCatchArm {
                    kind: LoweredCatchArmKind::Value,
                    pat,
                    continuation: None,
                    body: body.expr,
                })
            }
            [effect_pattern, continuation_pattern] => {
                let effect_op = catch_effect_op(
                    pattern_path(effect_pattern).ok_or(LoweringError::MissingCatchArmPattern)?,
                );
                let row_item = self.alloc_neg(Neg::Con(
                    effect_op
                        .family_path
                        .iter()
                        .map(|name| name.0.clone())
                        .collect(),
                    Vec::new(),
                ));
                let (pat, payload_value) =
                    self.lower_catch_effect_payload_pattern(effect_pattern)?;
                handled.record(effect_op, pat_covers_all(&self.session.poly, pat), row_item);
                let continuation = self.lower_catch_continuation_pattern(
                    continuation_pattern,
                    payload_value,
                    scrutinee_value,
                    scrutinee_effect,
                )?;
                let body = self.lower_expr(&body_node)?;
                self.subtype_var_to_var(body.value, result_value);
                self.subtype_var_to_var(body.effect, result_effect);
                Ok(LoweredCatchArm {
                    kind: LoweredCatchArmKind::Effect,
                    pat,
                    continuation: Some(continuation),
                    body: body.expr,
                })
            }
            [] => Err(LoweringError::MissingCatchArmPattern),
            _ => Err(LoweringError::UnsupportedPatternSyntax { kind: arm.kind() }),
        }
    }

    fn lower_catch_effect_payload_pattern(
        &mut self,
        effect_pattern: &Cst,
    ) -> Result<(PatId, TypeVar), LoweringError> {
        let payloads = pattern_payloads(effect_pattern);
        match payloads.as_slice() {
            [] => {
                let value = self.fresh_type_var();
                Ok((self.session.poly.add_pat(Pat::Wild), value))
            }
            [payload] => {
                let value = self.fresh_type_var();
                Ok((self.lower_match_pattern(payload, value)?, value))
            }
            _ => {
                let value = self.fresh_type_var();
                let mut pats = Vec::with_capacity(payloads.len());
                let mut pos_items = Vec::with_capacity(payloads.len());
                let mut neg_items = Vec::with_capacity(payloads.len());
                for payload in payloads {
                    let item_value = self.fresh_type_var();
                    pats.push(self.lower_match_pattern(&payload, item_value)?);
                    pos_items.push(self.alloc_pos(Pos::Var(item_value)));
                    neg_items.push(self.alloc_neg(Neg::Var(item_value)));
                }
                self.constrain_lower(value, Pos::Tuple(pos_items));
                self.constrain_upper(value, Neg::Tuple(neg_items));
                Ok((self.session.poly.add_pat(Pat::Tuple(pats)), value))
            }
        }
    }

    fn lower_catch_continuation_pattern(
        &mut self,
        node: &Cst,
        payload_value: TypeVar,
        scrutinee_value: TypeVar,
        scrutinee_effect: TypeVar,
    ) -> Result<PatId, LoweringError> {
        match single_pattern_item(node)? {
            PatternItem::Ident(name) if name.0 == "_" => Ok(self.session.poly.add_pat(Pat::Wild)),
            PatternItem::Ident(name) => {
                let continuation_value = self.fresh_type_var();
                let pat = self.bind_pattern_local(
                    name,
                    continuation_value,
                    LocalCallReturnEffect::Annotated,
                );
                self.constrain_continuation_value(
                    continuation_value,
                    payload_value,
                    scrutinee_value,
                    scrutinee_effect,
                );
                Ok(pat)
            }
            PatternItem::Unsupported(kind) => Err(LoweringError::UnsupportedPatternSyntax { kind }),
            PatternItem::Number(_) | PatternItem::Paren(_) => {
                Err(LoweringError::UnsupportedPatternSyntax { kind: node.kind() })
            }
        }
    }

    fn constrain_continuation_value(
        &mut self,
        continuation_value: TypeVar,
        payload_value: TypeVar,
        scrutinee_value: TypeVar,
        scrutinee_effect: TypeVar,
    ) {
        let arg_eff = self.fresh_type_var();
        let lower_arg = self.alloc_neg(Neg::Var(payload_value));
        let lower_arg_eff = self.alloc_neg(Neg::Var(arg_eff));
        let lower_ret_eff = self.alloc_pos(Pos::Var(scrutinee_effect));
        let lower_ret = self.alloc_pos(Pos::Var(scrutinee_value));
        self.constrain_lower(
            continuation_value,
            Pos::Fun {
                arg: lower_arg,
                arg_eff: lower_arg_eff,
                ret_eff: lower_ret_eff,
                ret: lower_ret,
            },
        );

        let upper_arg = self.alloc_pos(Pos::Var(payload_value));
        let upper_arg_eff = self.alloc_pos(Pos::Var(arg_eff));
        let upper_ret_eff = self.alloc_neg(Neg::Var(scrutinee_effect));
        let upper_ret = self.alloc_neg(Neg::Var(scrutinee_value));
        self.constrain_upper(
            continuation_value,
            Neg::Fun {
                arg: upper_arg,
                arg_eff: upper_arg_eff,
                ret_eff: upper_ret_eff,
                ret: upper_ret,
            },
        );
    }
}

struct LoweredCatchArm {
    kind: LoweredCatchArmKind,
    pat: PatId,
    continuation: Option<PatId>,
    body: poly::expr::ExprId,
}

struct CatchHandledEffects {
    rows: Vec<(Vec<Name>, NegId)>,
    covered_ops: Vec<(Vec<Name>, Name)>,
}

impl CatchHandledEffects {
    fn new() -> Self {
        Self {
            rows: Vec::new(),
            covered_ops: Vec::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    fn row_items(&self) -> Vec<NegId> {
        self.rows.iter().map(|(_, item)| *item).collect()
    }

    fn record(&mut self, op: CatchEffectOp, payload_covers_all: bool, row_item: NegId) {
        if !self
            .rows
            .iter()
            .any(|(family_path, _)| family_path == &op.family_path)
        {
            self.rows.push((op.family_path.clone(), row_item));
        }
        let Some(operation) = op.operation else {
            return;
        };
        if payload_covers_all
            && !self
                .covered_ops
                .iter()
                .any(|(family_path, name)| family_path == &op.family_path && name == &operation)
        {
            self.covered_ops.push((op.family_path, operation));
        }
    }

    fn is_complete(&self, modules: &ModuleTable, module: ModuleId, site: ModuleOrder) -> bool {
        self.rows.iter().all(|(family_path, _)| {
            modules
                .act_operation_decls_at(module, family_path, site)
                .iter()
                .all(|op| self.covers_operation(family_path, &op.name))
        })
    }

    fn covers_operation(&self, family_path: &[Name], operation: &Name) -> bool {
        self.covered_ops
            .iter()
            .any(|(path, name)| path == family_path && name == operation)
    }
}

struct CatchEffectOp {
    family_path: Vec<Name>,
    operation: Option<Name>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LoweredCatchArmKind {
    Value,
    Effect,
}

fn case_like_scrutinee_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

fn case_arm_nodes(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::CaseBlock)
        .flat_map(|block| arm_nodes(&block, SyntaxKind::CaseArm))
        .collect()
}

fn catch_arm_nodes(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::CatchBlock)
        .flat_map(|block| arm_nodes(&block, SyntaxKind::CatchArm))
        .collect()
}

fn arm_nodes(block: &Cst, kind: SyntaxKind) -> Vec<Cst> {
    block
        .children()
        .filter(|child| child.kind() == kind)
        .collect()
}

fn arm_pattern(arm: &Cst) -> Option<Cst> {
    arm_patterns(arm).into_iter().next()
}

fn arm_patterns(arm: &Cst) -> Vec<Cst> {
    arm.children()
        .filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Pattern
                    | SyntaxKind::PatOr
                    | SyntaxKind::PatAs
                    | SyntaxKind::PatParenGroup
            )
        })
        .collect()
}

fn arm_body_expr(arm: &Cst) -> Option<Cst> {
    arm.children()
        .filter(|child| child.kind() == SyntaxKind::Expr)
        .last()
}

fn catch_effect_op(path: Vec<Name>) -> CatchEffectOp {
    let Some((operation, family_path)) = path.split_last() else {
        return CatchEffectOp {
            family_path: Vec::new(),
            operation: None,
        };
    };
    if family_path.is_empty() {
        return CatchEffectOp {
            family_path: vec![operation.clone()],
            operation: None,
        };
    }
    CatchEffectOp {
        family_path: family_path.to_vec(),
        operation: Some(operation.clone()),
    }
}

fn pat_covers_all(poly: &poly::expr::Arena, pat: PatId) -> bool {
    match poly.pat(pat) {
        Pat::Wild | Pat::Var(_) => true,
        Pat::Tuple(items) => items.iter().all(|item| pat_covers_all(poly, *item)),
        Pat::Or(lhs, rhs) => pat_covers_all(poly, *lhs) || pat_covers_all(poly, *rhs),
        Pat::As(inner, _) => pat_covers_all(poly, *inner),
        Pat::Lit(_)
        | Pat::List { .. }
        | Pat::Record { .. }
        | Pat::PolyVariant(_, _)
        | Pat::Con(_, _)
        | Pat::Ref(_) => false,
    }
}
