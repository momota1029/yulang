//! `case` / `catch` の lowering と、catch handler coverage 判定。

mod syntax;

use super::pattern::{PatternItem, pattern_path, pattern_payloads, single_pattern_item};
use super::rule_lit::{
    RuleCaseBranch, RuleCasePart, rule_expr_case_branches, rule_lit_case_branches,
};
use super::*;
use syntax::*;

impl<'a> ExprLowerer<'a> {
    pub(super) fn lower_if(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let arm_nodes = if_arm_nodes(node);
        let else_node = else_arm_node(node);
        let has_else = else_node.is_some();

        if arm_nodes.is_empty() {
            return match else_node {
                Some(else_node) => {
                    let body = if_arm_body_expr(&else_node).ok_or(LoweringError::MissingIfBody)?;
                    self.lower_if_arm_body(&body)
                }
                None => Ok(self.unit_expr()),
            };
        }

        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let mut arms = Vec::with_capacity(arm_nodes.len());
        for arm in arm_nodes {
            let condition_node =
                if_arm_condition_expr(&arm).ok_or(LoweringError::MissingIfCondition)?;
            let body_node = if_arm_body_expr(&arm).ok_or(LoweringError::MissingIfBody)?;
            let condition = self.lower_if_condition(&condition_node, result_effect)?;
            let mut body = self.lower_if_arm_body(&body_node)?;
            if !has_else {
                body = self.discard_if_branch_value(body);
            }
            self.subtype_var_to_var(body.value, result_value);
            self.subtype_var_to_var(body.effect, result_effect);
            arms.push(LoweredIfArm { condition, body });
        }

        let tail = match else_node {
            Some(else_node) => {
                let body_node = if_arm_body_expr(&else_node).ok_or(LoweringError::MissingIfBody)?;
                let body = self.lower_if_arm_body(&body_node)?;
                self.subtype_var_to_var(body.value, result_value);
                self.subtype_var_to_var(body.effect, result_effect);
                body
            }
            None => {
                let body = self.unit_expr();
                self.subtype_var_to_var(body.value, result_value);
                self.subtype_var_to_var(body.effect, result_effect);
                body
            }
        };

        Ok(self.build_nested_if_cases(arms, tail, result_value, result_effect))
    }

    fn lower_if_condition(
        &mut self,
        node: &Cst,
        result_effect: TypeVar,
    ) -> Result<Computation, LoweringError> {
        let before_locals = self.locals.len();
        let condition = self.lower_expr(node);
        self.locals.truncate(before_locals);
        let condition = condition?;
        let raw_condition_effect = condition.effect;
        let condition = self.apply_junction(condition)?;
        self.constrain_exact_primitive(condition.value, "bool");
        self.subtype_var_to_var(raw_condition_effect, result_effect);
        self.subtype_var_to_var(condition.effect, result_effect);
        Ok(condition)
    }

    fn lower_if_arm_body(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let before_locals = self.locals.len();
        let body = self.lower_expr(node);
        self.locals.truncate(before_locals);
        body
    }

    fn discard_if_branch_value(&mut self, body: Computation) -> Computation {
        let tail = self.unit_expr();
        self.prepend_block(
            LoweredLocalStmt {
                stmt: Stmt::Expr(body.expr),
                effect: body.effect,
            },
            tail,
        )
    }

    fn build_nested_if_cases(
        &mut self,
        arms: Vec<LoweredIfArm>,
        mut tail: Computation,
        result_value: TypeVar,
        result_effect: TypeVar,
    ) -> Computation {
        for arm in arms.into_iter().rev() {
            let true_pat = self.session.poly.add_pat(Pat::Lit(Lit::Bool(true)));
            let false_pat = self.session.poly.add_pat(Pat::Lit(Lit::Bool(false)));
            let expr = self.session.poly.add_expr(Expr::Case(
                arm.condition.expr,
                vec![
                    CaseArm {
                        pat: true_pat,
                        guard: None,
                        body: arm.body.expr,
                    },
                    CaseArm {
                        pat: false_pat,
                        guard: None,
                        body: tail.expr,
                    },
                ],
            ));
            tail = Computation::new(expr, result_value, result_effect, Evaluation::Computation);
        }
        tail
    }

    pub(super) fn lower_case(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let scrutinee_node =
            case_like_scrutinee_expr(node).ok_or(LoweringError::MissingCaseScrutinee)?;
        let scrutinee = self.lower_expr(&scrutinee_node)?;
        if let Some(label) = case_like_label(node) {
            return self.lower_recursive_case_like(
                node,
                label,
                Some(scrutinee),
                lambda_scope,
                RecursiveCaseLikeKind::Case,
            );
        }
        self.lower_case_with_scrutinee(node, scrutinee)
    }

    pub(super) fn lower_case_lambda(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        if let Some(label) = case_like_label(node) {
            return self.lower_recursive_case_like(
                node,
                label,
                None,
                lambda_scope,
                RecursiveCaseLikeKind::Case,
            );
        }

        self.lower_case_lambda_without_label(node, lambda_scope)
    }

    fn lower_case_lambda_without_label(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let scrutinee_name = Name("#case-scrutinee".to_string());
        let scrutinee_value = self.fresh_type_var();
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            scrutinee_name.clone(),
            scrutinee_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let scrutinee_local = self
            .locals
            .last()
            .cloned()
            .expect("case lambda scrutinee should be the last local");
        let scrutinee = self.lower_local_name(scrutinee_name, scrutinee_local, None);

        self.function_frames
            .push(FunctionPredicateFrame::new(lambda_scope));
        let previous_level = self.session.infer.enter_child_level();
        let body_result = self.lower_case_with_scrutinee(node, scrutinee);
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("case lambda predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(scrutinee_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts = self.lambda_predicate_subtracts(lambda_scope, Vec::new(), frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_case_with_scrutinee(
        &mut self,
        node: &Cst,
        scrutinee: Computation,
    ) -> Result<Computation, LoweringError> {
        let arm_nodes = case_arm_nodes(node);
        if arm_nodes
            .iter()
            .any(|arm| case_arm_rule_pattern(arm).is_some())
        {
            return self.lower_rule_case_with_scrutinee(scrutinee, &arm_nodes);
        }

        let value = self.fresh_type_var();
        let effect = self.fresh_type_var();
        self.subtype_var_to_var(scrutinee.effect, effect);

        let mut arms = Vec::new();
        for arm in arm_nodes {
            let before_locals = self.locals.len();
            let lowered = self.lower_case_arm(&arm, scrutinee.value, value, effect);
            self.locals.truncate(before_locals);
            arms.push(lowered?);
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
    ) -> Result<CaseArm, LoweringError> {
        let pattern = arm_pattern(arm).ok_or(LoweringError::MissingCaseArmPattern)?;
        let pattern_value = self.fresh_type_var();
        let var_bindings = self.prepare_var_pattern_bindings(&pattern)?;
        let pat =
            self.lower_match_pattern_with_var_bindings(&pattern, pattern_value, &var_bindings)?;
        self.subtype_var_to_var(scrutinee_value, pattern_value);
        self.subtype_var_to_var(pattern_value, scrutinee_value);

        let guard_node = arm_guard_expr(arm);
        if guard_node.is_some() && !var_bindings.is_empty() {
            return Err(LoweringError::UnsupportedPatternSyntax { kind: arm.kind() });
        }
        let guard = guard_node
            .map(|guard| self.lower_arm_guard(&guard, result_effect))
            .transpose()?;
        let active_var_bindings = self.install_var_pattern_bindings(&var_bindings)?;
        let body_node = arm_body_expr(arm).ok_or(LoweringError::MissingCaseArmBody)?;
        let mut body = self.lower_expr(&body_node)?;
        body = self.wrap_var_pattern_bindings(active_var_bindings, body)?;
        self.subtype_var_to_var(body.value, result_value);
        self.subtype_var_to_var(body.effect, result_effect);
        Ok(CaseArm {
            pat,
            guard,
            body: body.expr,
        })
    }

    fn lower_rule_case_with_scrutinee(
        &mut self,
        scrutinee: Computation,
        arm_nodes: &[Cst],
    ) -> Result<Computation, LoweringError> {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let input_value = self.fresh_type_var();
        self.subtype_var_to_var(scrutinee.value, input_value);
        self.subtype_var_to_var(input_value, scrutinee.value);
        self.constrain_lower(
            input_value,
            Pos::Con(crate::std_paths::text_str_type(), Vec::new()),
        );
        self.constrain_upper(
            input_value,
            Neg::Con(crate::std_paths::text_str_type(), Vec::new()),
        );

        let before_locals = self.locals.len();
        let input_name = Name("#case-rule-input".to_string());
        let (input_pat, _) = self.bind_let_local_with_def(
            input_name.clone(),
            input_value,
            LocalCallReturnEffect::Annotated,
            Some(scrutinee.expr),
        );
        let input_local = self
            .locals
            .last()
            .cloned()
            .expect("rule case scrutinee should be the last local");
        let input = self.lower_local_name(input_name, input_local, None);
        let body = self.lower_case_arm_chain(arm_nodes, input, result_value, result_effect);
        self.locals.truncate(before_locals);
        let body = body?;

        self.subtype_var_to_var(scrutinee.effect, result_effect);
        let expr = self.session.poly.add_expr(Expr::Block(
            vec![Stmt::Let(Vis::My, input_pat, scrutinee.expr)],
            Some(body.expr),
        ));
        Ok(Computation::computation(expr, result_value, result_effect))
    }

    fn lower_case_arm_chain(
        &mut self,
        arm_nodes: &[Cst],
        input: Computation,
        result_value: TypeVar,
        result_effect: TypeVar,
    ) -> Result<Computation, LoweringError> {
        let Some((arm, rest)) = arm_nodes.split_first() else {
            return Ok(self.no_matching_case(input, result_value, result_effect));
        };

        if let Some(rule) = case_arm_rule_pattern(arm) {
            return self.lower_rule_case_arm(arm, &rule, rest, input, result_value, result_effect);
        }

        let before_locals = self.locals.len();
        let case_arm = self.lower_case_arm(arm, input.value, result_value, result_effect)?;
        self.locals.truncate(before_locals);

        let mut arms = vec![case_arm];
        if !rest.is_empty() {
            let fallback = self.lower_case_arm_chain(rest, input, result_value, result_effect)?;
            arms.push(CaseArm {
                pat: self.session.poly.add_pat(Pat::Wild),
                guard: None,
                body: fallback.expr,
            });
        }
        let expr = self.session.poly.add_expr(Expr::Case(input.expr, arms));
        Ok(Computation::computation(expr, result_value, result_effect))
    }

    fn lower_rule_case_arm(
        &mut self,
        arm: &Cst,
        rule: &Cst,
        rest: &[Cst],
        input: Computation,
        result_value: TypeVar,
        result_effect: TypeVar,
    ) -> Result<Computation, LoweringError> {
        let branches = rule_case_branches(rule)?;
        let rule_locals_start = self.locals.len();
        let fallback = self.lower_case_arm_chain(rest, input, result_value, result_effect)?;
        let start = self.int_value(0);
        let result = self.lower_rule_case_branch_chain(
            &branches,
            input,
            start,
            fallback,
            arm,
            result_value,
            result_effect,
            rule_locals_start,
        );
        self.locals.truncate(rule_locals_start);
        result
    }

    fn lower_rule_case_branch_chain(
        &mut self,
        branches: &[RuleCaseBranch],
        input: Computation,
        pos: Computation,
        fallback: Computation,
        arm: &Cst,
        result_value: TypeVar,
        result_effect: TypeVar,
        rule_locals_start: usize,
    ) -> Result<Computation, LoweringError> {
        let Some((branch, rest)) = branches.split_first() else {
            return Ok(fallback);
        };

        let next = self.lower_rule_case_branch_chain(
            rest,
            input,
            pos,
            fallback,
            arm,
            result_value,
            result_effect,
            rule_locals_start,
        )?;
        self.locals.truncate(rule_locals_start);

        let result = self.lower_rule_case_part_chain(
            &branch.parts,
            input,
            pos,
            next,
            arm,
            result_value,
            result_effect,
            rule_locals_start,
        );
        self.locals.truncate(rule_locals_start);
        result
    }

    fn lower_rule_case_part_chain(
        &mut self,
        parts: &[RuleCasePart],
        input: Computation,
        pos: Computation,
        fallback: Computation,
        arm: &Cst,
        result_value: TypeVar,
        result_effect: TypeVar,
        rule_locals_start: usize,
    ) -> Result<Computation, LoweringError> {
        let Some((part, rest)) = parts.split_first() else {
            return self.lower_rule_case_complete(
                input,
                pos,
                fallback,
                arm,
                result_value,
                result_effect,
                rule_locals_start,
            );
        };

        match part {
            RuleCasePart::Token(text) if text.is_empty() => self.lower_rule_case_part_chain(
                rest,
                input,
                pos,
                fallback,
                arm,
                result_value,
                result_effect,
                rule_locals_start,
            ),
            RuleCasePart::Token(text) => {
                let (condition, next_pos) =
                    self.lower_rule_case_token_condition(input, pos, text.clone())?;
                let body = self.lower_rule_case_part_chain(
                    rest,
                    input,
                    next_pos,
                    fallback,
                    arm,
                    result_value,
                    result_effect,
                    rule_locals_start,
                )?;
                Ok(self.lower_bool_case(condition, body, fallback, result_value, result_effect))
            }
            RuleCasePart::CaptureWord(name) => self.lower_rule_case_word_capture(
                name.clone(),
                rest,
                input,
                pos,
                fallback,
                arm,
                result_value,
                result_effect,
                rule_locals_start,
            ),
        }
    }

    fn lower_rule_case_token_condition(
        &mut self,
        input: Computation,
        pos: Computation,
        text: String,
    ) -> Result<(Computation, Computation), LoweringError> {
        let token = self.string_value(text);
        let token_len = self.str_len(token)?;
        let next_pos = self.int_add(pos, token_len)?;
        let input_len = self.str_len(input)?;
        let in_bounds = self.int_le(next_pos, input_len)?;
        let slice = self.str_index_range_raw(input, pos, next_pos)?;
        let eq = self.str_eq(slice, token)?;
        let condition = self.bool_and(in_bounds, eq);
        Ok((condition, next_pos))
    }

    fn lower_rule_case_word_capture(
        &mut self,
        name: Name,
        rest: &[RuleCasePart],
        input: Computation,
        pos: Computation,
        fallback: Computation,
        arm: &Cst,
        result_value: TypeVar,
        result_effect: TypeVar,
        rule_locals_start: usize,
    ) -> Result<Computation, LoweringError> {
        let captured = self.word_prefix_at(input, pos)?;
        let pat = self.bind_pattern_local(
            name.clone(),
            captured.value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let local = self
            .locals
            .last()
            .cloned()
            .expect("rule capture should be the last local");
        let captured_local = self.lower_local_name(name, local, None);
        let captured_len = self.str_len(captured_local)?;
        let zero = self.int_value(0);
        let nonempty = self.int_lt(zero, captured_len)?;
        let next_pos = self.int_add(pos, captured_len)?;
        let body = self.lower_rule_case_part_chain(
            rest,
            input,
            next_pos,
            fallback,
            arm,
            result_value,
            result_effect,
            rule_locals_start,
        )?;
        let body = self.lower_bool_case(nonempty, body, fallback, result_value, result_effect);
        Ok(self.prepend_block(
            LoweredLocalStmt {
                stmt: Stmt::Let(Vis::My, pat, captured.expr),
                effect: captured.effect,
            },
            body,
        ))
    }

    fn lower_rule_case_complete(
        &mut self,
        input: Computation,
        pos: Computation,
        fallback: Computation,
        arm: &Cst,
        result_value: TypeVar,
        result_effect: TypeVar,
        rule_locals_start: usize,
    ) -> Result<Computation, LoweringError> {
        let input_len = self.str_len(input)?;
        let complete = self.int_eq(pos, input_len)?;
        let body = self.lower_rule_case_success_body(
            arm,
            fallback,
            result_value,
            result_effect,
            rule_locals_start,
        )?;
        Ok(self.lower_bool_case(complete, body, fallback, result_value, result_effect))
    }

    fn lower_rule_case_success_body(
        &mut self,
        arm: &Cst,
        fallback: Computation,
        result_value: TypeVar,
        result_effect: TypeVar,
        _rule_locals_start: usize,
    ) -> Result<Computation, LoweringError> {
        let body_node = arm_body_expr(arm).ok_or(LoweringError::MissingCaseArmBody)?;
        let body = self.lower_expr(&body_node)?;
        self.subtype_var_to_var(body.value, result_value);
        self.subtype_var_to_var(body.effect, result_effect);

        let Some(guard_node) = arm_guard_expr(arm) else {
            return Ok(body);
        };
        let condition = self.lower_if_condition(&guard_node, result_effect)?;
        Ok(self.lower_bool_case(condition, body, fallback, result_value, result_effect))
    }

    fn lower_bool_case(
        &mut self,
        condition: Computation,
        body: Computation,
        fallback: Computation,
        result_value: TypeVar,
        result_effect: TypeVar,
    ) -> Computation {
        self.constrain_exact_primitive(condition.value, "bool");
        self.subtype_var_to_var(condition.effect, result_effect);
        self.subtype_var_to_var(body.value, result_value);
        self.subtype_var_to_var(body.effect, result_effect);
        self.subtype_var_to_var(fallback.value, result_value);
        self.subtype_var_to_var(fallback.effect, result_effect);
        self.build_nested_if_cases(
            vec![LoweredIfArm { condition, body }],
            fallback,
            result_value,
            result_effect,
        )
    }

    fn bool_and(&mut self, left: Computation, right: Computation) -> Computation {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        self.constrain_exact_primitive(result_value, "bool");
        let fallback = self.lower_bool(false);
        self.lower_bool_case(left, right, fallback, result_value, result_effect)
    }

    fn str_len(&mut self, value: Computation) -> Result<Computation, LoweringError> {
        self.std_call1(crate::std_paths::text_str_value("len"), value)
    }

    fn str_eq(&mut self, lhs: Computation, rhs: Computation) -> Result<Computation, LoweringError> {
        self.std_call2(crate::std_paths::text_str_value("eq"), lhs, rhs)
    }

    fn str_index_range_raw(
        &mut self,
        input: Computation,
        start: Computation,
        end: Computation,
    ) -> Result<Computation, LoweringError> {
        self.std_call3(
            crate::std_paths::text_str_value("index_range_raw"),
            input,
            start,
            end,
        )
    }

    fn word_prefix_at(
        &mut self,
        input: Computation,
        start: Computation,
    ) -> Result<Computation, LoweringError> {
        self.std_call2(
            crate::std_paths::text_str_value("word_prefix_at"),
            input,
            start,
        )
    }

    fn int_add(
        &mut self,
        lhs: Computation,
        rhs: Computation,
    ) -> Result<Computation, LoweringError> {
        self.std_call2(crate::std_paths::int_value("add"), lhs, rhs)
    }

    fn int_eq(&mut self, lhs: Computation, rhs: Computation) -> Result<Computation, LoweringError> {
        self.std_call2(crate::std_paths::int_value("eq"), lhs, rhs)
    }

    fn int_lt(&mut self, lhs: Computation, rhs: Computation) -> Result<Computation, LoweringError> {
        self.std_call2(crate::std_paths::int_value("lt"), lhs, rhs)
    }

    fn int_le(&mut self, lhs: Computation, rhs: Computation) -> Result<Computation, LoweringError> {
        self.std_call2(crate::std_paths::int_value("le"), lhs, rhs)
    }

    fn std_call1(
        &mut self,
        path: Vec<String>,
        arg: Computation,
    ) -> Result<Computation, LoweringError> {
        let callee = self.lower_std_value_ref(path)?;
        Ok(self.make_app(callee, arg))
    }

    fn std_call2(
        &mut self,
        path: Vec<String>,
        first: Computation,
        second: Computation,
    ) -> Result<Computation, LoweringError> {
        let call = self.std_call1(path, first)?;
        Ok(self.make_app(call, second))
    }

    fn std_call3(
        &mut self,
        path: Vec<String>,
        first: Computation,
        second: Computation,
        third: Computation,
    ) -> Result<Computation, LoweringError> {
        let call = self.std_call2(path, first, second)?;
        Ok(self.make_app(call, third))
    }

    fn no_matching_case(
        &mut self,
        input: Computation,
        result_value: TypeVar,
        result_effect: TypeVar,
    ) -> Computation {
        self.subtype_var_to_var(input.effect, result_effect);
        let expr = self
            .session
            .poly
            .add_expr(Expr::Case(input.expr, Vec::new()));
        Computation::computation(expr, result_value, result_effect)
    }

    pub(super) fn lower_catch(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let scrutinee_node =
            case_like_scrutinee_expr(node).ok_or(LoweringError::MissingCatchScrutinee)?;
        let scrutinee = self.lower_expr(&scrutinee_node)?;
        if let Some(label) = case_like_label(node) {
            return self.lower_recursive_case_like(
                node,
                label,
                Some(scrutinee),
                lambda_scope,
                RecursiveCaseLikeKind::Catch,
            );
        }
        self.lower_catch_with_scrutinee(node, scrutinee)
    }

    pub(super) fn lower_catch_lambda(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        if let Some(label) = case_like_label(node) {
            return self.lower_recursive_case_like(
                node,
                label,
                None,
                lambda_scope,
                RecursiveCaseLikeKind::Catch,
            );
        }

        self.lower_catch_lambda_without_label(node, lambda_scope)
    }

    fn lower_catch_lambda_without_label(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let scrutinee_name = Name("#catch-scrutinee".to_string());
        let scrutinee_value = self.fresh_type_var();
        let scrutinee_effect = self.fresh_type_var();
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            scrutinee_name.clone(),
            scrutinee_value,
            Some(LocalEffect::Var(scrutinee_effect)),
            LocalCallReturnEffect::Annotated,
        );
        let scrutinee_local = self
            .locals
            .last()
            .cloned()
            .expect("catch lambda scrutinee should be the last local");
        let scrutinee = self.lower_local_name(scrutinee_name, scrutinee_local, None);

        self.function_frames
            .push(FunctionPredicateFrame::new(lambda_scope));
        let previous_level = self.session.infer.enter_child_level();
        let body_result = self.lower_catch_with_scrutinee(node, scrutinee);
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("catch lambda predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(scrutinee_value));
        let arg_eff = self.alloc_neg(Neg::Var(scrutinee_effect));
        let predicate_subtracts = self.lambda_predicate_subtracts(lambda_scope, Vec::new(), frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_recursive_case_like(
        &mut self,
        node: &Cst,
        label: Name,
        target: Option<Computation>,
        lambda_scope: LambdaScope,
        kind: RecursiveCaseLikeKind,
    ) -> Result<Computation, LoweringError> {
        let boundary = self.local_generalize_boundary;
        let previous_level = self.session.infer.enter_child_level();
        let before_locals = self.locals.len();
        let result = (|| {
            let value = self.fresh_type_var();
            let (pat, def) = self.bind_let_local_with_def(
                label.clone(),
                value,
                LocalCallReturnEffect::Annotated,
                None,
            );
            let body = match kind {
                RecursiveCaseLikeKind::Case => {
                    self.lower_case_lambda_without_label(node, lambda_scope)?
                }
                RecursiveCaseLikeKind::Catch => {
                    self.lower_catch_lambda_without_label(node, lambda_scope)?
                }
            };
            self.subtype_var_to_var(body.value, value);
            self.subtype_var_to_var(value, body.value);
            self.set_local_let_body(def, body.expr);
            self.generalize_local_binding(
                def,
                value,
                boundary,
                BindingFetch::from_evaluation(body.evaluation),
            );
            let self_ref = self.lower_name(label)?;
            let tail = match target {
                Some(target) => self.make_app(self_ref, target),
                None => self_ref,
            };
            Ok(self.prepend_block(
                LoweredLocalStmt {
                    stmt: Stmt::Let(Vis::My, pat, body.expr),
                    effect: body.effect,
                },
                tail,
            ))
        })();
        self.locals.truncate(before_locals);
        self.session.infer.restore_level(previous_level);
        result
    }

    fn lower_catch_with_scrutinee(
        &mut self,
        node: &Cst,
        scrutinee: Computation,
    ) -> Result<Computation, LoweringError> {
        let value = self.fresh_type_var();
        let effect = self.fresh_type_var();

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
            saw_value_arm |= lowered.value_covers_all;
            saw_effect_arm |= matches!(lowered.kind, LoweredCatchArmKind::Effect);
            arms.push(CatchArm {
                operation: lowered.operation,
                pat: lowered.pat,
                continuation: lowered.continuation,
                guard: lowered.guard,
                body: lowered.body,
            });
        }

        let final_effect = if handled.is_empty() {
            self.subtype_var_to_var(scrutinee.effect, effect);
            effect
        } else {
            let complete = handled.is_complete(self.modules, self.module, self.site);
            let rest_effect = if complete {
                effect
            } else {
                self.fresh_type_var()
            };
            let tail = self.alloc_neg(Neg::Var(rest_effect));
            let row = self.alloc_neg(Neg::Row(handled.row_items(), tail));
            self.subtype_scrutinee_effect_to_row(scrutinee.effect, scrutinee.effect_view, row);
            if !complete {
                self.subtype_var_to_var(scrutinee.effect, effect);
            }
            effect
        };
        if !saw_value_arm {
            self.subtype_var_to_var(scrutinee.value, value);
            self.subtype_var_to_var(value, scrutinee.value);
        }
        if !saw_value_arm && !saw_effect_arm {
            self.subtype_var_to_var(scrutinee.effect, final_effect);
        }

        let expr = self
            .session
            .poly
            .add_expr(Expr::Catch(scrutinee.expr, arms));
        Ok(Computation::new(
            expr,
            value,
            final_effect,
            Evaluation::Computation,
        ))
    }

    fn subtype_scrutinee_effect_to_row(
        &mut self,
        effect: TypeVar,
        effect_view: Option<EffectViewId>,
        row: NegId,
    ) {
        let lower = match effect_view.map(|view| self.effect_view(view).clone()) {
            Some(LocalEffect::Stack { inner, weight, .. }) => {
                // Keep the public effect slot constrained by the handled row so
                // shallow handlers can surface the resumed effect, while the
                // stack view drives subtraction hygiene.
                let full = self.alloc_pos(Pos::Var(effect));
                self.session.infer.subtype(full, row);
                let inner = self.alloc_pos(Pos::Var(inner));
                self.alloc_pos(Pos::Stack { inner, weight })
            }
            Some(LocalEffect::Var(effect)) => self.alloc_pos(Pos::Var(effect)),
            None => self.alloc_pos(Pos::Var(effect)),
        };
        self.session.infer.subtype(lower, row);
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
        let patterns = arm_patterns(arm);
        let body_node = arm_body_expr(arm).ok_or(LoweringError::MissingCatchArmBody)?;
        match patterns.as_slice() {
            [value_pattern] => {
                let pattern_value = self.fresh_type_var();
                let var_bindings = self.prepare_var_pattern_bindings(value_pattern)?;
                let pat = self.lower_match_pattern_with_var_bindings(
                    value_pattern,
                    pattern_value,
                    &var_bindings,
                )?;
                self.subtype_var_to_var(scrutinee_value, pattern_value);
                let guard_node = arm_guard_expr(arm);
                if guard_node.is_some() && !var_bindings.is_empty() {
                    return Err(LoweringError::UnsupportedPatternSyntax { kind: arm.kind() });
                }
                let guard = guard_node
                    .map(|guard| self.lower_arm_guard(&guard, result_effect))
                    .transpose()?;
                let active_var_bindings = self.install_var_pattern_bindings(&var_bindings)?;
                let mut body = self.lower_expr(&body_node)?;
                body = self.wrap_var_pattern_bindings(active_var_bindings, body)?;
                self.subtype_var_to_var(body.value, result_value);
                self.subtype_var_to_var(body.effect, result_effect);
                Ok(LoweredCatchArm {
                    kind: LoweredCatchArmKind::Value,
                    operation: None,
                    pat,
                    continuation: None,
                    guard,
                    body: body.expr,
                    value_covers_all: pat_covers_all(&self.session.poly, pat) && guard.is_none(),
                })
            }
            [effect_pattern, continuation_pattern] => {
                let effect_op = catch_effect_op(
                    pattern_path(effect_pattern).ok_or(LoweringError::MissingCatchArmPattern)?,
                );
                let operation_decl = self.resolve_catch_operation_decl(&effect_op);
                let handled_op = operation_decl
                    .as_ref()
                    .map(|decl| self.catch_effect_op_from_decl(decl))
                    .unwrap_or_else(|| effect_op.clone());
                let effect_var_bindings = self.prepare_var_pattern_bindings(effect_pattern)?;
                let continuation_var_bindings =
                    self.prepare_var_pattern_bindings(continuation_pattern)?;
                let guard_node = arm_guard_expr(arm);
                if guard_node.is_some()
                    && (!effect_var_bindings.is_empty() || !continuation_var_bindings.is_empty())
                {
                    return Err(LoweringError::UnsupportedPatternSyntax { kind: arm.kind() });
                }
                let saved_rewrites = self.pattern_binding_rewrites.clone();
                for binding in effect_var_bindings
                    .iter()
                    .chain(continuation_var_bindings.iter())
                {
                    self.pattern_binding_rewrites
                        .insert(binding.source.clone(), binding.init_name.clone());
                }
                let lowered_patterns = (|| {
                    let payload = self.lower_catch_effect_payload_pattern(effect_pattern)?;
                    let signature = self
                        .lower_catch_operation_signature(operation_decl.as_ref(), payload.value)?;
                    let row_item = signature
                        .as_ref()
                        .map(|signature| signature.row_item)
                        .unwrap_or_else(|| {
                            self.fallback_catch_effect_row_item(&handled_op, &payload)
                        });
                    let continuation_value = signature
                        .as_ref()
                        .map(|signature| signature.continuation_value)
                        .unwrap_or(payload.value);
                    let continuation = self.lower_catch_continuation_pattern(
                        continuation_pattern,
                        continuation_value,
                        scrutinee_value,
                        scrutinee_effect,
                    )?;
                    Ok((payload, row_item, continuation))
                })();
                self.pattern_binding_rewrites = saved_rewrites;
                let (payload, row_item, continuation) = lowered_patterns?;
                let guard = guard_node
                    .map(|guard| self.lower_arm_guard(&guard, result_effect))
                    .transpose()?;
                let active_effect_var_bindings =
                    self.install_var_pattern_bindings(&effect_var_bindings)?;
                let active_continuation_var_bindings =
                    self.install_var_pattern_bindings(&continuation_var_bindings)?;
                let mut body = self.lower_expr(&body_node)?;
                body = self.wrap_var_pattern_bindings(active_continuation_var_bindings, body)?;
                body = self.wrap_var_pattern_bindings(active_effect_var_bindings, body)?;
                self.subtype_var_to_var(body.value, result_value);
                self.subtype_var_to_var(body.effect, result_effect);
                let operation_covers_all =
                    pat_covers_all(&self.session.poly, payload.pat) && guard.is_none();
                let operation = poly::expr::CatchOperation {
                    path: handled_op.path.iter().map(|name| name.0.clone()).collect(),
                    def: operation_decl.as_ref().and_then(|decl| decl.def),
                };
                handled.record(handled_op, operation_covers_all, row_item);
                Ok(LoweredCatchArm {
                    kind: LoweredCatchArmKind::Effect,
                    operation: Some(operation),
                    pat: payload.pat,
                    continuation: Some(continuation),
                    guard,
                    body: body.expr,
                    value_covers_all: false,
                })
            }
            [] => Err(LoweringError::MissingCatchArmPattern),
            _ => Err(LoweringError::UnsupportedPatternSyntax { kind: arm.kind() }),
        }
    }

    fn lower_arm_guard(
        &mut self,
        guard_node: &Cst,
        result_effect: TypeVar,
    ) -> Result<poly::expr::ExprId, LoweringError> {
        let before_locals = self.locals.len();
        let guard = self.lower_expr(guard_node);
        self.locals.truncate(before_locals);
        let guard = guard?;
        let guard = self.apply_junction(guard)?;
        self.constrain_exact_primitive(guard.value, "bool");
        self.subtype_var_to_var(guard.effect, result_effect);
        Ok(guard.expr)
    }

    fn apply_junction(&mut self, condition: Computation) -> Result<Computation, LoweringError> {
        let junction = self.lower_std_value_ref(crate::std_paths::control_junction_value())?;
        Ok(self.make_app(junction, condition))
    }

    fn lower_catch_operation_signature(
        &mut self,
        operation_decl: Option<&ActOperationDecl>,
        payload_value: TypeVar,
    ) -> Result<Option<LoweredCatchOperationSignature>, LoweringError> {
        let Some(operation_decl) = operation_decl else {
            return Ok(None);
        };
        let Some(signature) = operation_decl.signature.as_ref() else {
            return self.lower_error_catch_operation_signature(operation_decl, payload_value);
        };

        let effect_type_vars = self.act_effect_type_var_names(operation_decl.effect.id);
        let mut builder = ann_type_builder(
            self.modules,
            operation_decl.effect.module,
            operation_decl.effect.order,
            None,
        );
        for name in &effect_type_vars {
            builder.add_bare_type_var(name.clone());
        }
        if let Some(copy) = self.modules.resolved_act_copy(operation_decl.effect.id) {
            add_type_var_aliases(&mut builder, &copy.type_var_aliases);
        }

        let effect_ann = builder.type_decl_application(operation_decl.effect.id, &effect_type_vars);
        let signature_ann = builder
            .build_type_expr(signature)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let Some((param, ret)) = operation_signature_param_ret(&signature_ann) else {
            return Ok(None);
        };

        let effect_value = self.fresh_type_var();
        let continuation_value = self.fresh_type_var();
        let mut lowerer = AnnConstraintLowerer::new(&mut self.session.infer, self.modules);
        lowerer
            .connect_value(effect_value, &effect_ann)
            .map_err(|error| LoweringError::AnnotationConstraint { error })?;
        lowerer
            .connect_value(payload_value, param)
            .map_err(|error| LoweringError::AnnotationConstraint { error })?;
        lowerer
            .connect_value(continuation_value, ret)
            .map_err(|error| LoweringError::AnnotationConstraint { error })?;
        let vars = lowerer.into_vars();
        let bindings = builder.type_var_bindings();
        let mut row_args = Vec::with_capacity(effect_type_vars.len());
        for name in effect_type_vars {
            let Some((_, ann_var)) = bindings
                .iter()
                .find(|(binding_name, _)| binding_name == &name)
            else {
                continue;
            };
            let Some(var) = vars.get(ann_var).copied() else {
                continue;
            };
            row_args.push(self.invariant_var_arg(var));
        }
        let family_path = self
            .modules
            .type_decl_path(&operation_decl.effect)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        self.session
            .infer
            .register_effect_family_path(family_path.clone());
        let row_item = self.alloc_neg(Neg::Con(family_path, row_args));
        Ok(Some(LoweredCatchOperationSignature {
            row_item,
            continuation_value,
        }))
    }

    fn lower_error_catch_operation_signature(
        &mut self,
        operation_decl: &ActOperationDecl,
        payload_value: TypeVar,
    ) -> Result<Option<LoweredCatchOperationSignature>, LoweringError> {
        if operation_decl.effect.kind != ModuleTypeKind::Error {
            return Ok(None);
        }
        let Some(def) = operation_decl.def else {
            return Ok(None);
        };
        let Some((error, variant)) = self.modules.error_variant_for_operation(def) else {
            return Ok(None);
        };
        let error = error.clone();
        let variant = variant.clone();
        let Some(payload) =
            self.error_variant_payload_signature(&operation_decl.effect, &error, &variant)?
        else {
            return Ok(None);
        };
        let ret = SignatureType::Builtin(BuiltinType::Never);
        let effect = owner_signature_type(error.owner, &error.type_vars);
        let mut vars = error_type_var_slots(&mut self.session.infer, &error.type_vars);

        vars = self.connect_value_to_signature(payload_value, &payload, vars)?;
        let continuation_value = self.fresh_type_var();
        vars = self.connect_value_to_signature(continuation_value, &ret, vars)?;

        let mut lowerer = SignatureLowerer::with_vars(&mut self.session.infer, self.modules, vars);
        let row_item = lowerer
            .lower_neg(&effect)
            .map_err(|error| LoweringError::SignatureConstraint { error })?;

        Ok(Some(LoweredCatchOperationSignature {
            row_item,
            continuation_value,
        }))
    }

    fn connect_value_to_signature(
        &mut self,
        value: TypeVar,
        signature: &SignatureType,
        vars: FxHashMap<String, TypeVar>,
    ) -> Result<FxHashMap<String, TypeVar>, LoweringError> {
        let mut lowerer = SignatureLowerer::with_vars(&mut self.session.infer, self.modules, vars);
        let lower = lowerer
            .lower_pos(signature)
            .map_err(|error| LoweringError::SignatureConstraint { error })?;
        let upper = lowerer
            .lower_neg(signature)
            .map_err(|error| LoweringError::SignatureConstraint { error })?;
        let target_upper = lowerer.infer.alloc_neg(Neg::Var(value));
        let target_lower = lowerer.infer.alloc_pos(Pos::Var(value));
        lowerer.infer.subtype(lower, target_upper);
        lowerer.infer.subtype(target_lower, upper);
        Ok(lowerer.vars)
    }

    fn error_variant_payload_signature(
        &self,
        decl: &ModuleTypeDecl,
        error: &crate::ErrorDecl,
        variant: &crate::ErrorVariantDecl,
    ) -> Result<Option<SignatureType>, LoweringError> {
        let builder = NegSignatureBuilder::with_self_alias(
            self.modules,
            error.module,
            decl.order,
            SignatureSelfAlias {
                owner: error.owner,
                type_vars: error.type_vars.clone(),
            },
        );
        match &variant.payload {
            ConstructorPayload::Unit => Ok(Some(SignatureType::Builtin(BuiltinType::Unit))),
            ConstructorPayload::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| {
                        item.ty
                            .as_ref()
                            .map(|ty| builder.build_type_expr(ty))
                            .transpose()
                            .map_err(|error| LoweringError::NegSignatureBuild { error })
                            .map(|signature| {
                                signature
                                    .map(|signature| signature.as_type().clone())
                                    .unwrap_or(SignatureType::Builtin(BuiltinType::Unit))
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                match items.as_slice() {
                    [] => Ok(Some(SignatureType::Builtin(BuiltinType::Unit))),
                    [item] => Ok(Some(item.clone())),
                    _ => Ok(Some(SignatureType::Tuple(items))),
                }
            }
            ConstructorPayload::Record(_) => Ok(None),
        }
    }

    fn resolve_catch_operation_decl(&self, effect_op: &CatchEffectOp) -> Option<ActOperationDecl> {
        if let Some(target) = self
            .modules
            .value_path_at(self.module, &effect_op.path, self.site)
        {
            if let Some(decl) = self.modules.act_operation_decl_by_def(target) {
                return Some(decl);
            }
            if let Some(operation) = self.modules.error_operation_for_constructor(target)
                && let Some(decl) = self.modules.act_operation_decl_by_def(operation)
            {
                return Some(decl);
            }
        }
        let operation = effect_op.operation.as_ref()?;
        self.modules
            .act_operation_decls_at(self.module, &effect_op.family_path, self.site)
            .into_iter()
            .find(|decl| &decl.name == operation)
    }

    fn catch_effect_op_from_decl(&self, decl: &ActOperationDecl) -> CatchEffectOp {
        CatchEffectOp {
            path: self
                .modules
                .type_decl_path(&decl.effect)
                .segments
                .into_iter()
                .chain(std::iter::once(decl.name.clone()))
                .collect(),
            family_path: self
                .modules
                .type_decl_path(&decl.effect)
                .segments
                .into_iter()
                .collect(),
            operation: Some(decl.name.clone()),
        }
    }

    fn fallback_catch_effect_row_item(
        &mut self,
        effect_op: &CatchEffectOp,
        payload: &LoweredCatchPayloadPattern,
    ) -> NegId {
        let row_args = payload
            .effect_args
            .iter()
            .copied()
            .map(|arg| self.invariant_var_arg(arg))
            .collect();
        let family_path = effect_op
            .family_path
            .iter()
            .map(|name| name.0.clone())
            .collect::<Vec<_>>();
        self.session
            .infer
            .register_effect_family_path(family_path.clone());
        self.alloc_neg(Neg::Con(family_path, row_args))
    }

    fn lower_catch_effect_payload_pattern(
        &mut self,
        effect_pattern: &Cst,
    ) -> Result<LoweredCatchPayloadPattern, LoweringError> {
        let payloads = pattern_payloads(effect_pattern);
        match payloads.as_slice() {
            [] => {
                let value = self.fresh_type_var();
                Ok(LoweredCatchPayloadPattern {
                    pat: self.session.poly.add_pat(Pat::Wild),
                    value,
                    effect_args: Vec::new(),
                })
            }
            [payload] => {
                let value = self.fresh_type_var();
                Ok(LoweredCatchPayloadPattern {
                    pat: self.lower_match_pattern(payload, value)?,
                    value,
                    effect_args: vec![value],
                })
            }
            _ => {
                let value = self.fresh_type_var();
                let mut pats = Vec::with_capacity(payloads.len());
                let mut pos_items = Vec::with_capacity(payloads.len());
                let mut neg_items = Vec::with_capacity(payloads.len());
                let mut effect_args = Vec::with_capacity(payloads.len());
                for payload in payloads {
                    let item_value = self.fresh_type_var();
                    pats.push(self.lower_match_pattern(&payload, item_value)?);
                    pos_items.push(self.alloc_pos(Pos::Var(item_value)));
                    neg_items.push(self.alloc_neg(Neg::Var(item_value)));
                    effect_args.push(item_value);
                }
                self.constrain_lower(value, Pos::Tuple(pos_items));
                self.constrain_upper(value, Neg::Tuple(neg_items));
                Ok(LoweredCatchPayloadPattern {
                    pat: self.session.poly.add_pat(Pat::Tuple(pats)),
                    value,
                    effect_args,
                })
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
            PatternItem::Ident { name, .. } if name.0 == "_" => {
                Ok(self.session.poly.add_pat(Pat::Wild))
            }
            PatternItem::Ident { name, .. } => {
                let continuation_value = self.fresh_type_var();
                let pat = self.bind_pattern_local(
                    name,
                    continuation_value,
                    None,
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
            PatternItem::Number(_) | PatternItem::String(_) | PatternItem::Paren(_) => {
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
        let lower_arg = self.alloc_neg(Neg::Var(payload_value));
        let lower_arg_eff = self.never_neg();
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
        let upper_arg_eff = self.alloc_pos(Pos::Bot);
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
    operation: Option<poly::expr::CatchOperation>,
    pat: PatId,
    continuation: Option<PatId>,
    guard: Option<poly::expr::ExprId>,
    body: poly::expr::ExprId,
    value_covers_all: bool,
}

struct LoweredIfArm {
    condition: Computation,
    body: Computation,
}

fn case_arm_rule_pattern(arm: &Cst) -> Option<Cst> {
    let pattern = arm_pattern(arm)?;
    let rule = single_rule_pattern(&pattern)?;
    rule_pattern_needs_case_parser(&rule).then_some(rule)
}

fn single_rule_pattern(pattern: &Cst) -> Option<Cst> {
    let items = pattern
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item))
        .collect::<Vec<_>>();
    let [NodeOrToken::Node(rule)] = items.as_slice() else {
        return None;
    };
    matches!(rule.kind(), SyntaxKind::RuleLit | SyntaxKind::RuleExpr).then(|| rule.clone())
}

fn rule_pattern_needs_case_parser(rule: &Cst) -> bool {
    match rule.kind() {
        SyntaxKind::RuleExpr => true,
        SyntaxKind::RuleLit => {
            rule.children().any(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::RuleLazyCapture | SyntaxKind::RuleLitInterp
                )
            }) || rule
                .children_with_tokens()
                .filter_map(|item| item.into_token())
                .any(|token| token.kind() == SyntaxKind::RuleLitStart)
        }
        _ => false,
    }
}

fn rule_case_branches(rule: &Cst) -> Result<Vec<RuleCaseBranch>, LoweringError> {
    match rule.kind() {
        SyntaxKind::RuleLit => rule_lit_case_branches(rule),
        SyntaxKind::RuleExpr => rule_expr_case_branches(rule),
        kind => Err(LoweringError::UnsupportedSyntax { kind }),
    }
}

struct LoweredCatchPayloadPattern {
    pat: PatId,
    value: TypeVar,
    effect_args: Vec<TypeVar>,
}

struct LoweredCatchOperationSignature {
    row_item: NegId,
    continuation_value: TypeVar,
}

fn error_type_var_slots(infer: &mut crate::Arena, names: &[String]) -> FxHashMap<String, TypeVar> {
    names
        .iter()
        .cloned()
        .map(|name| (name, infer.fresh_type_var()))
        .collect()
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

#[derive(Clone)]
struct CatchEffectOp {
    path: Vec<Name>,
    family_path: Vec<Name>,
    operation: Option<Name>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LoweredCatchArmKind {
    Value,
    Effect,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RecursiveCaseLikeKind {
    Case,
    Catch,
}
