//! Extracted expression lowering methods.

use super::super::*;
use super::*;

impl<'a> ExprLowerer<'a> {
    pub(in crate::lowering) fn lower_tail_node(
        &mut self,
        acc: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::ApplyML | SyntaxKind::ApplyC | SyntaxKind::ApplyColon => {
                self.apply_arguments(acc, node)
            }
            SyntaxKind::Field => self.lower_field_selection(acc, node),
            SyntaxKind::Index => self.lower_index_selection(acc, node),
            SyntaxKind::Assign => self.lower_ref_assignment(acc, node),
            SyntaxKind::InfixNode => self.lower_infix_op_use(acc, node),
            SyntaxKind::SuffixNode => self.lower_suffix_op_use(acc, node),
            SyntaxKind::PipeNode => self.lower_pipe_node(acc, node),
            SyntaxKind::TypeAnn => self.lower_type_annotation_tail(acc, node),
            kind => Err(LoweringError::UnsupportedSyntax { kind }),
        }
    }

    pub(in crate::lowering) fn lower_pipe_node(
        &mut self,
        acc: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let rhs = node
            .children()
            .find(|child| child.kind() == SyntaxKind::Expr)
            .ok_or(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::PipeNode,
            })?;
        let pipe_arg = Some(PipeArg { expr: acc });
        if let Some(with_block) = rhs
            .children()
            .find(|child| child.kind() == SyntaxKind::WithBlock)
        {
            return self.lower_with_expr_chain(&rhs, &with_block, LambdaScope::Anonymous, pipe_arg);
        }
        self.lower_expr_chain_prefix_with_pipe_arg(&rhs, LambdaScope::Anonymous, false, pipe_arg)
    }

    pub(in crate::lowering) fn lower_type_annotation_tail(
        &mut self,
        acc: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let type_expr = node
            .children()
            .find(|child| child.kind() == SyntaxKind::TypeExpr)
            .ok_or(LoweringError::AnnotationBuild {
                error: AnnBuildError::ExpectedTypeExpr { kind: node.kind() },
            })?;
        let mut builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
            &self.type_name_aliases,
        );
        let ann = builder
            .build_type_expr(&type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        AnnConstraintLowerer::new(&mut self.session.infer, self.modules)
            .connect_computation(
                AnnComputationTarget {
                    value: acc.value,
                    effect: acc.effect,
                },
                &ann,
            )
            .map(|_| acc)
            .map_err(|error| LoweringError::AnnotationConstraint { error })
    }

    pub(in crate::lowering) fn apply_arguments(
        &mut self,
        mut callee: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let args = self.apply_argument_exprs(callee, node);
        if args.is_empty() {
            let unit = self.unit_expr();
            return Ok(self.make_app(callee, unit));
        }
        for arg in args {
            let lowered_arg = self.lower_expr(&arg)?;
            callee = self.make_app(callee, lowered_arg);
        }
        Ok(callee)
    }

    pub(in crate::lowering) fn apply_argument_exprs(
        &self,
        callee: Computation,
        node: &Cst,
    ) -> Vec<Cst> {
        let args = apply_argument_nodes(node);
        let Some(arity) = self.declared_constructor_payload_arity(callee) else {
            return args;
        };
        declared_constructor_expr_payloads(args, arity)
    }

    pub(in crate::lowering) fn declared_constructor_payload_arity(
        &self,
        callee: Computation,
    ) -> Option<usize> {
        let Expr::Var(reference) = self.session.poly.expr(callee.expr) else {
            return None;
        };
        let target = self
            .known_ref_targets
            .get(reference)
            .copied()
            .or_else(|| self.session.poly.ref_target(*reference))?;
        let constructor = self.modules.constructor_by_def(target)?;
        Some(constructor_payload_arity(&constructor.payload))
    }

    pub(in crate::lowering) fn lower_field_selection(
        &mut self,
        receiver: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let name = field_name(node).ok_or(LoweringError::MissingFieldName)?;
        if name == "return"
            && let Some(target) = self.sub_label_return_target(receiver.expr).cloned()
        {
            return Ok(self.lower_sub_return_target(&target));
        }
        Ok(self.lower_synthetic_selection(receiver, name))
    }

    pub(in crate::lowering) fn lower_index_selection(
        &mut self,
        receiver: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let arg_node = index_expr(node).ok_or(LoweringError::MissingIndexArgument)?;
        let index = self.lower_expr(&arg_node)?;
        let selection = self.lower_synthetic_selection(receiver, "index".to_string());
        Ok(self.make_app(selection, index))
    }

    pub(in crate::lowering) fn lower_ref_assignment(
        &mut self,
        reference: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let value = match assignment_value_expr(node) {
            Some(expr) => self.lower_expr(&expr)?,
            None => self.unit_expr(),
        };
        Ok(self.make_ref_set(reference, value))
    }

    pub(in crate::lowering) fn make_ref_set(
        &mut self,
        reference: Computation,
        value: Computation,
    ) -> Computation {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let ref_effect = self.fresh_type_var();
        let expected_value = self.fresh_type_var();

        self.constrain_exact_primitive(result_value, "unit");
        self.subtype_var_to_var(reference.effect, result_effect);
        self.subtype_var_to_var(value.effect, result_effect);
        self.subtype_var_to_var(ref_effect, result_effect);
        self.subtype_var_to_var(value.value, expected_value);

        let effect_arg = self.invariant_var_arg(ref_effect);
        let value_arg = self.invariant_var_arg(expected_value);
        let args = vec![effect_arg, value_arg];
        self.constrain_lower(
            reference.value,
            Pos::Con(crate::std_paths::control_var_ref_type(), args.clone()),
        );
        self.constrain_upper(
            reference.value,
            Neg::Con(crate::std_paths::control_var_ref_type(), args),
        );

        let expr = self
            .session
            .poly
            .add_expr(Expr::RefSet(reference.expr, value.expr));
        Computation::computation(expr, result_value, result_effect)
    }

    pub(in crate::lowering) fn lower_synthetic_selection(
        &mut self,
        receiver: Computation,
        name: String,
    ) -> Computation {
        let method_value = self.fresh_type_var();
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let call_effect = self.fresh_type_var();
        let method = self.alloc_pos(Pos::Var(method_value));
        let receiver_value = self.alloc_pos(Pos::Var(receiver.value));
        let receiver_arg_eff = self.alloc_pos(Pos::Bot);
        let ret_eff = self.alloc_neg(Neg::Var(call_effect));
        let ret = self.alloc_neg(Neg::Var(result_value));
        let method_upper = self.alloc_neg(Neg::Fun {
            arg: receiver_value,
            arg_eff: receiver_arg_eff,
            ret_eff,
            ret,
        });
        self.session.infer.subtype(method, method_upper);
        self.subtype_var_to_var(receiver.effect, result_effect);
        self.subtype_var_to_var(call_effect, result_effect);

        let select = self.session.poly.add_select(name);
        self.session.register_selection_use(
            select,
            SelectionUse {
                parent: self.parent,
                method_value,
                receiver_value: receiver.value,
                receiver_effect: receiver.effect,
                local_method_scope: self.local_method_scope,
            },
        );
        let expr = self
            .session
            .poly
            .add_expr(Expr::Select(receiver.expr, select));
        Computation::new(expr, result_value, result_effect, receiver.evaluation)
    }

    /// op 使用ノードから symbol を読んで mangled 名で解決する。戻りは (op 参照, lazy)。
    pub(in crate::lowering) fn resolve_op_use(
        &mut self,
        fixity: &'static str,
        node: &Cst,
    ) -> Result<(Computation, bool), LoweringError> {
        let symbol = node
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .find_map(|item| item.into_token())
            .map(|tok| tok.text().to_string())
            .ok_or(LoweringError::MissingOpName)?;
        self.resolve_op_symbol(fixity, &symbol)
    }

    pub(in crate::lowering) fn resolve_op_symbol(
        &mut self,
        fixity: &'static str,
        symbol: &str,
    ) -> Result<(Computation, bool), LoweringError> {
        let name = crate::op_value_name(fixity, symbol);
        let Some(target) = self.modules.lexical_value_at(self.module, &name, self.site) else {
            return Err(LoweringError::UnresolvedName { name });
        };
        let lazy = self.modules.is_lazy_op(target);
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let reference = self.session.poly.add_ref();
        if let Some(labels) = self.labels.as_mut() {
            labels.set_ref_label(reference, name.0);
        }
        self.session.refs.insert(
            reference,
            RefUse {
                parent: self.parent,
                value,
            },
        );
        self.known_ref_targets.insert(reference, target);
        self.session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: reference,
            target,
        });
        let expr = self.session.poly.add_expr(Expr::Var(reference));
        Ok((Computation::value(expr, value, effect), lazy))
    }

    pub(in crate::lowering) fn lower_infix_op_use(
        &mut self,
        acc: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let (op, lazy) = self.resolve_op_use("infix", node)?;
        let rhs_node = node
            .children()
            .find(|child| child.kind() == SyntaxKind::Expr)
            .ok_or(LoweringError::MissingOpOperand)?;
        let rhs = self.lower_expr(&rhs_node)?;
        let (lhs, rhs) = if lazy {
            (self.thunk_computation(acc), self.thunk_computation(rhs))
        } else {
            (acc, rhs)
        };
        let applied = self.make_app(op, lhs);
        Ok(self.make_app(applied, rhs))
    }

    pub(in crate::lowering) fn lower_suffix_op_use(
        &mut self,
        acc: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let (op, lazy) = self.resolve_op_use("suffix", node)?;
        let arg = if lazy {
            self.thunk_computation(acc)
        } else {
            acc
        };
        Ok(self.make_app(op, arg))
    }

    pub(in crate::lowering) fn lower_prefix_op_use(
        &mut self,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let (op, lazy) = self.resolve_op_use("prefix", node)?;
        let operand_node = node
            .children()
            .find(|child| child.kind() == SyntaxKind::Expr)
            .ok_or(LoweringError::MissingOpOperand)?;
        let operand = self.lower_expr(&operand_node)?;
        let arg = if lazy {
            self.thunk_computation(operand)
        } else {
            operand
        };
        Ok(self.make_app(op, arg))
    }

    pub(in crate::lowering) fn lower_nullfix_op_use(
        &mut self,
        symbol: &str,
    ) -> Result<Computation, LoweringError> {
        let (op, _lazy) = self.resolve_op_symbol("nullfix", symbol)?;
        let unit = self.unit_expr();
        Ok(self.make_app(op, unit))
    }

    /// `\() -> body` の thunk。lazy op の被演算子と nullfix op の本体に使う。
    pub(in crate::lowering) fn thunk_computation(&mut self, body: Computation) -> Computation {
        let pat = self.session.poly.add_pat(Pat::Lit(Lit::Unit));
        let param = self.fresh_type_var();
        self.constrain_exact_primitive(param, "unit");
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(param));
        let arg_eff = self.never_neg();
        let ret_eff = self.alloc_pos(Pos::Var(body.effect));
        let ret = self.alloc_pos(Pos::Var(body.value));
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
        Computation::value(expr, value, effect)
    }

    pub(in crate::lowering) fn make_app(
        &mut self,
        callee: Computation,
        arg: Computation,
    ) -> Computation {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let call_effect = self.fresh_type_var();

        let arg_value = self.alloc_pos(Pos::Var(arg.value));
        let arg_effect = self.alloc_pos(Pos::Var(arg.effect));
        let return_effect = self.unannotated_local_callee_return_effect(&callee, call_effect);
        let return_value = self.alloc_neg(Neg::Var(result_value));
        let callee_upper = self.alloc_neg(Neg::Fun {
            arg: arg_value,
            arg_eff: arg_effect,
            ret_eff: return_effect.upper,
            ret: return_value,
        });
        self.subtype(Pos::Var(callee.value), callee_upper);
        self.subtype_var_to_var(callee.effect, result_effect);
        self.subtype_pos_to_var(return_effect.lower, result_effect);

        let expr = self.session.poly.add_expr(Expr::App(callee.expr, arg.expr));
        Computation::computation(expr, result_value, result_effect)
    }

    pub(in crate::lowering) fn unit_expr(&mut self) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(value, primitive_type("unit"));
        let expr = self.session.poly.add_expr(Expr::Lit(Lit::Unit));
        Computation::value(expr, value, effect)
    }

    pub(in crate::lowering) fn fresh_type_var(&mut self) -> TypeVar {
        self.session.infer.fresh_type_var()
    }

    pub(in crate::lowering) fn unannotated_local_callee_return_effect(
        &mut self,
        callee: &Computation,
        call_effect: TypeVar,
    ) -> ApplicationReturnEffect {
        let bare = self.alloc_neg(Neg::Var(call_effect));
        let lower = self.alloc_pos(Pos::Var(call_effect));
        let Some(def) = self.local_callee_def(callee) else {
            return ApplicationReturnEffect { upper: bare, lower };
        };
        let Some(local) = self.local_binding_by_def(def) else {
            return ApplicationReturnEffect { upper: bare, lower };
        };
        if !matches!(self.session.poly.defs.get(local.def), Some(Def::Arg)) {
            return ApplicationReturnEffect { upper: bare, lower };
        }
        if local.call_return_effect != LocalCallReturnEffect::Unannotated {
            return ApplicationReturnEffect { upper: bare, lower };
        }

        let Some(frame_index) = self.unannotated_call_frame_index(local) else {
            return ApplicationReturnEffect { upper: bare, lower };
        };
        if !self
            .function_frames
            .get(frame_index)
            .is_some_and(|frame| frame.scope == LambdaScope::Defined)
        {
            return ApplicationReturnEffect { upper: bare, lower };
        }
        let (subtract, inserted) = match self.function_frames[frame_index].unannotated_call_subtract
        {
            Some(subtract) => (subtract, false),
            None => {
                let subtract = self.session.infer.fresh_subtract_id();
                let frame = &mut self.function_frames[frame_index];
                frame.unannotated_call_subtract = Some(subtract);
                frame.subtracts.push(subtract);
                (subtract, true)
            }
        };
        if inserted {
            self.refresh_active_defined_skeletons_for_frame(frame_index);
        }
        let weight = StackWeight::push(subtract, Subtractability::Empty);
        let effect_pos = self.alloc_pos(Pos::Var(call_effect));
        let lower = self.alloc_pos(Pos::Stack {
            inner: effect_pos,
            weight: weight.clone(),
        });
        let upper = self.alloc_neg(Neg::Stack {
            inner: bare,
            weight,
        });
        ApplicationReturnEffect { upper, lower }
    }

    pub(in crate::lowering) fn unannotated_call_frame_index(
        &self,
        local: &LocalBinding,
    ) -> Option<usize> {
        let frame_index = local.unannotated_call_frame?;
        let direct_defined_call = self
            .function_frames
            .last()
            .is_some_and(|frame| frame.scope == LambdaScope::Defined);
        if direct_defined_call || !self.sub_syntax_scopes.is_empty() {
            return Some(frame_index);
        }
        None
    }

    pub(in crate::lowering) fn mark_defined_unannotated_arg_call_frame(
        &mut self,
        local_start: usize,
        frame_index: usize,
    ) {
        for local in &mut self.locals[local_start..] {
            if local.call_return_effect == LocalCallReturnEffect::Unannotated {
                local.unannotated_call_frame = Some(frame_index);
            }
        }
    }

    pub(in crate::lowering) fn refresh_active_defined_skeletons_for_frame(
        &mut self,
        frame_index: usize,
    ) {
        let updates = self
            .active_defined_skeletons
            .iter()
            .filter(|active| {
                frame_index >= active.before_frames
                    && frame_index < active.before_frames + active.params.len()
            })
            .cloned()
            .collect::<Vec<_>>();
        for active in updates {
            let frame_end = active.before_frames + active.params.len();
            let frames = self.function_frames[active.before_frames..frame_end].to_vec();
            self.connect_defined_lambda_skeleton_predicates(
                &active.params,
                &frames,
                &active.skeleton,
                SkeletonPredicateMode::NonEmptyOnly,
            );
        }
    }

    pub(in crate::lowering) fn local_callee_def(&self, callee: &Computation) -> Option<DefId> {
        let Expr::Var(reference) = self.session.poly.expr(callee.expr) else {
            return None;
        };
        self.session.poly.ref_target(*reference)
    }

    pub(in crate::lowering) fn local_binding_by_def(&self, def: DefId) -> Option<&LocalBinding> {
        self.locals.iter().rev().find(|local| local.def == def)
    }

    pub(in crate::lowering) fn instantiate_local_value(&mut self, local: &LocalBinding) -> TypeVar {
        let Some(scheme) = local.scheme.as_ref() else {
            return local.value;
        };
        let value = self.fresh_type_var();
        let level = self.session.infer.current_level();
        let predicate = crate::instantiate::instantiate_scheme(
            &self.session.poly.typ,
            &mut self.session.infer,
            level,
            scheme,
        );
        let upper = self.alloc_neg(Neg::Var(value));
        self.session.infer.subtype(predicate, upper);
        value
    }

    pub(in crate::lowering) fn generalize_local_binding(
        &mut self,
        def: DefId,
        value: TypeVar,
        boundary: TypeLevel,
        fetch: BindingFetch,
    ) {
        let mut non_generic = self.local_non_generic_vars(def, value);
        if fetch.runs_computation() {
            non_generic.insert(value);
        }
        let needs_recursive_effect_passthrough = self
            .local_binding_needs_recursive_effect_passthrough(def)
            && self.local_let_body_references(def);
        let mut forced_quantifiers = Vec::new();
        if needs_recursive_effect_passthrough {
            forced_quantifiers = add_root_vars_connected_to_environment(
                self.session.infer.constraints(),
                value,
                boundary,
                &mut non_generic,
            );
        }
        let generalized = generalize_type_var_with_boundaries(
            self.session.infer.constraints(),
            value,
            fetch.generalize_boundary(boundary),
            boundary.child(),
            &non_generic,
        );
        let mut finalized = crate::generalize::finalize_generalized_compact_root(
            &mut self.session.poly.typ,
            self.session.infer.constraints(),
            &generalized,
        );
        let use_monomorphic_local = !forced_quantifiers.is_empty();
        add_forced_quantifiers(&mut finalized.scheme, forced_quantifiers);
        self.set_local_let_scheme(def, finalized.scheme.clone());
        if let Some(local) = self.locals.iter_mut().rev().find(|local| local.def == def) {
            local.scheme = (!use_monomorphic_local || self.parent_has_type_annotation)
                .then_some(finalized.scheme);
        }
    }

    pub(in crate::lowering) fn local_non_generic_vars(
        &self,
        exclude: DefId,
        exclude_value: TypeVar,
    ) -> FxHashSet<TypeVar> {
        let mut vars = FxHashSet::default();
        let machine = self.session.infer.constraints();
        for local in &self.locals {
            if local.def == exclude {
                continue;
            }
            vars.insert(local.value);
            if let Some(effect) = local.effect.as_ref() {
                effect.collect_vars(&mut vars);
            }
            let Some(bounds) = machine.bounds().of(local.value) else {
                continue;
            };
            for lower in bounds.lowers() {
                collect_pos_id_vars(machine.types(), lower.pos, &mut vars);
            }
            for upper in bounds.uppers() {
                collect_neg_id_vars(machine.types(), upper.neg, &mut vars);
            }
        }
        close_non_generic_vars(machine, &mut vars, exclude_value);
        vars
    }

    fn local_let_body_references(&self, def: DefId) -> bool {
        let Some(Def::Let {
            body: Some(body), ..
        }) = self.session.poly.defs.get(def)
        else {
            return false;
        };
        expr_references_def(&self.session.poly, *body, def)
    }

    fn local_binding_needs_recursive_effect_passthrough(&self, def: DefId) -> bool {
        self.local_binding_by_def(def)
            .is_some_and(|local| local.recursive_effect_passthrough)
    }

    pub(in crate::lowering) fn lambda_predicate_subtracts(
        &mut self,
        lambda_scope: LambdaScope,
        mut annotation_subtracts: Vec<SubtractId>,
        mut frame: FunctionPredicateFrame,
    ) -> Vec<SubtractId> {
        if lambda_scope != LambdaScope::Defined {
            return Vec::new();
        }
        annotation_subtracts.append(&mut frame.subtracts);
        annotation_subtracts.sort_by_key(|id| id.0);
        annotation_subtracts.dedup();
        annotation_subtracts
    }

    pub(in crate::lowering) fn lambda_output_predicate(
        &mut self,
        body: &Computation,
        subtracts: &[SubtractId],
    ) -> (PosId, PosId) {
        self.lambda_output_predicate_vars(body.effect, body.value, subtracts)
    }

    pub(in crate::lowering) fn lambda_output_predicate_vars(
        &mut self,
        body_effect: TypeVar,
        body_value: TypeVar,
        subtracts: &[SubtractId],
    ) -> (PosId, PosId) {
        if subtracts.is_empty() {
            let ret_eff = self.alloc_pos(Pos::Var(body_effect));
            let ret = self.alloc_pos(Pos::Var(body_value));
            return (ret_eff, ret);
        }

        let ret_eff = self.alloc_pos(Pos::Var(body_effect));
        let ret = self.alloc_pos(Pos::Var(body_value));
        (
            self.wrap_pos_with_subtracts(ret_eff, subtracts),
            self.wrap_pos_with_subtracts(ret, subtracts),
        )
    }
}

fn expr_references_def(poly: &poly::expr::Arena, expr: ExprId, def: DefId) -> bool {
    match poly.expr(expr) {
        Expr::Lit(_) | Expr::PrimitiveOp(_) => false,
        Expr::Var(reference) => poly.ref_target(*reference) == Some(def),
        Expr::App(callee, arg) | Expr::RefSet(callee, arg) => {
            expr_references_def(poly, *callee, def) || expr_references_def(poly, *arg, def)
        }
        Expr::Lambda(_, body) => expr_references_def(poly, *body, def),
        Expr::Tuple(items) => items
            .iter()
            .any(|item| expr_references_def(poly, *item, def)),
        Expr::Record { fields, spread } => {
            fields
                .iter()
                .any(|(_, field)| expr_references_def(poly, *field, def))
                || record_spread_expr_references_def(poly, spread, def)
        }
        Expr::PolyVariant(_, payloads) => payloads
            .iter()
            .any(|payload| expr_references_def(poly, *payload, def)),
        Expr::Select(receiver, _) => expr_references_def(poly, *receiver, def),
        Expr::Case(scrutinee, arms) => {
            expr_references_def(poly, *scrutinee, def)
                || arms.iter().any(|arm| {
                    arm.guard
                        .is_some_and(|guard| expr_references_def(poly, guard, def))
                        || expr_references_def(poly, arm.body, def)
                })
        }
        Expr::Catch(scrutinee, arms) => {
            expr_references_def(poly, *scrutinee, def)
                || arms.iter().any(|arm| {
                    arm.guard
                        .is_some_and(|guard| expr_references_def(poly, guard, def))
                        || expr_references_def(poly, arm.body, def)
                })
        }
        Expr::Block(stmts, tail) => {
            stmts
                .iter()
                .any(|stmt| stmt_references_def(poly, stmt, def))
                || tail.is_some_and(|tail| expr_references_def(poly, tail, def))
        }
    }
}

fn stmt_references_def(poly: &poly::expr::Arena, stmt: &Stmt, def: DefId) -> bool {
    match stmt {
        Stmt::Let(_, _, body) | Stmt::Expr(body) => expr_references_def(poly, *body, def),
        Stmt::Module(_, stmts) => stmts
            .iter()
            .any(|stmt| stmt_references_def(poly, stmt, def)),
    }
}

fn record_spread_expr_references_def(
    poly: &poly::expr::Arena,
    spread: &RecordSpread<ExprId>,
    def: DefId,
) -> bool {
    match spread {
        RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
            expr_references_def(poly, *expr, def)
        }
        RecordSpread::None => false,
    }
}

fn close_non_generic_vars(
    machine: &crate::constraints::ConstraintMachine,
    vars: &mut FxHashSet<TypeVar>,
    exclude: TypeVar,
) {
    vars.remove(&exclude);
    let mut pending = vars.iter().copied().collect::<Vec<_>>();
    let mut visited = FxHashSet::default();
    while let Some(var) = pending.pop() {
        if !visited.insert(var) {
            continue;
        }
        let Some(bounds) = machine.bounds().of(var) else {
            continue;
        };
        let mut found = FxHashSet::default();
        for lower in bounds.lowers() {
            collect_pos_id_vars(machine.types(), lower.pos, &mut found);
        }
        for upper in bounds.uppers() {
            collect_neg_id_vars(machine.types(), upper.neg, &mut found);
        }
        for var in found {
            if var == exclude || !vars.insert(var) {
                continue;
            }
            pending.push(var);
        }
    }
}

fn add_root_vars_connected_to_environment(
    machine: &crate::constraints::ConstraintMachine,
    root: TypeVar,
    boundary: TypeLevel,
    non_generic: &mut FxHashSet<TypeVar>,
) -> Vec<TypeVar> {
    let compact = crate::compact::compact_type_var_for_scheme(machine, root);
    let environment = non_generic.clone();
    let mut effect_vars = compact_root_effect_vars(&compact)
        .into_iter()
        .filter(|var| *var != root)
        .collect::<Vec<_>>();
    effect_vars.sort_by_key(|var| var.0);

    let representatives =
        effect_representatives_reaching_environment(machine, effect_vars, &environment, boundary);
    non_generic.extend(representatives.iter().copied());
    representatives
}

fn add_forced_quantifiers(scheme: &mut Scheme, vars: Vec<TypeVar>) {
    for var in vars {
        if !scheme.quantifiers.contains(&var) {
            scheme.quantifiers.push(var);
        }
    }
    scheme.quantifiers.sort_by_key(|var| var.0);
}

fn compact_root_effect_vars(root: &CompactRoot) -> FxHashSet<TypeVar> {
    let mut vars = FxHashSet::default();
    collect_compact_type_effect_vars(&root.root, false, &mut vars);
    for rec in &root.rec_vars {
        collect_compact_bounds_effect_vars(&rec.bounds, false, &mut vars);
    }
    vars
}

fn collect_compact_type_effect_vars(
    ty: &CompactType,
    in_effect_position: bool,
    out: &mut FxHashSet<TypeVar>,
) {
    if in_effect_position {
        out.extend(ty.vars.iter().map(|var| var.var));
    }
    for args in ty.cons.values() {
        for arg in args {
            collect_compact_bounds_effect_vars(arg, false, out);
        }
    }
    for fun in &ty.funs {
        collect_compact_type_effect_vars(&fun.arg, false, out);
        collect_compact_type_effect_vars(&fun.arg_eff, true, out);
        collect_compact_type_effect_vars(&fun.ret_eff, true, out);
        collect_compact_type_effect_vars(&fun.ret, false, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_compact_type_effect_vars(&field.value, false, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_compact_type_effect_vars(&field.value, false, out);
        }
        collect_compact_type_effect_vars(&spread.tail, false, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_compact_type_effect_vars(payload, false, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_compact_type_effect_vars(item, false, out);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                collect_compact_bounds_effect_vars(arg, false, out);
            }
        }
        collect_compact_type_effect_vars(&row.tail, true, out);
    }
}

fn collect_compact_bounds_effect_vars(
    bounds: &CompactBounds,
    in_effect_position: bool,
    out: &mut FxHashSet<TypeVar>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            collect_compact_type_effect_vars(lower, in_effect_position, out);
            collect_compact_type_effect_vars(upper, in_effect_position, out);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                collect_compact_bounds_effect_vars(arg, false, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_compact_bounds_effect_vars(arg, false, out);
            collect_compact_bounds_effect_vars(arg_eff, true, out);
            collect_compact_bounds_effect_vars(ret_eff, true, out);
            collect_compact_bounds_effect_vars(ret, false, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_compact_bounds_effect_vars(&field.value, false, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_compact_bounds_effect_vars(payload, false, out);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                collect_compact_bounds_effect_vars(item, false, out);
            }
        }
    }
}

fn effect_representatives_reaching_environment(
    machine: &crate::constraints::ConstraintMachine,
    effect_vars: Vec<TypeVar>,
    environment: &FxHashSet<TypeVar>,
    boundary: TypeLevel,
) -> Vec<TypeVar> {
    let effect_set = effect_vars.iter().copied().collect::<FxHashSet<_>>();
    let mut representatives = Vec::new();
    let mut visited = FxHashSet::default();
    for seed in effect_vars {
        if visited.contains(&seed) {
            continue;
        }
        let mut pending = vec![seed];
        let mut component_effects = Vec::new();
        let mut reaches_environment = false;
        while let Some(var) = pending.pop() {
            if !visited.insert(var) {
                continue;
            }
            if environment.contains(&var) {
                reaches_environment = true;
            }
            if effect_set.contains(&var) {
                component_effects.push(var);
            }
            for neighbor in machine.var_neighbors(var) {
                if !environment.contains(&neighbor) && machine.birth_level_of(neighbor) <= boundary
                {
                    continue;
                }
                if !visited.contains(&neighbor) {
                    pending.push(neighbor);
                }
            }
        }
        if reaches_environment
            && let Some(representative) = component_effects.into_iter().min_by_key(|var| var.0)
        {
            representatives.push(representative);
        }
    }
    representatives
}
