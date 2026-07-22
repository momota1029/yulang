//! Extracted expression lowering methods.

use super::super::*;
use super::*;
use crate::token_source_range;

impl<'a> ExprLowerer<'a> {
    pub(in crate::lowering) fn lower_tail_node(
        &mut self,
        acc: Computation,
        node: &Cst,
        callee_source_range: TextRange,
    ) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::ApplyML | SyntaxKind::ApplyC | SyntaxKind::ApplyColon => {
                self.apply_arguments(acc, node, callee_source_range)
            }
            SyntaxKind::Field => self.lower_field_selection(acc, node),
            SyntaxKind::ProjectionTuple => self.lower_projection_tuple_tail(acc, node),
            SyntaxKind::ProjectionRecord => self.lower_projection_record_tail(acc, node),
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
                source_range: Some(crate::node_source_range(node)),
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
            .map_err(|error| LoweringError::annotation_build(error, &type_expr))?;
        let acc = self.apply_effect_annotation_upcasts(acc, &ann);
        let connection = AnnConstraintLowerer::new(&mut self.session.infer, self.modules)
            .connect_computation_detailed(
                AnnComputationTarget {
                    value: acc.value,
                    effect: acc.effect,
                },
                &ann,
            )
            .map_err(|error| LoweringError::AnnotationConstraint { error })?;
        self.extend_current_predicate_connection(connection);
        Ok(acc)
    }

    pub(in crate::lowering) fn apply_arguments(
        &mut self,
        mut callee: Computation,
        node: &Cst,
        mut callee_source_range: TextRange,
    ) -> Result<Computation, LoweringError> {
        let args = self.apply_argument_exprs(callee, node);
        if args.is_empty() {
            let unit = self.unit_expr();
            let application_source_range = callee_source_range.cover(node.text_range());
            return Ok(self.make_source_app(
                callee,
                unit,
                application_source_range,
                callee_source_range,
                None,
            ));
        }
        let arg_count = args.len();
        for (index, arg) in args.into_iter().enumerate() {
            let argument_boundary_source_range = arg.text_range();
            let argument_source_range = if index + 1 == arg_count {
                node.text_range()
            } else {
                argument_boundary_source_range
            };
            let application_source_range = callee_source_range.cover(argument_source_range);
            let lowered_arg = self.lower_expr(&arg)?;
            callee = self.make_source_app(
                callee,
                lowered_arg,
                application_source_range,
                callee_source_range,
                Some(argument_boundary_source_range),
            );
            callee_source_range = application_source_range;
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
        let source_range = field_source_range(node);
        if name == "return"
            && let Some(target) = self.sub_label_return_target(receiver.expr).cloned()
        {
            return Ok(self.lower_sub_return_target(&target));
        }
        Ok(self.lower_synthetic_selection_at(receiver, name, source_range))
    }

    pub(in crate::lowering) fn lower_index_selection(
        &mut self,
        receiver: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let arg_node = index_expr(node).ok_or_else(|| LoweringError::MissingIndexArgument {
            source_range: index_source_range(node),
        })?;
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
        self.subtype_var_to_var_with_origin(
            value.effect,
            result_effect,
            crate::constraints::OriginId::internal(),
        );
        self.subtype_var_to_var_with_origin(
            ref_effect,
            result_effect,
            crate::constraints::OriginId::internal(),
        );
        self.subtype_var_to_var(value.value, expected_value);

        let effect_arg = self.invariant_var_arg(ref_effect);
        let value_arg = self.invariant_var_arg(expected_value);
        let args = vec![effect_arg, value_arg];
        let reference_type = self.alloc_pos(Pos::Con(
            crate::std_paths::control_var_ref_type(),
            args.clone(),
        ));
        let reference_upper = self.alloc_neg(Neg::Var(reference.value));
        self.session.infer.subtype(
            reference_type,
            reference_upper,
            crate::constraints::OriginId::internal(),
        );
        let reference_lower = self.alloc_pos(Pos::Var(reference.value));
        let reference_type =
            self.alloc_neg(Neg::Con(crate::std_paths::control_var_ref_type(), args));
        self.session.infer.subtype(
            reference_lower,
            reference_type,
            crate::constraints::OriginId::internal(),
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
        self.lower_synthetic_selection_at_with_origin(
            receiver,
            name,
            None,
            crate::constraints::OriginId::internal(),
        )
    }

    pub(in crate::lowering) fn lower_internal_synthetic_selection(
        &mut self,
        receiver: Computation,
        name: String,
    ) -> Computation {
        self.lower_synthetic_selection_at_with_origin(
            receiver,
            name,
            None,
            crate::constraints::OriginId::internal(),
        )
    }

    pub(in crate::lowering) fn lower_synthetic_selection_at(
        &mut self,
        receiver: Computation,
        name: String,
        source_range: Option<SourceRange>,
    ) -> Computation {
        self.lower_synthetic_selection_at_with_origin(
            receiver,
            name,
            source_range,
            crate::constraints::OriginId::internal(),
        )
    }

    fn lower_synthetic_selection_at_with_origin(
        &mut self,
        receiver: Computation,
        name: String,
        source_range: Option<SourceRange>,
        origin: crate::constraints::OriginId,
    ) -> Computation {
        let method_value = self.fresh_type_var();
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let call_effect = self.fresh_type_var();
        let method = self.alloc_pos(Pos::Var(method_value));
        let receiver_value = self.alloc_pos(Pos::Var(receiver.value));
        let receiver_arg_eff = self.alloc_pos(Pos::Var(receiver.effect));
        let ret_eff = self.alloc_neg(Neg::Var(call_effect));
        let ret = self.alloc_neg(Neg::Var(result_value));
        let method_upper = self.alloc_neg(Neg::Fun {
            arg: receiver_value,
            arg_eff: receiver_arg_eff,
            ret_eff,
            ret,
        });
        self.session.infer.subtype(method, method_upper, origin);
        self.subtype_var_to_var(call_effect, result_effect);

        let select = self.session.poly.add_select(name);
        self.session.register_selection_use(
            select,
            SelectionUse {
                parent: self.parent,
                method_value,
                selected_value: result_value,
                receiver_value: receiver.value,
                receiver_effect: receiver.effect,
                local_method_scope: self.local_method_scope,
                recursive_self_value: self.recursive_self_value,
            },
        );
        if let Some(source_span) = self.source_span(source_range) {
            self.session
                .selections
                .insert_source_span(select, source_span);
        }
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
            .map(|tok| (tok.text().to_string(), token_source_range(&tok)))
            .ok_or(LoweringError::MissingOpName)?;
        self.resolve_op_symbol_at(fixity, &symbol.0, Some(symbol.1))
    }

    pub(in crate::lowering) fn resolve_op_symbol_at(
        &mut self,
        fixity: &'static str,
        symbol: &str,
        source_range: Option<SourceRange>,
    ) -> Result<(Computation, bool), LoweringError> {
        let name = crate::op_value_name(fixity, symbol);
        let Some(target) = self.modules.lexical_value_at(self.module, &name, self.site) else {
            return Err(LoweringError::UnresolvedName { name, source_range });
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
                source_span: self.source_span(source_range),
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

    pub(in crate::lowering) fn lower_nullfix_op_use_at(
        &mut self,
        symbol: &str,
        source_range: Option<SourceRange>,
    ) -> Result<Computation, LoweringError> {
        let (op, _lazy) = self.resolve_op_symbol_at("nullfix", symbol, source_range)?;
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

    /// Build an application without assigning source ownership.
    ///
    /// Desugaring helpers use this entrypoint deliberately. Surface application syntax must go
    /// through `make_source_app` while its CST ranges are still in hand.
    pub(in crate::lowering) fn make_app(
        &mut self,
        callee: Computation,
        arg: Computation,
    ) -> Computation {
        self.make_app_with_origin(callee, arg, crate::constraints::OriginId::internal())
    }

    pub(in crate::lowering) fn make_internal_app(
        &mut self,
        callee: Computation,
        arg: Computation,
    ) -> Computation {
        self.make_app_with_origin(callee, arg, crate::constraints::OriginId::internal())
    }

    fn make_app_with_origin(
        &mut self,
        callee: Computation,
        arg: Computation,
        origin: crate::constraints::OriginId,
    ) -> Computation {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let call_effect = self.fresh_type_var();

        let arg_value = self.alloc_pos(Pos::Var(arg.value));
        let arg_effect = self.alloc_pos(Pos::Var(arg.effect));
        let (local_callee_def, local_callee_predicate, local_callee_erased_upper) =
            self.local_callee_call_projection(&callee);
        self.extend_current_latent_predicate(&local_callee_predicate);
        let return_effect = self.unannotated_local_callee_return_effect(&callee, call_effect);
        let return_value = self.alloc_neg(Neg::Var(result_value));
        let callee_upper = self.alloc_neg(Neg::Fun {
            arg: arg_value,
            arg_eff: arg_effect,
            ret_eff: return_effect.upper,
            ret: return_value,
        });
        self.subtype(Pos::Var(callee.value), callee_upper, origin);
        if let Some(erased_upper) = local_callee_erased_upper {
            if let Some(def) = local_callee_def {
                let frame_index = self.function_frames.len().checked_sub(1);
                self.record_local_call_upper(def, callee_upper, frame_index);
            }
            let callee_lower = self.alloc_pos(Pos::Var(callee.value));
            self.session.infer.subtype(
                callee_lower,
                erased_upper,
                crate::constraints::OriginId::unknown_internal(),
            );
        }
        self.subtype_var_to_var_with_origin(
            callee.effect,
            result_effect,
            crate::constraints::OriginId::internal(),
        );
        self.subtype_pos_to_var_with_origin(
            return_effect.lower,
            result_effect,
            crate::constraints::OriginId::internal(),
        );

        let expr = self.session.poly.add_expr(Expr::App(callee.expr, arg.expr));
        Computation::computation(expr, result_value, result_effect)
    }

    fn make_source_app(
        &mut self,
        callee: Computation,
        arg: Computation,
        application_source_range: TextRange,
        callee_source_range: TextRange,
        argument_source_range: Option<TextRange>,
    ) -> Computation {
        let source_boundary = self
            .session
            .infer
            .alloc_source_boundary(crate::constraints::ConstraintOriginKind::ApplicationArgument);
        let application = self.make_app_with_origin(callee, arg, source_boundary.origin());
        let application_span = self.source_span(Some(crate::source_range_from_text_range(
            application_source_range,
        )));
        let callee_span = self.source_span(Some(crate::source_range_from_text_range(
            callee_source_range,
        )));
        let argument_span = argument_source_range
            .and_then(|range| self.source_span(Some(crate::source_range_from_text_range(range))));
        if let (Some(application_span), Some(callee_span)) =
            (application_span.clone(), callee_span.clone())
        {
            let previous = self.session.application_provenance.insert(
                application.expr,
                ApplicationProvenance {
                    origin: ApplicationOrigin::Source,
                    module: self.module,
                    application_span,
                    callee_span,
                },
            );
            debug_assert!(
                previous.is_none(),
                "each arena-local application is assigned source provenance at most once"
            );
        }
        if let (Some(application_span), Some(callee_span), Some(argument_span)) =
            (application_span, callee_span, argument_span)
        {
            let inserted = self
                .session
                .source_boundary_provenance
                .insert_application_argument(
                    source_boundary.boundary(),
                    ApplicationArgumentBoundaryProvenance {
                        application_span,
                        callee_span,
                        argument_span,
                    },
                );
            debug_assert!(
                inserted,
                "each source boundary is assigned source provenance at most once"
            );
        }
        application
    }

    fn local_callee_call_projection(
        &self,
        callee: &Computation,
    ) -> (Option<DefId>, Vec<StackWeight>, Option<NegId>) {
        let Some(def) = self.local_callee_def(callee) else {
            return (None, Vec::new(), None);
        };
        let Some(local) = self.local_binding_by_def(def) else {
            return (Some(def), Vec::new(), None);
        };
        (
            Some(def),
            local.call_predicate_subtracts.clone(),
            local.call_erased_upper,
        )
    }

    fn record_local_call_upper(&mut self, def: DefId, upper: NegId, frame_index: Option<usize>) {
        if let Some(local) = self.locals.iter_mut().rev().find(|local| local.def == def) {
            local.call_erased_used = true;
            if frame_index.is_some() && frame_index != local.call_predicate_frame {
                local.call_nested = true;
            }
            if !local.call_uppers.contains(&upper) {
                local.call_uppers.push(upper);
            }
        }
    }

    fn extend_current_latent_predicate(&mut self, subtracts: &[StackWeight]) {
        if subtracts.is_empty() {
            return;
        }
        if let Some(frame) = self.function_frames.last_mut() {
            frame.latent_subtracts.extend(subtracts.iter().cloned());
        }
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
        let subtract = match self.function_frames[frame_index]
            .unannotated_call_subtracts
            .get(&def)
            .copied()
        {
            Some(subtract) => subtract,
            None => {
                let subtract = self.session.infer.fresh_subtract_id();
                self.session.infer.declared_subtract_fact(
                    call_effect,
                    subtract,
                    Subtractability::Empty,
                );
                let frame = &mut self.function_frames[frame_index];
                frame.unannotated_call_subtracts.insert(def, subtract);
                frame.subtracts.push(StackWeight::pop(subtract));
                subtract
            }
        };
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
        let introduced_frame_index = local.unannotated_call_frame?;
        let direct_defined_call = self
            .function_frames
            .last()
            .is_some_and(|frame| frame.scope == LambdaScope::Defined);
        if direct_defined_call {
            let current_frame_index = self
                .function_frames
                .iter()
                .rposition(|frame| frame.scope == LambdaScope::Defined)?;
            let crosses_inner_active_skeleton =
                self.active_defined_skeletons.iter().any(|active| {
                    introduced_frame_index < active.before_frames
                        && current_frame_index >= active.before_frames
                        && current_frame_index < active.before_frames + active.params.len()
                });
            if crosses_inner_active_skeleton {
                return Some(introduced_frame_index);
            }
            return Some(current_frame_index);
        }
        if !self.sub_syntax_scopes.is_empty() {
            return Some(introduced_frame_index);
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
        self.session
            .infer
            .subtype(predicate, upper, crate::constraints::OriginId::internal());
        value
    }

    pub(in crate::lowering) fn generalize_local_binding(
        &mut self,
        def: DefId,
        value: TypeVar,
        boundary: TypeLevel,
        fetch: BindingFetch,
    ) {
        // Local schemes are used immediately by later statements in the same block, so they must
        // see the closure of method selections and subtype constraints emitted while lowering the
        // RHS.
        self.session.drain_selection_work_for_parent(self.parent);
        self.session.infer.constraints_mut().drain();
        if self
            .session
            .selections
            .iter()
            .any(|(_, use_site)| use_site.parent == self.parent && use_site.selected_value == value)
        {
            // A local scheme is a snapshot. If method selections owned by this definition are
            // still producing this value, later statements must keep sharing the live slot instead
            // of reading a generalized copy that lacks the method result constraints.
            if let Some(local) = self.locals.iter_mut().rev().find(|local| local.def == def) {
                local.scheme = None;
            }
            return;
        }
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
        let (witnesses, witness_completeness) = crate::generalize::capture_generalized_witnesses(
            self.session.infer.constraints(),
            value,
            &generalized,
        );
        let mut finalized = crate::generalize::finalize_generalized_compact_root(
            &mut self.session.poly.typ,
            self.session.infer.constraints(),
            &generalized,
        );
        let use_monomorphic_local = !forced_quantifiers.is_empty();
        add_forced_quantifiers(&mut finalized.scheme, forced_quantifiers);
        self.session
            .record_generalized_scheme(def, witnesses, witness_completeness);
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
        mut annotation: PredicateOutputConstraints,
        mut frame: FunctionPredicateFrame,
    ) -> PredicateOutputConstraints {
        if lambda_scope != LambdaScope::Defined {
            return PredicateOutputConstraints {
                subtracts: dedupe_predicate_weights(frame.latent_subtracts),
            };
        }
        annotation.subtracts.append(&mut frame.subtracts);
        annotation.subtracts.append(&mut frame.latent_subtracts);
        annotation.subtracts = dedupe_predicate_weights(annotation.subtracts);
        annotation
    }

    pub(in crate::lowering) fn extend_current_predicate_connection(
        &mut self,
        connection: AnnComputationConnection,
    ) {
        if let Some(frame) = self.function_frames.last_mut() {
            frame.subtracts.extend(connection.subtracts);
        }
    }

    pub(in crate::lowering) fn lambda_output_predicate(
        &mut self,
        body: &Computation,
        predicate: &PredicateOutputConstraints,
    ) -> (PosId, PosId) {
        self.lambda_output_predicate_vars(body.effect, body.value, predicate)
    }

    pub(in crate::lowering) fn lambda_output_predicate_vars(
        &mut self,
        body_effect: TypeVar,
        body_value: TypeVar,
        predicate: &PredicateOutputConstraints,
    ) -> (PosId, PosId) {
        if predicate.is_empty() {
            let ret_eff = self.alloc_pos(Pos::Var(body_effect));
            let ret = self.alloc_pos(Pos::Var(body_value));
            return (ret_eff, ret);
        }

        let ret_eff = self.alloc_pos(Pos::Var(body_effect));
        let ret = self.alloc_pos(Pos::Var(body_value));
        (
            self.wrap_pos_with_subtracts(ret_eff, &predicate.subtracts),
            self.wrap_pos_with_subtracts(ret, &predicate.subtracts),
        )
    }
}

pub(in crate::lowering) fn field_source_range(node: &Cst) -> Option<SourceRange> {
    let token = node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::DotField)?;
    let mut range = token_source_range(&token);
    if token.text().starts_with('.') {
        range.start = range.start.saturating_add(1);
    }
    Some(range)
}

fn index_source_range(node: &Cst) -> SourceRange {
    node.children()
        .find(|child| child.kind() == SyntaxKind::Bracket)
        .map(|bracket| crate::node_trimmed_source_range(&bracket))
        .unwrap_or_else(|| crate::node_trimmed_source_range(node))
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

fn dedupe_predicate_weights(weights: Vec<StackWeight>) -> Vec<StackWeight> {
    let mut out = Vec::new();
    for weight in weights {
        if !out.contains(&weight) {
            out.push(weight);
        }
    }
    out
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
