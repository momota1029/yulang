//! Extracted expression lowering methods.

use super::super::*;
use super::*;

impl<'a> ExprLowerer<'a> {
    pub(in crate::lowering) fn lower_paren(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let exprs = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::Expr)
            .collect::<Vec<_>>();
        match exprs.as_slice() {
            [] => Ok(self.unit_expr()),
            [expr] => self.lower_expr_with_lambda_scope(expr, lambda_scope),
            _ => {
                let item_lowers = exprs
                    .iter()
                    .map(|expr| self.lower_expr(expr))
                    .collect::<Result<Vec<_>, _>>()?;
                let items = item_lowers
                    .iter()
                    .map(|computation| computation.expr)
                    .collect::<Vec<_>>();
                let value = self.fresh_type_var();
                let expansive = item_lowers.iter().any(|item| item.is_expansive());
                let effect = if expansive {
                    self.fresh_type_var()
                } else {
                    self.fresh_exact_pure_effect()
                };
                let expr = self.session.poly.add_expr(Expr::Tuple(items));
                let item_values = item_lowers
                    .iter()
                    .map(|item| self.alloc_pos(Pos::Var(item.value)))
                    .collect::<Vec<_>>();
                for item in &item_lowers {
                    self.subtype_var_to_var(item.effect, effect);
                }
                self.constrain_lower(value, Pos::Tuple(item_values));
                Ok(Computation::new(
                    expr,
                    value,
                    effect,
                    if expansive {
                        Evaluation::Computation
                    } else {
                        Evaluation::Value
                    },
                ))
            }
        }
    }

    pub(in crate::lowering) fn lower_expr_block(
        &mut self,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let before_locals = self.locals.len();
        let items = block_lowering_items(node);
        let result = self.lower_block_items(items.as_slice());
        self.locals.truncate(before_locals);
        result
    }

    pub(in crate::lowering) fn lower_block_items(
        &mut self,
        items: &[Cst],
    ) -> Result<Computation, LoweringError> {
        let Some((head, rest)) = items.split_first() else {
            return Ok(self.unit_expr());
        };

        match head.kind() {
            SyntaxKind::Binding if local_var_binding_source(head).is_some() => {
                self.lower_local_var_binding(head, rest)
            }
            SyntaxKind::Binding => {
                let lowered = self.lower_local_binding_stmt(head)?;
                let tail = self.lower_block_items(rest)?;
                Ok(self.prepend_block(lowered, tail))
            }
            SyntaxKind::Expr => {
                let head = self.lower_expr(head)?;
                if rest.is_empty() {
                    Ok(head)
                } else {
                    let stmt = LoweredLocalStmt {
                        stmt: Stmt::Expr(head.expr),
                        effect: head.effect,
                    };
                    let tail = self.lower_block_items(rest)?;
                    Ok(self.prepend_block(stmt, tail))
                }
            }
            SyntaxKind::ForStmt => {
                let head = self.lower_for_stmt(head)?;
                if rest.is_empty() {
                    Ok(head)
                } else {
                    let stmt = LoweredLocalStmt {
                        stmt: Stmt::Expr(head.expr),
                        effect: head.effect,
                    };
                    let tail = self.lower_block_items(rest)?;
                    Ok(self.prepend_block(stmt, tail))
                }
            }
            kind => Err(LoweringError::UnsupportedSyntax { kind }),
        }
    }

    pub(in crate::lowering) fn lower_for_stmt(
        &mut self,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let label = for_label(node)
            .map(|label| {
                for_label_name(&label).ok_or(LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::ForLabel,
                })
            })
            .transpose()?;
        let has_label = label.is_some();
        let iter_node = for_iter_expr(node).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::ForHeader,
        })?;
        let body = for_body_expr(node).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::ForBody,
        })?;
        let pattern = for_pattern(node).ok_or(LoweringError::UnsupportedPatternSyntax {
            kind: SyntaxKind::ForHeader,
        })?;

        let iter = self.lower_expr(&iter_node)?;
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
            &self.type_name_aliases,
        );
        let mut ann_solver_vars = FxHashMap::default();
        let body = match label {
            Some(label) => self.lower_labeled_for_body(
                label,
                pattern,
                &body,
                &mut ann_builder,
                &mut ann_solver_vars,
            )?,
            None => self.lower_lambda_params(
                &[pattern],
                &body,
                LambdaScope::Anonymous,
                &mut ann_builder,
                &mut ann_solver_vars,
                None,
                None,
            )?,
        };
        let for_in = if has_label {
            self.lower_std_value_ref(crate::std_paths::control_flow_label_loop_for_in_value())?
        } else {
            self.lower_std_value_ref(crate::std_paths::control_flow_loop_for_in_value())?
        };
        let applied_iter = self.make_app(for_in, iter);
        Ok(self.make_app(applied_iter, body))
    }

    pub(in crate::lowering) fn lower_labeled_for_body(
        &mut self,
        label: Name,
        item_pattern: Cst,
        body: &Cst,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<Computation, LoweringError> {
        let label_value = self.fresh_type_var();
        let before_locals = self.locals.len();
        let pat =
            self.bind_pattern_local(label, label_value, None, LocalCallReturnEffect::Annotated);

        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Anonymous));
        let previous_level = self.session.infer.enter_child_level();
        let body_result = self.lower_lambda_params(
            &[item_pattern],
            body,
            LambdaScope::Anonymous,
            ann_builder,
            ann_solver_vars,
            None,
            None,
        );
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("labeled for lambda predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(label_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Anonymous, Vec::new(), frame);
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

    pub(in crate::lowering) fn lower_local_binding_stmt(
        &mut self,
        node: &Cst,
    ) -> Result<LoweredLocalStmt, LoweringError> {
        let arg_patterns = binding_arg_patterns(node);
        if arg_patterns.is_empty() && !crate::binding_has_single_head_pattern(node) {
            return self.lower_local_pattern_binding_stmt(node);
        }

        let name = crate::binding_name(node).ok_or(LoweringError::MissingLocalBindingName)?;
        let body = binding_body_expr(node).ok_or(LoweringError::MissingLocalBindingBody)?;
        let boundary = self.local_generalize_boundary;
        let previous_level = self.session.infer.enter_child_level();
        let result = (|| {
            let value = self.fresh_type_var();
            let call_return_effect = local_binding_call_return_effect(node);
            let (pat, def) = self.bind_let_local_with_def(name, value, call_return_effect, None);
            let recursive_effect_passthrough = arg_patterns
                .iter()
                .any(|pattern| pattern_type_expr(pattern).is_none());
            if let Some(local) = self.locals.iter_mut().rev().find(|local| local.def == def) {
                local.recursive_effect_passthrough = recursive_effect_passthrough;
            }
            let body = self.lower_local_binding_body(node, &body, Some(value))?;
            self.subtype_var_to_var(body.value, value);
            self.connect_local_binding_annotation(node, value, body)?;
            self.set_local_let_body(def, body.expr);
            self.generalize_local_binding(
                def,
                value,
                boundary,
                BindingFetch::from_evaluation(body.evaluation),
            );

            Ok(LoweredLocalStmt {
                stmt: Stmt::Let(Vis::My, pat, body.expr),
                effect: body.effect,
            })
        })();
        self.session.infer.restore_level(previous_level);
        result
    }

    pub(in crate::lowering) fn lower_local_pattern_binding_stmt(
        &mut self,
        node: &Cst,
    ) -> Result<LoweredLocalStmt, LoweringError> {
        let pattern = crate::binding_pattern(node).ok_or(LoweringError::MissingLocalBindingName)?;
        let body_node = binding_body_expr(node).ok_or(LoweringError::MissingLocalBindingBody)?;
        let previous_level = self.session.infer.enter_child_level();
        let result = (|| {
            let body = self.lower_expr(&body_node)?;
            let value = self.fresh_type_var();
            let pat = self.lower_lambda_pattern(
                &pattern,
                value,
                None,
                local_binding_call_return_effect(node),
            )?;
            self.subtype_var_to_var(body.value, value);
            self.subtype_var_to_var(value, body.value);
            self.connect_local_binding_annotation(node, value, body)?;
            Ok(LoweredLocalStmt {
                stmt: Stmt::Let(Vis::My, pat, body.expr),
                effect: body.effect,
            })
        })();
        self.session.infer.restore_level(previous_level);
        result
    }

    pub(in crate::lowering) fn lower_local_var_binding(
        &mut self,
        node: &Cst,
        rest: &[Cst],
    ) -> Result<Computation, LoweringError> {
        let source =
            local_var_binding_source(node).ok_or(LoweringError::MissingLocalBindingName)?;
        let init_name = var_init_name(&source).ok_or(LoweringError::MissingLocalBindingName)?;
        let reference_name =
            var_reference_name(&source).ok_or(LoweringError::MissingLocalBindingName)?;
        let local_act = self.next_synthetic_var_act(&reference_name)?;
        let body = binding_body_expr(node).ok_or(LoweringError::MissingLocalBindingBody)?;
        let boundary = self.local_generalize_boundary;
        let init_value = self.fresh_type_var();
        let init = self.lower_local_binding_body(node, &body, None)?;
        self.subtype_var_to_var(init.value, init_value);
        self.subtype_var_to_var(init_value, init.value);

        let (init_pat, init_def) = self.bind_let_local_with_def(
            init_name.clone(),
            init_value,
            LocalCallReturnEffect::Annotated,
            Some(init.expr),
        );
        self.generalize_local_binding(
            init_def,
            init_value,
            boundary,
            BindingFetch::from_evaluation(init.evaluation),
        );
        let init_stmt = LoweredLocalStmt {
            stmt: Stmt::Let(Vis::My, init_pat, init.expr),
            effect: init.effect,
        };

        let reference = self.lower_var_ref_constructor(&local_act, init_value)?;
        let reference_value = self.fresh_type_var();
        self.subtype_var_to_var(reference.value, reference_value);
        self.subtype_var_to_var(reference_value, reference.value);
        self.constrain_local_ref_value(&local_act, reference_value, init_value)?;
        let (reference_pat, reference_def) = self.bind_let_local_with_def(
            reference_name.clone(),
            reference_value,
            LocalCallReturnEffect::Annotated,
            Some(reference.expr),
        );
        self.generalize_local_binding(
            reference_def,
            reference_value,
            boundary,
            BindingFetch::FetchComputation,
        );
        let reference_stmt = LoweredLocalStmt {
            stmt: Stmt::Let(Vis::My, reference_pat, reference.expr),
            effect: reference.effect,
        };

        let tail = self.lower_block_items(rest)?;
        let wrapped = self.wrap_var_binding_run(&local_act, init_name, init_value, tail)?;
        let with_reference = self.prepend_block(reference_stmt, wrapped);
        Ok(self.prepend_block(init_stmt, with_reference))
    }

    pub(in crate::lowering) fn next_synthetic_var_act(
        &mut self,
        reference_name: &Name,
    ) -> Result<SyntheticVarActUse, LoweringError> {
        let Some(next) = self
            .synthetic_var_acts
            .get(self.synthetic_var_act_cursor)
            .cloned()
        else {
            return Err(LoweringError::MissingLocalVarAct {
                name: reference_name.clone(),
            });
        };
        if next.source != *reference_name {
            return Err(LoweringError::MissingLocalVarAct {
                name: reference_name.clone(),
            });
        }
        self.synthetic_var_act_cursor += 1;
        Ok(next)
    }

    pub(in crate::lowering) fn lower_local_binding_body(
        &mut self,
        binding: &Cst,
        body: &Cst,
        self_value: Option<TypeVar>,
    ) -> Result<Computation, LoweringError> {
        let arg_patterns = binding_arg_patterns(binding);
        if arg_patterns.is_empty() {
            return self.lower_expr(body);
        }
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
            &self.type_name_aliases,
        );
        let mut ann_solver_vars = FxHashMap::default();
        let result_type_expr = binding_type_expr(binding);
        self.lower_lambda_params(
            arg_patterns.as_slice(),
            body,
            LambdaScope::Defined,
            &mut ann_builder,
            &mut ann_solver_vars,
            result_type_expr.as_ref(),
            self_value,
        )
    }

    pub(in crate::lowering) fn connect_local_binding_annotation(
        &mut self,
        node: &Cst,
        value: TypeVar,
        computation: Computation,
    ) -> Result<(), LoweringError> {
        let Some(type_expr) = binding_type_expr(node) else {
            return Ok(());
        };
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
                    value,
                    effect: computation.effect,
                },
                &ann,
            )
            .map(|_| ())
            .map_err(|error| LoweringError::AnnotationConstraint { error })
    }

    pub(in crate::lowering) fn lower_var_ref_constructor(
        &mut self,
        act: &SyntheticVarActUse,
        payload: TypeVar,
    ) -> Result<Computation, LoweringError> {
        let var_ref = self.lower_var_act_member(act, "var_ref")?;
        let unit = self.unit_expr();
        let reference = self.make_app(var_ref, unit);
        self.constrain_local_ref_value(act, reference.value, payload)?;
        Ok(reference)
    }

    pub(in crate::lowering) fn wrap_var_binding_run(
        &mut self,
        act: &SyntheticVarActUse,
        init_name: Name,
        init_value: TypeVar,
        body: Computation,
    ) -> Result<Computation, LoweringError> {
        let run = self.lower_var_act_member(act, "run")?;
        let init = self.lower_name(init_name)?;
        self.subtype_var_to_var(init.value, init_value);
        self.subtype_var_to_var(init_value, init.value);
        let run_with_init = self.make_app(run, init);
        Ok(self.make_app(run_with_init, body))
    }

    pub(in crate::lowering) fn lower_var_act_member(
        &mut self,
        act: &SyntheticVarActUse,
        member: &str,
    ) -> Result<Computation, LoweringError> {
        let member_name = Name(member.to_string());
        let target = self
            .modules
            .type_companion(act.act)
            .and_then(|companion| {
                self.modules
                    .value_decls(companion, &member_name)
                    .first()
                    .map(|decl| decl.def)
            })
            .ok_or_else(|| LoweringError::UnresolvedName {
                name: Name(format!("{}::{member}", act.source.0)),
            })?;
        Ok(self.lower_resolved_value_ref(format!("{}::{member}", act.source.0), target))
    }

    pub(in crate::lowering) fn lower_resolved_value_ref(
        &mut self,
        label: String,
        target: DefId,
    ) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let reference = self.session.poly.add_ref();
        if let Some(labels) = self.labels.as_mut() {
            labels.set_ref_label(reference, label);
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
        Computation::value(expr, value, effect)
    }

    pub(in crate::lowering) fn constrain_local_ref_value(
        &mut self,
        act: &SyntheticVarActUse,
        reference: TypeVar,
        payload: TypeVar,
    ) -> Result<(), LoweringError> {
        let effect = self.local_var_effect_value(act, payload)?;
        let effect_arg = self.invariant_var_arg(effect);
        let payload_arg = self.invariant_var_arg(payload);
        let args = vec![effect_arg, payload_arg];
        self.constrain_lower(
            reference,
            Pos::Con(crate::std_paths::control_var_ref_type(), args.clone()),
        );
        self.constrain_upper(
            reference,
            Neg::Con(crate::std_paths::control_var_ref_type(), args),
        );
        Ok(())
    }

    pub(in crate::lowering) fn local_var_effect_value(
        &mut self,
        act: &SyntheticVarActUse,
        payload: TypeVar,
    ) -> Result<TypeVar, LoweringError> {
        let effect = self.fresh_type_var();
        let path = self.local_var_act_effect_path(act)?;
        let payload_arg = self.invariant_var_arg(payload);
        let lower_item = self.alloc_pos(Pos::Con(path.clone(), vec![payload_arg]));
        self.constrain_lower(effect, Pos::Row(vec![lower_item]));
        let upper_item = self.alloc_neg(Neg::Con(path, vec![payload_arg]));
        let upper_tail = self.alloc_neg(Neg::Bot);
        self.constrain_upper(effect, Neg::Row(vec![upper_item], upper_tail));
        Ok(effect)
    }

    pub(in crate::lowering) fn local_var_act_effect_path(
        &self,
        act: &SyntheticVarActUse,
    ) -> Result<Vec<String>, LoweringError> {
        let decl = self.modules.type_decl_by_id(act.act).ok_or_else(|| {
            LoweringError::MissingLocalVarAct {
                name: act.source.clone(),
            }
        })?;
        Ok(self
            .modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect())
    }

    pub(in crate::lowering) fn bind_let_local_with_def(
        &mut self,
        name: Name,
        value: TypeVar,
        call_return_effect: LocalCallReturnEffect,
        body: Option<poly::expr::ExprId>,
    ) -> (PatId, DefId) {
        let def = self.session.poly.defs.fresh();
        self.session.poly.defs.set(
            def,
            Def::Let {
                vis: Vis::My,
                scheme: None,
                body,
                children: Vec::new(),
            },
        );
        if let Some(labels) = self.labels.as_mut() {
            labels.set_def_label(def, name.0.clone());
        }
        self.locals.push(LocalBinding {
            name,
            def,
            value,
            effect: None,
            call_return_effect,
            unannotated_call_frame: None,
            recursive_effect_passthrough: false,
            scheme: None,
        });
        (self.session.poly.add_pat(Pat::Var(def)), def)
    }

    pub(in crate::lowering) fn set_local_let_body(
        &mut self,
        def: DefId,
        body_expr: poly::expr::ExprId,
    ) {
        let Some(Def::Let { body, .. }) = self.session.poly.defs.get_mut(def) else {
            unreachable!("local binding def should be a let");
        };
        *body = Some(body_expr);
    }

    pub(in crate::lowering) fn set_local_let_scheme(&mut self, def: DefId, new_scheme: Scheme) {
        let Some(Def::Let { scheme, .. }) = self.session.poly.defs.get_mut(def) else {
            unreachable!("local binding def should be a let");
        };
        *scheme = Some(new_scheme);
    }

    pub(in crate::lowering) fn prepend_block(
        &mut self,
        head: LoweredLocalStmt,
        tail: Computation,
    ) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_type_var();
        self.subtype_var_to_var(head.effect, effect);
        self.subtype_var_to_var(tail.effect, effect);
        self.subtype_var_to_var(tail.value, value);
        let expr = self
            .session
            .poly
            .add_expr(Expr::Block(vec![head.stmt], Some(tail.expr)));
        Computation::computation(expr, value, effect)
    }

    pub(in crate::lowering) fn lower_number(
        &mut self,
        text: &str,
    ) -> Result<Computation, LoweringError> {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let (lit, primitive) = parse_number_lit(text)?;

        self.constrain_lower(value, primitive_type(primitive));
        self.constrain_upper(value, primitive_neg_type(primitive));
        let expr = self.session.poly.add_expr(Expr::Lit(lit));
        Ok(Computation::value(expr, value, effect))
    }

    pub(in crate::lowering) fn lower_yada_yada_expr(&mut self) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(value, Pos::Bot);
        self.constrain_upper(value, Neg::Bot);
        let expr = self
            .session
            .poly
            .add_expr(Expr::PrimitiveOp(PrimitiveOp::YadaYada));
        Computation::value(expr, value, effect)
    }

    pub(in crate::lowering) fn lower_bool(&mut self, value: bool) -> Computation {
        let slot = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(slot, primitive_type("bool"));
        let expr = self.session.poly.add_expr(Expr::Lit(Lit::Bool(value)));
        Computation::value(expr, slot, effect)
    }

    pub(in crate::lowering) fn string_value(&mut self, text: String) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(
            value,
            Pos::Con(crate::std_paths::text_str_type(), Vec::new()),
        );
        self.constrain_upper(
            value,
            Neg::Con(crate::std_paths::text_str_type(), Vec::new()),
        );
        let expr = self.session.poly.add_expr(Expr::Lit(Lit::Str(text)));
        Computation::value(expr, value, effect)
    }

    pub(in crate::lowering) fn int_value(&mut self, number: i64) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(value, primitive_type("int"));
        self.constrain_upper(value, primitive_neg_type("int"));
        let expr = self.session.poly.add_expr(Expr::Lit(Lit::Int(number)));
        Computation::value(expr, value, effect)
    }
}
