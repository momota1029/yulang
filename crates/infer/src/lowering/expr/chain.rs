//! Extracted expression lowering methods.

use super::super::*;
use super::*;
use crate::token_source_range;

impl<'a> ExprLowerer<'a> {
    pub(in crate::lowering) fn lower_expr_with_lambda_scope(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::Expr => self.lower_expr_chain(node, lambda_scope),
            _ => self.lower_atom_with_lambda_scope(node, lambda_scope),
        }
    }

    pub(in crate::lowering) fn lower_expr_chain(
        &mut self,
        node: &Cst,
        head_lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        if let Some(with_block) = node
            .children()
            .find(|child| child.kind() == SyntaxKind::WithBlock)
        {
            return self.lower_with_expr_chain(node, &with_block, head_lambda_scope, None);
        }
        self.lower_expr_chain_prefix(node, head_lambda_scope, false)
    }

    pub(in crate::lowering) fn lower_expr_chain_prefix(
        &mut self,
        node: &Cst,
        head_lambda_scope: LambdaScope,
        stop_at_with: bool,
    ) -> Result<Computation, LoweringError> {
        self.lower_expr_chain_prefix_with_pipe_arg(node, head_lambda_scope, stop_at_with, None)
    }

    pub(in crate::lowering) fn lower_expr_chain_prefix_with_pipe_arg(
        &mut self,
        node: &Cst,
        head_lambda_scope: LambdaScope,
        stop_at_with: bool,
        pipe_arg: Option<PipeArg>,
    ) -> Result<Computation, LoweringError> {
        self.lower_expr_chain_prefix_with_pipe_arg_until(
            node,
            head_lambda_scope,
            stop_at_with,
            pipe_arg,
            None,
        )
    }

    pub(in crate::lowering) fn lower_expr_chain_prefix_with_pipe_arg_until(
        &mut self,
        node: &Cst,
        head_lambda_scope: LambdaScope,
        stop_at_with: bool,
        pipe_arg: Option<PipeArg>,
        stop_kind: Option<SyntaxKind>,
    ) -> Result<Computation, LoweringError> {
        let items = node
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .collect::<Vec<_>>();
        let Some(head) = items.first() else {
            return Ok(self.unit_expr());
        };

        if let Some(parts) = crate::sub_syntax_parts(node) {
            let mut lowered = self.lower_sub_syntax(parts)?;
            if let Some(pipe_arg) = pipe_arg {
                lowered = self.make_app(lowered, pipe_arg.expr);
            }
            return Ok(lowered);
        }

        if let Some(name) = expr_symbol_head_name(head) {
            return self.lower_poly_variant_expr_chain(
                name,
                &items,
                1,
                stop_at_with,
                pipe_arg,
                stop_kind,
            );
        }

        let (mut acc, tail_start) = match expr_path_prefix(&items) {
            Some((path, consumed)) if path.len() > 1 => (
                self.lower_path_name_at(&path, item_slice_source_range(&items[..consumed]))?,
                consumed,
            ),
            _ => (self.lower_head(head.clone(), head_lambda_scope)?, 1),
        };
        if let Some(pipe_arg) = pipe_arg {
            acc = self.make_app(acc, pipe_arg.expr);
        }
        let mut index = tail_start;
        while index < items.len() {
            match &items[index] {
                NodeOrToken::Node(child)
                    if should_stop_expr_tail(child.kind(), stop_at_with, stop_kind) =>
                {
                    break;
                }
                NodeOrToken::Node(child) if child.kind() == SyntaxKind::Field => {
                    let (name, path_tail_len) =
                        qualified_field_selection_name(child, &items[index + 1..])?;
                    acc = if path_tail_len == 0 {
                        self.lower_field_selection(acc, child)?
                    } else {
                        self.lower_synthetic_selection_at(
                            acc,
                            name,
                            super::tail::field_source_range(child),
                        )
                    };
                    index += 1 + path_tail_len;
                    continue;
                }
                NodeOrToken::Node(child) => acc = self.lower_tail_node(acc, child)?,
                NodeOrToken::Token(token) => {
                    return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
                }
            }
            index += 1;
        }
        Ok(acc)
    }

    pub(in crate::lowering) fn lower_poly_variant_expr_chain(
        &mut self,
        name: String,
        items: &[NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>],
        mut tail_start: usize,
        stop_at_with: bool,
        pipe_arg: Option<PipeArg>,
        stop_kind: Option<SyntaxKind>,
    ) -> Result<Computation, LoweringError> {
        let mut payloads = Vec::new();
        while let Some(NodeOrToken::Node(node)) = items.get(tail_start) {
            if !matches!(node.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC) {
                break;
            }
            let args = node
                .children()
                .filter(|child| child.kind() == SyntaxKind::Expr)
                .collect::<Vec<_>>();
            if args.is_empty() {
                payloads.push(self.unit_expr());
            } else {
                for arg in args {
                    payloads.push(self.lower_expr(&arg)?);
                }
            }
            tail_start += 1;
        }

        let result_value = self.fresh_type_var();
        let expansive = payloads.iter().any(|payload| payload.is_expansive());
        let result_effect = if expansive {
            self.fresh_type_var()
        } else {
            self.fresh_exact_pure_effect()
        };
        let mut pos_payloads = Vec::with_capacity(payloads.len());
        let mut neg_payloads = Vec::with_capacity(payloads.len());
        let mut expr_payloads = Vec::with_capacity(payloads.len());
        for payload in payloads {
            self.connect_effect_var_to_var(payload.effect, result_effect);
            pos_payloads.push(self.alloc_pos(Pos::Var(payload.value)));
            neg_payloads.push(self.alloc_neg(Neg::Var(payload.value)));
            expr_payloads.push(payload.expr);
        }
        self.constrain_lower(
            result_value,
            Pos::PolyVariant(vec![(name.clone(), pos_payloads)]),
        );
        self.constrain_upper(
            result_value,
            Neg::PolyVariant(vec![(name.clone(), neg_payloads)]),
        );
        let expr = self
            .session
            .poly
            .add_expr(Expr::PolyVariant(name, expr_payloads));
        let mut acc = Computation::new(
            expr,
            result_value,
            result_effect,
            if expansive {
                Evaluation::Computation
            } else {
                Evaluation::Value
            },
        );
        if let Some(pipe_arg) = pipe_arg {
            acc = self.make_app(acc, pipe_arg.expr);
        }

        for item in items.iter().skip(tail_start) {
            match item {
                NodeOrToken::Node(child)
                    if should_stop_expr_tail(child.kind(), stop_at_with, stop_kind) =>
                {
                    break;
                }
                NodeOrToken::Node(child) => acc = self.lower_tail_node(acc, child)?,
                NodeOrToken::Token(token) => {
                    return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
                }
            }
        }
        Ok(acc)
    }

    pub(in crate::lowering) fn lower_with_expr_chain(
        &mut self,
        node: &Cst,
        with_block: &Cst,
        head_lambda_scope: LambdaScope,
        pipe_arg: Option<PipeArg>,
    ) -> Result<Computation, LoweringError> {
        let items = with_block_lowering_items(with_block);
        let public_names = with_public_binding_names(&items);
        let before_locals = self.locals.len();
        let prefix = self.lower_block_items(items.as_slice())?;
        let public_locals = self.locals[before_locals..]
            .iter()
            .filter(|local| public_names.iter().any(|name| name == &local.name))
            .cloned()
            .collect::<Vec<_>>();
        self.locals.truncate(before_locals);
        self.locals.extend(public_locals);
        let tail =
            self.lower_expr_chain_prefix_with_pipe_arg(node, head_lambda_scope, true, pipe_arg);
        self.locals.truncate(before_locals);
        let tail = tail?;
        Ok(self.prepend_block(
            LoweredLocalStmt {
                stmt: Stmt::Expr(prefix.expr),
                effect: prefix.effect,
            },
            tail,
        ))
    }

    pub(in crate::lowering) fn lower_sub_syntax(
        &mut self,
        parts: crate::SubSyntaxParts,
    ) -> Result<Computation, LoweringError> {
        match parts.label {
            Some(label) => self.lower_labeled_sub_syntax(label, parts.body),
            None => self.lower_unlabeled_sub_syntax(parts.body),
        }
    }

    pub(in crate::lowering) fn lower_unlabeled_sub_syntax(
        &mut self,
        body_node: Cst,
    ) -> Result<Computation, LoweringError> {
        let sub = self.lower_std_value_ref(crate::std_paths::control_flow_sub_sub_value())?;
        let return_def = self.std_value_def(crate::std_paths::control_flow_sub_return_value())?;
        self.sub_syntax_scopes.push(SubSyntaxScope {
            bare_return: SubReturnTarget {
                label: "return".to_string(),
                def: return_def,
            },
            labels: Vec::new(),
        });
        let body = self.lower_expr(&body_node);
        self.sub_syntax_scopes.pop();
        let body = body?;
        let result = self.make_app(sub, body);
        self.constrain_unlabeled_sub_passthrough(body.effect, result.effect)?;
        Ok(result)
    }

    pub(in crate::lowering) fn lower_labeled_sub_syntax(
        &mut self,
        label: Name,
        body_node: Cst,
    ) -> Result<Computation, LoweringError> {
        let act = self.next_synthetic_sub_label_act(&label)?;
        let sub = self.lower_sub_label_act_member(&act, "sub")?;
        let control_label = self.lower_sub_label_act_member(&act, "control_label")?;
        let return_def = self.sub_label_act_member_def(&act, "return")?;

        let label_value = self.fresh_type_var();
        let before_locals = self.locals.len();
        let pat =
            self.bind_pattern_local(label, label_value, None, LocalCallReturnEffect::Annotated);
        let label_def = self
            .locals
            .last()
            .expect("sub label pattern should bind one local")
            .def;

        self.sub_syntax_scopes.push(SubSyntaxScope {
            bare_return: SubReturnTarget {
                label: "return".to_string(),
                def: return_def,
            },
            labels: vec![SubLabelReturnTarget {
                label_def,
                target: SubReturnTarget {
                    label: format!("{}::return", act.label.0),
                    def: return_def,
                },
            }],
        });
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Anonymous));
        let previous_level = self.session.infer.enter_child_level();
        let body_result = self.lower_expr(&body_node);
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("labeled sub lambda predicate frame should be balanced");
        self.sub_syntax_scopes.pop();
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
        let lambda = Computation::value(expr, value, effect);
        let arg = self.make_app(lambda, control_label);
        let result = self.make_app(sub, arg);
        self.constrain_labeled_sub_passthrough(&act, body.effect, result.effect)?;
        Ok(result)
    }

    pub(in crate::lowering) fn next_synthetic_sub_label_act(
        &mut self,
        label: &Name,
    ) -> Result<SyntheticSubLabelActUse, LoweringError> {
        let Some(next) = self
            .synthetic_sub_label_acts
            .get(self.synthetic_sub_label_act_cursor)
            .cloned()
        else {
            return Err(LoweringError::MissingSubLabelAct {
                label: label.clone(),
            });
        };
        if next.label != *label {
            return Err(LoweringError::MissingSubLabelAct {
                label: label.clone(),
            });
        }
        self.synthetic_sub_label_act_cursor += 1;
        Ok(next)
    }

    pub(in crate::lowering) fn lower_sub_label_act_member(
        &mut self,
        act: &SyntheticSubLabelActUse,
        member: &str,
    ) -> Result<Computation, LoweringError> {
        let target = self.sub_label_act_member_def(act, member)?;
        Ok(self.lower_resolved_value_ref(format!("{}::{member}", act.label.0), target))
    }

    pub(in crate::lowering) fn sub_label_act_member_def(
        &self,
        act: &SyntheticSubLabelActUse,
        member: &str,
    ) -> Result<DefId, LoweringError> {
        let member_name = Name(member.to_string());
        self.modules
            .type_companion(act.act)
            .and_then(|companion| {
                self.modules
                    .value_decls(companion, &member_name)
                    .first()
                    .map(|decl| decl.def)
            })
            .ok_or_else(|| LoweringError::UnresolvedName {
                name: Name(format!("{}::{member}", act.label.0)),
                source_range: None,
            })
    }

    pub(in crate::lowering) fn std_value_def(
        &self,
        path: Vec<String>,
    ) -> Result<DefId, LoweringError> {
        let path = path.into_iter().map(Name).collect::<Vec<_>>();
        self.modules
            .value_path_at(self.modules.root_id(), &path, module_path_lookup_site())
            .ok_or_else(|| LoweringError::UnresolvedName {
                name: Name(path_label(&path)),
                source_range: None,
            })
    }

    fn std_type_decl(&self, path: Vec<String>) -> Result<ModuleTypeDecl, LoweringError> {
        let path = path.into_iter().map(Name).collect::<Vec<_>>();
        self.modules
            .type_path_at(self.modules.root_id(), &path, module_path_lookup_site())
            .ok_or_else(|| LoweringError::UnresolvedName {
                name: Name(path_label(&path)),
                source_range: None,
            })
    }

    fn constrain_labeled_sub_passthrough(
        &mut self,
        act: &SyntheticSubLabelActUse,
        body_effect: TypeVar,
        result_effect: TypeVar,
    ) -> Result<(), LoweringError> {
        let label_decl =
            self.modules
                .type_decl_by_id(act.act)
                .ok_or_else(|| LoweringError::UnresolvedName {
                    name: Name(act.label.0.clone()),
                    source_range: None,
                })?;
        let label_path = self.type_decl_path_segments(&label_decl);
        let sub_path = self.std_sub_effect_path()?;
        self.constrain_sub_effect_passthrough(
            body_effect,
            result_effect,
            vec![label_path, sub_path],
        );
        Ok(())
    }

    fn constrain_unlabeled_sub_passthrough(
        &mut self,
        body_effect: TypeVar,
        result_effect: TypeVar,
    ) -> Result<(), LoweringError> {
        let sub_path = self.std_sub_effect_path()?;
        self.constrain_sub_effect_passthrough(body_effect, result_effect, vec![sub_path]);
        Ok(())
    }

    fn std_sub_effect_path(&self) -> Result<Vec<String>, LoweringError> {
        let sub_decl = self.std_type_decl(crate::std_paths::control_flow_sub_act())?;
        Ok(self.type_decl_path_segments(&sub_decl))
    }

    fn constrain_sub_effect_passthrough(
        &mut self,
        body_effect: TypeVar,
        result_effect: TypeVar,
        handled_paths: Vec<Vec<String>>,
    ) {
        let handled_payload = self.fresh_type_var();
        let result_arg = self.invariant_var_arg(handled_payload);
        let handled = handled_paths
            .into_iter()
            .map(|path| self.alloc_neg(Neg::Con(path, vec![result_arg])))
            .collect();
        let tail = self.alloc_neg(Neg::Var(result_effect));
        let upper = self.alloc_neg(Neg::Row(handled, tail));
        self.subtype(Pos::Var(body_effect), upper);
    }

    fn type_decl_path_segments(&self, decl: &ModuleTypeDecl) -> Vec<String> {
        self.modules
            .type_decl_path(decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect()
    }

    pub(in crate::lowering) fn lower_head(
        &mut self,
        head: NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        match head {
            NodeOrToken::Token(token) => match token.kind() {
                SyntaxKind::Ident => self.lower_name_at(
                    Name(token.text().to_string()),
                    Some(token_source_range(&token)),
                ),
                SyntaxKind::SigilIdent => {
                    self.lower_sigil_name_at(token.text(), Some(token_source_range(&token)))
                }
                SyntaxKind::Number => self.lower_number(token.text()),
                SyntaxKind::Do => Ok(self.do_replacement.unwrap_or_else(|| self.unit_expr())),
                SyntaxKind::YadaYada => Ok(self.lower_yada_yada_expr()),
                SyntaxKind::Nullfix => {
                    self.lower_nullfix_op_use_at(token.text(), Some(token_source_range(&token)))
                }
                _ => Err(LoweringError::UnsupportedSyntax { kind: token.kind() }),
            },
            NodeOrToken::Node(node) => self.lower_atom_with_lambda_scope(&node, lambda_scope),
        }
    }

    pub(in crate::lowering) fn lower_atom_with_lambda_scope(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::Expr => self.lower_expr_chain(node, lambda_scope),
            SyntaxKind::LambdaExpr => self.lower_lambda(node, lambda_scope),
            SyntaxKind::SubExpr => {
                let parts = crate::sub_syntax_parts(node)
                    .ok_or(LoweringError::UnsupportedSyntax { kind: node.kind() })?;
                self.lower_sub_syntax(parts)
            }
            SyntaxKind::SubLambdaExpr => self.lower_sub_lambda(node, lambda_scope),
            SyntaxKind::MethodLambdaExpr => self.lower_method_lambda(node, lambda_scope),
            SyntaxKind::RecursiveLambdaExpr => self.lower_recursive_lambda(node, lambda_scope),
            SyntaxKind::CaseLambdaExpr => self.lower_case_lambda(node, lambda_scope),
            SyntaxKind::CatchLambdaExpr => self.lower_catch_lambda(node, lambda_scope),
            SyntaxKind::IfExpr => self.lower_if(node),
            SyntaxKind::CaseExpr => self.lower_case(node, lambda_scope),
            SyntaxKind::CatchExpr => self.lower_catch(node, lambda_scope),
            SyntaxKind::Number => self.lower_number(&node.text().to_string()),
            SyntaxKind::YadaYada => Ok(self.lower_yada_yada_expr()),
            SyntaxKind::RuleLit => self.lower_rule_lit(node),
            SyntaxKind::RuleExpr => self.lower_rule_expr(node),
            SyntaxKind::StringLit => self.lower_string_lit(node),
            SyntaxKind::Paren => self.lower_paren(node, lambda_scope),
            SyntaxKind::Bracket => self.lower_list_literal(node),
            SyntaxKind::PrefixNode => self.lower_prefix_op_use(node),
            SyntaxKind::BraceGroup if brace_group_is_record_literal(node) => {
                self.lower_record_literal(node)
            }
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup => self.lower_expr_block(node),
            _ => Err(LoweringError::UnsupportedSyntax { kind: node.kind() }),
        }
    }
}

fn qualified_field_selection_name(
    field: &Cst,
    tail: &[CstItem],
) -> Result<(String, usize), LoweringError> {
    let mut path = vec![field_name(field).ok_or(LoweringError::MissingFieldName)?];
    let mut consumed = 0;
    for item in tail {
        let NodeOrToken::Node(path_sep) = item else {
            break;
        };
        if path_sep.kind() != SyntaxKind::PathSep {
            break;
        }
        let name = path_sep_name(path_sep).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::PathSep,
        })?;
        path.push(name.0);
        consumed += 1;
    }
    Ok((path.join("::"), consumed))
}
