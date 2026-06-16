//! Rule literal and rule expression lowering.
//!
//! This module owns the parser-combinator lowering path for rule literals and
//! `{ ... }` rule expressions. The parent expression lowerer still owns shared
//! expression helpers and type constraint primitives.

use super::*;

enum RuleLitPart {
    Token(String),
    Parser(Cst),
    CaptureWord(Name),
    CaptureParser { name: Name, parser: Cst },
}

struct RuleParserItem {
    parser: Computation,
    semantic: RuleSemantic,
}

struct RuleLowered {
    expr: Computation,
    semantic: RuleSemantic,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RuleSemantic {
    Unit,
    Record,
    Value,
}

impl<'a> ExprLowerer<'a> {
    /// Lower a rule literal into a thunked parser computation.
    pub(super) fn lower_rule_lit(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        if let Some(text) = plain_rule_lit_text(node) {
            return self.rule_token_parser(text);
        }

        let before_locals = self.locals.len();
        let result = (|| {
            let body = self.lower_rule_lit_sequence(rule_lit_parts(node)?)?;
            Ok(self.thunk_computation(body))
        })();
        self.locals.truncate(before_locals);
        result
    }

    /// Lower an explicit rule expression body into a thunked parser computation.
    pub(super) fn lower_rule_expr(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let before_locals = self.locals.len();
        let result = (|| {
            let body = self.rule_expr_body(node)?;
            Ok(self.thunk_computation(body.expr))
        })();
        self.locals.truncate(before_locals);
        result
    }

    fn lower_rule_lit_sequence(
        &mut self,
        parts: Vec<RuleLitPart>,
    ) -> Result<Computation, LoweringError> {
        let mut stmts = Vec::new();
        let mut fields = Vec::new();
        for part in parts {
            match part {
                RuleLitPart::Token(text) => {
                    if !text.is_empty() {
                        let parser = self.rule_token_parser(text)?;
                        let run = self.run_rule_parser(parser);
                        stmts.push(LoweredLocalStmt {
                            stmt: Stmt::Expr(run.expr),
                            effect: run.effect,
                        });
                    }
                }
                RuleLitPart::Parser(parser) => {
                    let parser = self.lower_rule_item(&parser)?.parser;
                    let run = self.run_rule_parser(parser);
                    stmts.push(LoweredLocalStmt {
                        stmt: Stmt::Expr(run.expr),
                        effect: run.effect,
                    });
                }
                RuleLitPart::CaptureWord(name) => {
                    let parser = self.rule_word_parser()?;
                    let run = self.run_rule_parser(parser);
                    let (stmt, captured) = self.bind_rule_capture(name.clone(), run);
                    stmts.push(stmt);
                    fields.push((name, captured));
                }
                RuleLitPart::CaptureParser { name, parser } => {
                    let parser = self.lower_expr(&parser)?;
                    let run = self.run_rule_parser(parser);
                    let (stmt, captured) = self.bind_rule_capture(name.clone(), run);
                    stmts.push(stmt);
                    fields.push((name, captured));
                }
            }
        }

        let tail = if fields.is_empty() {
            self.unit_expr()
        } else {
            self.rule_record_expr(fields)
        };
        Ok(self.rule_block_expr(stmts, tail))
    }

    fn rule_expr_body(&mut self, node: &Cst) -> Result<RuleLowered, LoweringError> {
        let group = node
            .children()
            .find(|child| child.kind() == SyntaxKind::BraceGroup)
            .ok_or(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::RuleExpr,
            })?;
        self.lower_rule_container_body(&group)
    }

    fn lower_rule_container_body(&mut self, node: &Cst) -> Result<RuleLowered, LoweringError> {
        let mut lowered = rule_branches(node)
            .into_iter()
            .map(|branch| self.lower_rule_sequence(branch))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter();
        let Some(first) = lowered.next() else {
            return Ok(RuleLowered {
                expr: self.unit_expr(),
                semantic: RuleSemantic::Unit,
            });
        };
        lowered.try_fold(first, |left, right| {
            let choice = self.std_parse_ref("choice")?;
            let left_parser = self.thunk_computation(left.expr);
            let right_parser = self.thunk_computation(right.expr);
            let partial = self.make_app(choice, left_parser);
            let expr = self.make_app(partial, right_parser);
            let semantic =
                if left.semantic == RuleSemantic::Unit && right.semantic == RuleSemantic::Unit {
                    RuleSemantic::Unit
                } else {
                    RuleSemantic::Value
                };
            Ok(RuleLowered { expr, semantic })
        })
    }

    fn lower_rule_sequence(&mut self, items: Vec<Cst>) -> Result<RuleLowered, LoweringError> {
        let mut stmts = Vec::new();
        let mut fields = Vec::new();
        let mut value = None;

        for item in items {
            if let Some((name, parser)) = rule_expr_capture(&item) {
                let parser = self.lower_expr(&parser)?;
                let unit = self.unit_expr();
                let run = self.make_app(parser, unit);
                let (stmt, captured) = self.bind_rule_capture(name.clone(), run);
                stmts.push(stmt);
                fields.push((name, captured));
                continue;
            }

            let lowered = self.lower_rule_item(&item)?;
            let unit = self.unit_expr();
            let run = self.make_app(lowered.parser, unit);
            match lowered.semantic {
                RuleSemantic::Unit => stmts.push(LoweredLocalStmt {
                    stmt: Stmt::Expr(run.expr),
                    effect: run.effect,
                }),
                RuleSemantic::Record | RuleSemantic::Value => {
                    if value.is_some() {
                        return Err(LoweringError::UnsupportedSyntax {
                            kind: SyntaxKind::RuleExpr,
                        });
                    }
                    value = Some(run);
                }
            }
        }

        let (tail, semantic) = if fields.is_empty() {
            match value {
                Some(value) => (value, RuleSemantic::Value),
                None => (self.unit_expr(), RuleSemantic::Unit),
            }
        } else {
            if value.is_some() {
                return Err(LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::RuleExpr,
                });
            }
            (self.rule_record_expr(fields), RuleSemantic::Record)
        };
        Ok(RuleLowered {
            expr: self.rule_block_expr(stmts, tail),
            semantic,
        })
    }

    fn lower_rule_item(&mut self, node: &Cst) -> Result<RuleParserItem, LoweringError> {
        if let Some(quant) = rule_quant(node) {
            return self.lower_rule_quant(node, quant);
        }

        if let Some(text) = plain_string_expr_text(node)? {
            return Ok(RuleParserItem {
                parser: self.rule_token_parser(text)?,
                semantic: RuleSemantic::Unit,
            });
        }

        if let Some(paren) = direct_child(node, SyntaxKind::Paren) {
            let body = self.lower_rule_container_body(&paren)?;
            return Ok(RuleParserItem {
                parser: self.thunk_computation(body.expr),
                semantic: body.semantic,
            });
        }

        Ok(RuleParserItem {
            parser: self.lower_expr(node)?,
            semantic: RuleSemantic::Value,
        })
    }

    fn lower_rule_quant(
        &mut self,
        node: &Cst,
        quant: SyntaxKind,
    ) -> Result<RuleParserItem, LoweringError> {
        let combinator = match quant {
            SyntaxKind::RuleQuantStar => "many",
            SyntaxKind::RuleQuantPlus => "some",
            SyntaxKind::RuleQuantOpt => "optional",
            SyntaxKind::RuleQuantStarLazy | SyntaxKind::RuleQuantPlusLazy => {
                return Err(LoweringError::UnsupportedSyntax { kind: quant });
            }
            _ => {
                return Err(LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::RuleQuant,
                });
            }
        };
        let base = self.lower_rule_quant_base(node)?;
        let combinator = self.std_parse_ref(combinator)?;
        Ok(RuleParserItem {
            parser: self.make_app(combinator, base.parser),
            semantic: if base.semantic == RuleSemantic::Unit {
                RuleSemantic::Unit
            } else {
                RuleSemantic::Value
            },
        })
    }

    fn lower_rule_quant_base(&mut self, node: &Cst) -> Result<RuleParserItem, LoweringError> {
        if let Some(text) = plain_string_expr_text(node)? {
            return Ok(RuleParserItem {
                parser: self.rule_token_parser(text)?,
                semantic: RuleSemantic::Unit,
            });
        }
        if let Some(paren) = direct_child(node, SyntaxKind::Paren) {
            let body = self.lower_rule_container_body(&paren)?;
            return Ok(RuleParserItem {
                parser: self.thunk_computation(body.expr),
                semantic: body.semantic,
            });
        }
        Ok(RuleParserItem {
            parser: self.lower_expr_chain_prefix_with_pipe_arg_until(
                node,
                LambdaScope::Anonymous,
                false,
                None,
                Some(SyntaxKind::RuleQuant),
            )?,
            semantic: RuleSemantic::Value,
        })
    }

    fn rule_token_parser(&mut self, text: String) -> Result<Computation, LoweringError> {
        let token = self.std_parse_ref("token")?;
        let expected = self.string_value(text);
        Ok(self.make_app(token, expected))
    }

    fn rule_word_parser(&mut self) -> Result<Computation, LoweringError> {
        self.std_parse_ref("word")
    }

    fn run_rule_parser(&mut self, parser: Computation) -> Computation {
        let unit = self.unit_expr();
        self.make_app(parser, unit)
    }

    fn std_parse_ref(&mut self, name: &str) -> Result<Computation, LoweringError> {
        self.lower_std_value_ref(crate::std_paths::text_parse_value(name))
    }

    fn bind_rule_capture(
        &mut self,
        name: Name,
        value: Computation,
    ) -> (LoweredLocalStmt, Computation) {
        let pat = self.bind_pattern_local(
            name.clone(),
            value.value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let local = self
            .locals
            .last()
            .cloned()
            .expect("rule capture should be the last local");
        let captured = self.lower_local_name(name, local);
        (
            LoweredLocalStmt {
                stmt: Stmt::Let(Vis::My, pat, value.expr),
                effect: value.effect,
            },
            captured,
        )
    }

    fn rule_record_expr(&mut self, fields: Vec<(Name, Computation)>) -> Computation {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_exact_pure_effect();
        let record_fields = fields
            .iter()
            .map(|(name, value)| RecordField {
                name: name.0.clone(),
                value: self.alloc_pos(Pos::Var(value.value)),
                optional: false,
            })
            .collect::<Vec<_>>();
        for (_, value) in &fields {
            self.subtype_var_to_var(value.effect, result_effect);
        }
        self.constrain_lower(result_value, Pos::Record(record_fields));

        let expr_fields = fields
            .into_iter()
            .map(|(name, value)| (name.0, value.expr))
            .collect();
        let expr = self.session.poly.add_expr(Expr::Record {
            fields: expr_fields,
            spread: RecordSpread::None,
        });
        Computation::value(expr, result_value, result_effect)
    }

    fn rule_block_expr(&mut self, stmts: Vec<LoweredLocalStmt>, tail: Computation) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_type_var();
        let mut ir_stmts = Vec::with_capacity(stmts.len());
        for stmt in stmts {
            self.subtype_var_to_var(stmt.effect, effect);
            ir_stmts.push(stmt.stmt);
        }
        self.subtype_var_to_var(tail.effect, effect);
        self.subtype_var_to_var(tail.value, value);
        let expr = self
            .session
            .poly
            .add_expr(Expr::Block(ir_stmts, Some(tail.expr)));
        Computation::computation(expr, value, effect)
    }
}

fn plain_rule_lit_text(node: &Cst) -> Option<String> {
    if node.children().any(|child| {
        matches!(
            child.kind(),
            SyntaxKind::RuleLazyCapture | SyntaxKind::RuleLitInterp
        )
    }) {
        return None;
    }

    Some(
        node.children_with_tokens()
            .filter_map(|item| item.into_token())
            .filter(|token| token.kind() == SyntaxKind::RuleLitText)
            .map(|token| token.text().to_string())
            .collect(),
    )
}

fn rule_lit_parts(node: &Cst) -> Result<Vec<RuleLitPart>, LoweringError> {
    let mut parts = Vec::new();
    for item in node.children_with_tokens() {
        if item_is_trivia(&item) {
            continue;
        }
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::RuleLitText => {
                parts.push(RuleLitPart::Token(token.text().to_string()));
            }
            NodeOrToken::Token(token)
                if matches!(
                    token.kind(),
                    SyntaxKind::RuleLitStart | SyntaxKind::RuleLitEnd
                ) => {}
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::RuleLazyCapture => {
                let name = lazy_capture_name(&child).ok_or(LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::RuleLazyCapture,
                })?;
                parts.push(RuleLitPart::CaptureWord(name));
            }
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::RuleLitInterp => {
                let parser = single_rule_lit_interp_expr(&child).ok_or(
                    LoweringError::UnsupportedSyntax {
                        kind: SyntaxKind::RuleLitInterp,
                    },
                )?;
                if let Some((name, parser)) = rule_expr_capture(&parser) {
                    parts.push(RuleLitPart::CaptureParser { name, parser });
                } else {
                    parts.push(RuleLitPart::Parser(parser));
                }
            }
            NodeOrToken::Node(child) => {
                return Err(LoweringError::UnsupportedSyntax { kind: child.kind() });
            }
            NodeOrToken::Token(token) => {
                return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
            }
        }
    }
    Ok(parts)
}

fn single_rule_lit_interp_expr(node: &Cst) -> Option<Cst> {
    let mut exprs = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::Expr);
    let expr = exprs.next()?;
    exprs.next().is_none().then_some(expr)
}

fn lazy_capture_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::RuleLitText)
        .map(|token| Name(token.text().to_string()))
}

fn rule_branches(node: &Cst) -> Vec<Vec<Cst>> {
    let mut branches = vec![Vec::new()];
    for child in node.children() {
        match child.kind() {
            SyntaxKind::Expr => {
                if let Some(branch) = branches.last_mut() {
                    branch.push(child);
                }
            }
            SyntaxKind::Separator => branches.push(Vec::new()),
            _ => {}
        }
    }
    branches
}

fn rule_expr_capture(node: &Cst) -> Option<(Name, Cst)> {
    let name = node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))?;
    let parser = node
        .children()
        .find(|child| child.kind() == SyntaxKind::RuleCapture)?
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)?;
    Some((name, parser))
}

fn rule_quant(node: &Cst) -> Option<SyntaxKind> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::RuleQuant)?
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find_map(|token| match token.kind() {
            SyntaxKind::RuleQuantStar
            | SyntaxKind::RuleQuantPlus
            | SyntaxKind::RuleQuantStarLazy
            | SyntaxKind::RuleQuantPlusLazy
            | SyntaxKind::RuleQuantOpt => Some(token.kind()),
            _ => None,
        })
}
