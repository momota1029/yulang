//! Yumark literal lowering into an eta-expanded algebra-passing builder.
//!
//! Every static node becomes a call to a `std::text::yumark` builder
//! combinator. One format and one algebra parameter flow through the complete
//! generated document; no recursive typed document tree is constructed.
//! Commands and inline expressions remain unsupported.

use super::*;

#[derive(Clone, Copy)]
struct YumarkSequenceOptions {
    include_newlines: bool,
    trim_trailing_line_breaks: bool,
}

impl YumarkSequenceOptions {
    const INLINE: Self = Self {
        include_newlines: true,
        trim_trailing_line_breaks: false,
    };

    const BLOCK_CONTENT: Self = Self {
        include_newlines: true,
        trim_trailing_line_breaks: true,
    };

    const LINE_CONTENT: Self = Self {
        include_newlines: false,
        trim_trailing_line_breaks: true,
    };
}

impl<'a> ExprLowerer<'a> {
    pub(super) fn lower_mark_expr(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let doc = mark_expr_doc(node)?;
        self.lower_yumark_builder(&doc)
    }

    fn lower_yumark_builder(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        // Eta-expand the generated builder so one let-bound literal can be
        // selected at multiple representation types without value restriction.
        self.lower_yumark_builder_lambda(Name("#yumark-format".to_string()), |lowerer, format| {
            lowerer.lower_yumark_builder_lambda(
                Name("#yumark-algebra".to_string()),
                |lowerer, algebra| {
                    let document =
                        lowerer.lower_yumark_sequence(node, YumarkSequenceOptions::INLINE)?;
                    let format =
                        lowerer.lower_local_name(format.name.clone(), format.clone(), None);
                    let algebra = lowerer.lower_local_name(algebra.name.clone(), algebra, None);
                    let document = lowerer.make_app(document, format);
                    Ok(lowerer.make_app(document, algebra))
                },
            )
        })
    }

    fn lower_yumark_builder_lambda(
        &mut self,
        param_name: Name,
        lower_body: impl FnOnce(&mut Self, LocalBinding) -> Result<Computation, LoweringError>,
    ) -> Result<Computation, LoweringError> {
        let param_value = self.fresh_type_var();
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            param_name,
            param_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let Pat::Var(param_def) = self.session.poly.pat(pat) else {
            unreachable!("Yumark builder parameter should lower to a variable pattern");
        };
        if let Some(use_site) = self.session.local_defs.get_mut(*param_def) {
            use_site.role = LocalDefRole::Input;
        }
        let param = self
            .locals
            .last()
            .cloned()
            .expect("Yumark builder parameter should be the last local");

        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Anonymous));
        let previous_level = self.session.infer.enter_child_level();
        let previous_local_generalize_boundary = self.local_generalize_boundary;
        self.local_generalize_boundary = previous_level;
        let body_result = lower_body(self, param);
        self.local_generalize_boundary = previous_local_generalize_boundary;
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("Yumark builder predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(param_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts = self.lambda_predicate_subtracts(
            LambdaScope::Anonymous,
            PredicateOutputConstraints::default(),
            frame,
        );
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

    fn lower_yumark_node(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::YmDoc => self.lower_yumark_sequence(node, YumarkSequenceOptions::INLINE),
            SyntaxKind::YmParagraph => self.lower_yumark_paragraph(node),
            SyntaxKind::YmEmphasis => self.lower_yumark_container("emphasis", node),
            SyntaxKind::YmStrong => self.lower_yumark_container("strong", node),
            SyntaxKind::YmHeading => self.lower_yumark_heading(node),
            SyntaxKind::YmBlankLine => {
                let marker = self.string_value("\n".to_string());
                self.yumark_static_operation("blank_line", vec![("marker", marker)])
            }
            SyntaxKind::YmSectionClose => self.lower_yumark_section_close(node),
            SyntaxKind::YmList => self.lower_yumark_list(node),
            SyntaxKind::YmListItem => self.lower_yumark_list_item(node),
            SyntaxKind::YmListItemBody => self.lower_yumark_list_item_body(node),
            SyntaxKind::YmCodeFence => self.lower_yumark_code_fence(node),
            SyntaxKind::YmQuoteBlock => self.lower_yumark_container("quote_block", node),
            _ => Err(LoweringError::UnsupportedSyntax { kind: node.kind() }),
        }
    }

    fn lower_yumark_paragraph(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::BLOCK_CONTENT)?;
        self.yumark_static_operation("paragraph", vec![("children", children)])
    }

    fn lower_yumark_container(
        &mut self,
        operation: &str,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::INLINE)?;
        self.yumark_static_operation(operation, vec![("children", children)])
    }

    fn lower_yumark_heading(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let marker = required_token_text(node, &[SyntaxKind::YmHashSigil])?;
        let level = marker.chars().take_while(|ch| *ch == '#').count() as i64;
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::LINE_CONTENT)?;
        let marker = self.string_value(marker);
        let level = self.int_value(level);
        self.yumark_static_operation(
            "heading",
            vec![("marker", marker), ("level", level), ("children", children)],
        )
    }

    fn lower_yumark_section_close(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let marker = required_token_text(node, &[SyntaxKind::YmHashDotSigil])?;
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::LINE_CONTENT)?;
        let marker = self.string_value(marker);
        self.yumark_static_operation(
            "section_close",
            vec![("marker", marker), ("children", children)],
        )
    }

    fn lower_yumark_list(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let items = self.lower_yumark_sequence(node, YumarkSequenceOptions::INLINE)?;
        let ordered = self.lower_bool(list_is_ordered(node));
        self.yumark_static_operation("list_block", vec![("ordered", ordered), ("items", items)])
    }

    fn lower_yumark_list_item(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let marker = required_token_text(
            node,
            &[SyntaxKind::YmListDashSigil, SyntaxKind::YmListNumSigil],
        )?;
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::BLOCK_CONTENT)?;
        let marker = self.string_value(marker);
        self.yumark_static_operation(
            "list_item",
            vec![("marker", marker), ("children", children)],
        )
    }

    fn lower_yumark_list_item_body(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::BLOCK_CONTENT)?;
        self.yumark_static_operation("list_item_body", vec![("children", children)])
    }

    fn lower_yumark_code_fence(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let (info, body) = self.code_fence_raw_source(node)?;
        let info = self.string_value(info);
        let body = self.string_value(body);
        self.yumark_static_operation("code_fence", vec![("info", info), ("body", body)])
    }

    fn lower_yumark_sequence(
        &mut self,
        node: &Cst,
        options: YumarkSequenceOptions,
    ) -> Result<Computation, LoweringError> {
        let mut lowered = Vec::new();
        let mut text = String::new();
        for item in node.children_with_tokens() {
            match item {
                NodeOrToken::Token(token) => {
                    let kind = token.kind();
                    if token_is_yumark_text(kind, options.include_newlines) {
                        text.push_str(token.text());
                    } else if token_is_yumark_syntax(kind) {
                        continue;
                    } else {
                        return Err(LoweringError::UnsupportedSyntax { kind });
                    }
                }
                NodeOrToken::Node(child) => {
                    if is_empty_yumark_paragraph(&child) {
                        continue;
                    }
                    self.flush_yumark_text(&mut text, &mut lowered, options)?;
                    lowered.push(self.lower_yumark_node(&child)?);
                }
            }
        }
        self.flush_yumark_text(&mut text, &mut lowered, options)?;
        self.yumark_chain(lowered)
    }

    fn flush_yumark_text(
        &mut self,
        text: &mut String,
        lowered: &mut Vec<Computation>,
        options: YumarkSequenceOptions,
    ) -> Result<(), LoweringError> {
        if options.trim_trailing_line_breaks {
            trim_trailing_line_breaks(text);
        }
        if !text.is_empty() {
            lowered.push(self.yumark_text(std::mem::take(text))?);
        }
        Ok(())
    }

    fn yumark_chain(&mut self, lowered: Vec<Computation>) -> Result<Computation, LoweringError> {
        let mut tail = self.yumark_operation_ref("nil")?;
        for head in lowered.into_iter().rev() {
            let cons = self.yumark_operation_ref("cons")?;
            let partial = self.make_app(cons, head);
            tail = self.make_app(partial, tail);
        }
        Ok(tail)
    }

    fn yumark_text(&mut self, text: String) -> Result<Computation, LoweringError> {
        let value = self.string_value(text);
        let text = self.yumark_operation_ref("text")?;
        Ok(self.make_app(text, value))
    }

    fn yumark_static_operation(
        &mut self,
        operation: &str,
        fields: Vec<(&str, Computation)>,
    ) -> Result<Computation, LoweringError> {
        let mut call = self.yumark_operation_ref(operation)?;
        for (_, value) in fields {
            call = self.make_app(call, value);
        }
        Ok(call)
    }

    fn yumark_operation_ref(&mut self, name: &str) -> Result<Computation, LoweringError> {
        self.lower_std_value_ref(crate::std_paths::text_yumark_value(name))
    }

    fn code_fence_raw_source(&self, node: &Cst) -> Result<(String, String), LoweringError> {
        let text = node.text().to_string();
        split_code_fence_node_text(&text).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::YmCodeFence,
        })
    }
}

fn split_code_fence_node_text(text: &str) -> Option<(String, String)> {
    let text = text.strip_prefix("```")?;
    let (info, rest) = text.split_once('\n')?;
    let body = if rest.starts_with("```") {
        ""
    } else {
        let close = rest.rfind("\n```")?;
        &rest[..close]
    };
    Some((info.trim_end_matches('\r').to_string(), body.to_string()))
}

fn mark_expr_doc(node: &Cst) -> Result<Cst, LoweringError> {
    if node.kind() != SyntaxKind::MarkExpr {
        return Err(LoweringError::UnsupportedSyntax { kind: node.kind() });
    }
    let body = node
        .children()
        .next()
        .ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::MarkExpr,
        })?;
    if !matches!(
        body.kind(),
        SyntaxKind::MarkInlineBody | SyntaxKind::MarkHeredocBody
    ) {
        return Err(LoweringError::UnsupportedSyntax { kind: body.kind() });
    }
    if node.children().nth(1).is_some() {
        return Err(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::MarkExpr,
        });
    }

    let mut docs = body
        .children()
        .filter(|child| child.kind() == SyntaxKind::YmDoc);
    let doc = docs
        .next()
        .ok_or(LoweringError::UnsupportedSyntax { kind: body.kind() })?;
    if docs.next().is_some() {
        return Err(LoweringError::UnsupportedSyntax { kind: body.kind() });
    }

    for item in body.children_with_tokens() {
        match item {
            NodeOrToken::Token(token)
                if matches!(
                    token.kind(),
                    SyntaxKind::MarkLitStart
                        | SyntaxKind::MarkLitEnd
                        | SyntaxKind::Space
                        | SyntaxKind::YmNewline
                ) => {}
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::YmDoc => {}
            NodeOrToken::Token(token) => {
                return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
            }
            NodeOrToken::Node(child) => {
                return Err(LoweringError::UnsupportedSyntax { kind: child.kind() });
            }
        }
    }

    Ok(doc)
}

fn required_token_text(node: &Cst, kinds: &[SyntaxKind]) -> Result<String, LoweringError> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| kinds.contains(&token.kind()))
        .map(|token| token.text().to_string())
        .ok_or(LoweringError::UnsupportedSyntax { kind: node.kind() })
}

fn list_is_ordered(node: &Cst) -> bool {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::YmListItem)
        .flat_map(|child| child.children_with_tokens())
        .filter_map(|item| item.into_token())
        .find_map(|token| match token.kind() {
            SyntaxKind::YmListNumSigil => Some(true),
            SyntaxKind::YmListDashSigil => Some(false),
            _ => None,
        })
        .unwrap_or(false)
}

fn is_empty_yumark_paragraph(node: &Cst) -> bool {
    node.kind() == SyntaxKind::YmParagraph
        && node.children_with_tokens().all(|item| match item {
            NodeOrToken::Token(token) => token_is_yumark_syntax(token.kind()),
            NodeOrToken::Node(child) => is_empty_yumark_paragraph(&child),
        })
}

fn token_is_yumark_text(kind: SyntaxKind, include_newlines: bool) -> bool {
    matches!(kind, SyntaxKind::YmText | SyntaxKind::Space)
        || (include_newlines && kind == SyntaxKind::YmNewline)
}

fn token_is_yumark_syntax(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::MarkLitStart
            | SyntaxKind::MarkLitEnd
            | SyntaxKind::YmStarSigil
            | SyntaxKind::YmStrongSigil
            | SyntaxKind::YmHashSigil
            | SyntaxKind::YmHashDotSigil
            | SyntaxKind::YmListDashSigil
            | SyntaxKind::YmListNumSigil
            | SyntaxKind::YmChevronPrefixSigil
            | SyntaxKind::YmFenceSigil
            | SyntaxKind::QuotePrefix
            | SyntaxKind::YmNewline
    )
}

fn trim_trailing_line_breaks(text: &mut String) {
    while text.ends_with('\n') || text.ends_with('\r') {
        text.pop();
    }
}
