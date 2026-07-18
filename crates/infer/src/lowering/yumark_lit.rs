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

/// Structural blank-line boundaries found in one Yumark CST sequence.
///
/// The parser currently emits the same source boundary both as trailing
/// trivia in the preceding child and as direct sequence trivia immediately
/// before a zero-width `YmBlankLine`. Keeping those ranges together lets the
/// lowering path discard the boundary once without rewriting the parser CST.
// Slice 2 deliberately lands this mechanism before production lowering uses it.
#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct YumarkSequenceNormalization {
    pub(super) structural_blank_boundaries: Vec<YumarkStructuralBlankBoundary>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct YumarkStructuralBlankBoundary {
    pub(super) range: rowan::TextRange,
    pub(super) trivia_ranges: Vec<rowan::TextRange>,
    pub(super) blank_line_range: rowan::TextRange,
}

/// Identify parser-generated blank nodes and every adjacent duplicate of
/// their source boundary. This is intentionally not wired into lowering yet.
#[allow(dead_code)]
pub(super) fn normalize_yumark_sequence_blank_boundaries(
    node: &Cst,
) -> YumarkSequenceNormalization {
    let items = node.children_with_tokens().collect::<Vec<_>>();
    let mut structural_blank_boundaries = Vec::new();

    for (blank_index, item) in items.iter().enumerate() {
        let NodeOrToken::Node(blank_line) = item else {
            continue;
        };
        if blank_line.kind() != SyntaxKind::YmBlankLine {
            continue;
        }

        let mut direct_left = blank_index;
        let mut direct_left_ranges = Vec::new();
        while let Some(NodeOrToken::Token(token)) = direct_left
            .checked_sub(1)
            .and_then(|index| items.get(index))
        {
            if !token_is_yumark_blank_boundary_trivia(token) {
                break;
            }
            direct_left -= 1;
            direct_left_ranges.push(token.text_range());
        }
        direct_left_ranges.reverse();

        let mut trivia_ranges = direct_left
            .checked_sub(1)
            .and_then(|index| items.get(index))
            .and_then(NodeOrToken::as_node)
            .map(trailing_yumark_blank_boundary_trivia_ranges)
            .unwrap_or_default();
        trivia_ranges.extend(direct_left_ranges);

        let mut direct_right = blank_index + 1;
        while let Some(NodeOrToken::Token(token)) = items.get(direct_right) {
            if !token_is_yumark_blank_boundary_trivia(token) {
                break;
            }
            trivia_ranges.push(token.text_range());
            direct_right += 1;
        }

        let blank_line_range = blank_line.text_range();
        let mut range = blank_line.text_range();
        for trivia_range in &trivia_ranges {
            range = range.cover(*trivia_range);
        }
        structural_blank_boundaries.push(YumarkStructuralBlankBoundary {
            range,
            trivia_ranges,
            blank_line_range,
        });
    }

    YumarkSequenceNormalization {
        structural_blank_boundaries,
    }
}

#[allow(dead_code)]
fn trailing_yumark_blank_boundary_trivia_ranges(node: &Cst) -> Vec<rowan::TextRange> {
    let tokens = node
        .descendants_with_tokens()
        .filter_map(NodeOrToken::into_token)
        .collect::<Vec<_>>();
    let mut ranges = Vec::new();
    for token in tokens.into_iter().rev() {
        if !token_is_yumark_blank_boundary_trivia(&token) {
            break;
        }
        ranges.push(token.text_range());
    }
    ranges.reverse();
    ranges
}

#[allow(dead_code)]
fn token_is_yumark_blank_boundary_trivia(token: &rowan::SyntaxToken<YulangLanguage>) -> bool {
    matches!(
        token.kind(),
        SyntaxKind::Space | SyntaxKind::YmNewline | SyntaxKind::QuotePrefix
    ) && token.text().chars().any(|ch| matches!(ch, '\n' | '\r'))
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

#[cfg(test)]
mod boundary_normalization_tests {
    use super::*;

    fn parsed_yumark_doc(body: &str) -> Cst {
        let source = format!("pub main = '{{{body}}}\n");
        let root = SyntaxNode::new_root(parser::parse_module_to_green(&source));
        root.descendants()
            .find(|node| node.kind() == SyntaxKind::YmDoc)
            .expect("ordinary Yumark literal should contain YmDoc")
    }

    fn assert_single_structural_boundary(
        body: &str,
        sequence_kind: SyntaxKind,
        expected_trivia: &[(SyntaxKind, &str)],
    ) {
        let doc = parsed_yumark_doc(body);
        let sequence = if doc.kind() == sequence_kind {
            doc
        } else {
            doc.descendants()
                .find(|node| node.kind() == sequence_kind)
                .unwrap_or_else(|| panic!("missing {sequence_kind:?} in {body:?}"))
        };
        let normalization = normalize_yumark_sequence_blank_boundaries(&sequence);
        let [boundary] = normalization.structural_blank_boundaries.as_slice() else {
            panic!(
                "expected one structural blank boundary in {body:?}, got {:?}",
                normalization.structural_blank_boundaries
            );
        };

        let blank_line = sequence
            .children()
            .find(|node| node.kind() == SyntaxKind::YmBlankLine)
            .expect("sequence should contain YmBlankLine");
        assert_eq!(boundary.blank_line_range, blank_line.text_range());

        let actual_trivia = boundary
            .trivia_ranges
            .iter()
            .map(|range| {
                let token = sequence
                    .descendants_with_tokens()
                    .filter_map(NodeOrToken::into_token)
                    .find(|token| token.text_range() == *range)
                    .unwrap_or_else(|| panic!("missing boundary token at {range:?}"));
                (token.kind(), token.text().to_string())
            })
            .collect::<Vec<_>>();
        let expected_trivia = expected_trivia
            .iter()
            .map(|(kind, text)| (*kind, (*text).to_string()))
            .collect::<Vec<_>>();
        assert_eq!(actual_trivia, expected_trivia, "{body:?}");

        for ranges in boundary.trivia_ranges.windows(2) {
            assert_eq!(ranges[0].end(), ranges[1].start(), "{body:?}");
        }
        let first = boundary
            .trivia_ranges
            .first()
            .expect("characterized boundaries carry parser trivia");
        let last = boundary
            .trivia_ranges
            .last()
            .expect("characterized boundaries carry parser trivia");
        assert_eq!(boundary.range.start(), first.start(), "{body:?}");
        assert_eq!(boundary.range.end(), last.end(), "{body:?}");
        assert_eq!(blank_line.text_range().start(), boundary.range.end());
        assert_eq!(blank_line.text_range().end(), boundary.range.end());
    }

    #[test]
    fn normalizes_paragraph_to_paragraph_blank_boundary() {
        assert_single_structural_boundary(
            "first\n\nsecond\n",
            SyntaxKind::YmDoc,
            &[
                (SyntaxKind::Space, "\n"),
                (SyntaxKind::Space, "\n"),
                (SyntaxKind::YmNewline, "\n"),
                (SyntaxKind::YmNewline, "\n"),
            ],
        );
    }

    #[test]
    fn normalizes_leading_blank_boundary() {
        assert_single_structural_boundary(
            "\n\nfirst\n",
            SyntaxKind::YmDoc,
            &[(SyntaxKind::YmNewline, "\n"), (SyntaxKind::YmNewline, "\n")],
        );
    }

    #[test]
    fn normalizes_trailing_blank_boundary() {
        assert_single_structural_boundary(
            "first\n\n",
            SyntaxKind::YmDoc,
            &[
                (SyntaxKind::Space, "\n"),
                (SyntaxKind::Space, "\n"),
                (SyntaxKind::YmNewline, "\n"),
                (SyntaxKind::YmNewline, "\n"),
            ],
        );
    }

    #[test]
    fn normalizes_multiple_consecutive_blank_lines_as_one_boundary() {
        assert_single_structural_boundary(
            "first\n\n\nsecond\n",
            SyntaxKind::YmDoc,
            &[
                (SyntaxKind::Space, "\n"),
                (SyntaxKind::Space, "\n"),
                (SyntaxKind::Space, "\n"),
                (SyntaxKind::YmNewline, "\n"),
                (SyntaxKind::YmNewline, "\n"),
                (SyntaxKind::YmNewline, "\n"),
            ],
        );
    }

    #[test]
    fn normalizes_whitespace_only_blank_line_boundary() {
        assert_single_structural_boundary(
            "first\n  \nsecond\n",
            SyntaxKind::YmDoc,
            &[
                (SyntaxKind::Space, "\n  "),
                (SyntaxKind::Space, "\n"),
                (SyntaxKind::YmNewline, "\n  "),
                (SyntaxKind::YmNewline, "\n"),
            ],
        );
    }

    #[test]
    fn normalizes_blank_boundary_inside_quote() {
        assert_single_structural_boundary(
            "> foo\n>\n> bar\n",
            SyntaxKind::YmQuoteBlock,
            &[
                (SyntaxKind::QuotePrefix, "\n>\n> "),
                (SyntaxKind::QuotePrefix, "\n>\n> "),
            ],
        );
    }

    #[test]
    fn normalizes_crlf_blank_boundary() {
        assert_single_structural_boundary(
            "first\r\n\r\nsecond\r\n",
            SyntaxKind::YmDoc,
            &[
                (SyntaxKind::Space, "\r\n"),
                (SyntaxKind::Space, "\r\n"),
                (SyntaxKind::YmNewline, "\r\n"),
                (SyntaxKind::YmNewline, "\r\n"),
            ],
        );
    }
}
