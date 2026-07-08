//! Yumark literal lowering into the std typed cons-chain vocabulary.
//!
//! Quoted Yumark expressions lower to bare `std::text::yumark::cons`/`nil`
//! chains. Each static node kind becomes the corresponding stdlib leaf
//! constructor, and container children are lowered recursively into their own
//! concrete cons-chain shape.

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
        self.lower_yumark_doc(&doc)
    }

    fn lower_yumark_doc(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        if node.kind() != SyntaxKind::YmDoc {
            return Err(LoweringError::UnsupportedSyntax { kind: node.kind() });
        }
        self.lower_yumark_sequence(node, YumarkSequenceOptions::INLINE)
    }

    fn lower_yumark_node(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::YmDoc => self.lower_yumark_doc(node),
            SyntaxKind::YmParagraph => self.lower_yumark_paragraph(node),
            SyntaxKind::YmEmphasis => self.lower_yumark_container("emphasis_leaf", node),
            SyntaxKind::YmStrong => self.lower_yumark_container("strong_leaf", node),
            SyntaxKind::YmHeading => self.lower_yumark_heading(node),
            SyntaxKind::YmBlankLine => {
                let marker = self.string_value("\n".to_string());
                self.yumark_leaf("blank_line_leaf", vec![("marker", marker)])
            }
            SyntaxKind::YmSectionClose => self.lower_yumark_section_close(node),
            SyntaxKind::YmList => self.lower_yumark_list(node),
            SyntaxKind::YmListItem => self.lower_yumark_list_item(node),
            SyntaxKind::YmListItemBody => self.lower_yumark_list_item_body(node),
            SyntaxKind::YmCodeFence => self.lower_yumark_code_fence(node),
            SyntaxKind::YmQuoteBlock => self.lower_yumark_container("quote_block_leaf", node),
            _ => Err(LoweringError::UnsupportedSyntax { kind: node.kind() }),
        }
    }

    fn lower_yumark_paragraph(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::BLOCK_CONTENT)?;
        self.yumark_leaf("paragraph_leaf", vec![("children", children)])
    }

    fn lower_yumark_container(
        &mut self,
        constructor: &str,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::INLINE)?;
        self.yumark_leaf(constructor, vec![("children", children)])
    }

    fn lower_yumark_heading(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let marker = required_token_text(node, &[SyntaxKind::YmHashSigil])?;
        let level = marker.chars().take_while(|ch| *ch == '#').count() as i64;
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::LINE_CONTENT)?;
        let marker = self.string_value(marker);
        let level = self.int_value(level);
        self.yumark_leaf(
            "heading_leaf",
            vec![("marker", marker), ("level", level), ("children", children)],
        )
    }

    fn lower_yumark_section_close(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let marker = required_token_text(node, &[SyntaxKind::YmHashDotSigil])?;
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::LINE_CONTENT)?;
        let marker = self.string_value(marker);
        self.yumark_leaf(
            "section_close_leaf",
            vec![("marker", marker), ("children", children)],
        )
    }

    fn lower_yumark_list(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let items = self.lower_yumark_sequence(node, YumarkSequenceOptions::INLINE)?;
        let ordered = self.lower_bool(list_is_ordered(node));
        self.yumark_leaf(
            "list_block_leaf",
            vec![("ordered", ordered), ("items", items)],
        )
    }

    fn lower_yumark_list_item(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let marker = required_token_text(
            node,
            &[SyntaxKind::YmListDashSigil, SyntaxKind::YmListNumSigil],
        )?;
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::BLOCK_CONTENT)?;
        let marker = self.string_value(marker);
        self.yumark_leaf(
            "list_item_leaf",
            vec![("marker", marker), ("children", children)],
        )
    }

    fn lower_yumark_list_item_body(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let children = self.lower_yumark_sequence(node, YumarkSequenceOptions::BLOCK_CONTENT)?;
        self.yumark_leaf("list_item_body_leaf", vec![("children", children)])
    }

    fn lower_yumark_code_fence(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let (info, body) = self.code_fence_raw_source(node)?;
        let info = self.string_value(info);
        let body = self.string_value(body);
        self.yumark_leaf("code_fence_leaf", vec![("info", info), ("body", body)])
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
            lowered.push(self.yumark_text_leaf(std::mem::take(text))?);
        }
        Ok(())
    }

    fn yumark_chain(&mut self, lowered: Vec<Computation>) -> Result<Computation, LoweringError> {
        let mut tail = self.yumark_nil()?;
        for head in lowered.into_iter().rev() {
            tail = self.yumark_cons(head, tail)?;
        }
        Ok(tail)
    }

    fn yumark_cons(
        &mut self,
        head: Computation,
        tail: Computation,
    ) -> Result<Computation, LoweringError> {
        let cons = self.yumark_ref("cons")?;
        let partial = self.make_app(cons, head);
        Ok(self.make_app(partial, tail))
    }

    fn yumark_nil(&mut self) -> Result<Computation, LoweringError> {
        let nil = self.yumark_ref("nil")?;
        let unit = self.unit_expr();
        Ok(self.make_app(nil, unit))
    }

    fn yumark_text_leaf(&mut self, text: String) -> Result<Computation, LoweringError> {
        let value = self.string_value(text);
        self.yumark_leaf("text_leaf", vec![("value", value)])
    }

    fn yumark_leaf(
        &mut self,
        constructor: &str,
        fields: Vec<(&str, Computation)>,
    ) -> Result<Computation, LoweringError> {
        let constructor = self.yumark_ref(constructor)?;
        let payload = self.synthetic_record_value(
            fields
                .into_iter()
                .map(|(name, value)| (name.to_string(), value))
                .collect(),
        );
        Ok(self.make_app(constructor, payload))
    }

    fn yumark_ref(&mut self, name: &str) -> Result<Computation, LoweringError> {
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
