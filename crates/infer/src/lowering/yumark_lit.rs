//! Yumark literal lowering for the first typed-cons-chain slice.
//!
//! This module intentionally accepts only quoted inline Yumark whose document
//! body is plain text. Rich Yumark nodes remain rejected until their value-model
//! vocabulary is wired into lowering.

use super::*;

impl<'a> ExprLowerer<'a> {
    pub(super) fn lower_mark_expr(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        match plain_inline_yumark_text(node)? {
            Some(text) => {
                let head = self.yumark_text_leaf(text)?;
                let tail = self.yumark_nil()?;
                self.yumark_cons(head, tail)
            }
            None => self.yumark_nil(),
        }
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
        let constructor = self.yumark_ref("text_leaf")?;
        let value = self.string_value(text);
        let payload = self.synthetic_record_value(vec![("value".to_string(), value)]);
        Ok(self.make_app(constructor, payload))
    }

    fn yumark_ref(&mut self, name: &str) -> Result<Computation, LoweringError> {
        self.lower_std_value_ref(crate::std_paths::text_yumark_value(name))
    }
}

fn plain_inline_yumark_text(node: &Cst) -> Result<Option<String>, LoweringError> {
    if node.kind() != SyntaxKind::MarkExpr {
        return Err(LoweringError::UnsupportedSyntax { kind: node.kind() });
    }

    let body = node
        .children()
        .next()
        .ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::MarkExpr,
        })?;
    if body.kind() != SyntaxKind::MarkInlineBody {
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
    let doc = docs.next().ok_or(LoweringError::UnsupportedSyntax {
        kind: SyntaxKind::MarkInlineBody,
    })?;
    if docs.next().is_some() {
        return Err(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::MarkInlineBody,
        });
    }

    for item in body.children_with_tokens() {
        match item {
            NodeOrToken::Token(token)
                if matches!(
                    token.kind(),
                    SyntaxKind::MarkLitStart | SyntaxKind::MarkLitEnd
                ) => {}
            NodeOrToken::Token(token)
                if matches!(token.kind(), SyntaxKind::Space | SyntaxKind::YmNewline) => {}
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::YmDoc => {}
            NodeOrToken::Token(token) => {
                return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
            }
            NodeOrToken::Node(child) => {
                return Err(LoweringError::UnsupportedSyntax { kind: child.kind() });
            }
        }
    }

    let mut text = String::new();
    for item in doc.children_with_tokens() {
        match item {
            NodeOrToken::Token(token)
                if matches!(
                    token.kind(),
                    SyntaxKind::YmText | SyntaxKind::Space | SyntaxKind::YmNewline
                ) =>
            {
                text.push_str(token.text());
            }
            NodeOrToken::Token(token) => {
                return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
            }
            NodeOrToken::Node(child) => {
                return Err(LoweringError::UnsupportedSyntax { kind: child.kind() });
            }
        }
    }

    Ok((!text.is_empty()).then_some(text))
}
