//! Owned, cache-ready input and per-unit literal mapping for lazy Yumark docs.
//!
//! Unit sources are never joined: each successful mapping becomes one ordinary
//! literal, while typed failures retain that unit's static fallback bytes. The
//! runtime concatenates rendered unit outputs in their original order.

use parser::lex::SyntaxKind;
use rowan::NodeOrToken;

use crate::doc_comment_render::{
    doc_comment_is_safe_for_yumark_literal_reparse, render_doc_unit_markdown,
};
use crate::{DocComment, DocCommentKind, DocCommentUnit};

/// An owned safe-subset doc comment awaiting Yumark literal construction.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DocCommentRenderInput {
    key: DocCommentRenderInputKey,
}

impl DocCommentRenderInput {
    /// Copy the exact logical bodies of a doc comment accepted by the Slice 1
    /// safe-subset check. Lossless line-doc continuation prefixes stay in the
    /// CST but are not literal body content.
    ///
    /// Joining fragments and normalizing their boundaries are deliberately
    /// deferred to literal construction.
    pub fn from_safe_doc_comment(doc: &DocComment) -> Self {
        debug_assert!(
            doc_comment_is_safe_for_yumark_literal_reparse(doc),
            "lazy Yumark render input requires a delimiter-safe static doc comment"
        );
        let units = doc
            .units()
            .iter()
            .map(DocCommentRenderInputUnit::from_doc_comment_unit)
            .collect();
        Self {
            key: DocCommentRenderInputKey { units },
        }
    }

    pub fn units(&self) -> &[DocCommentRenderInputUnit] {
        self.key.units()
    }

    pub fn key(&self) -> &DocCommentRenderInputKey {
        &self.key
    }
}

/// Content identity for a lazy doc render, independent of source location.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DocCommentRenderInputKey {
    units: Vec<DocCommentRenderInputUnit>,
}

impl DocCommentRenderInputKey {
    pub fn units(&self) -> &[DocCommentRenderInputUnit] {
        &self.units
    }
}

/// One logical doc-comment unit with its delimiter-free, unnormalized body.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DocCommentRenderInputUnit {
    kind: DocCommentKind,
    body_source: String,
    literal_closing_boundary: Result<LiteralClosingBoundary, DocUnitLiteralMappingError>,
    static_fallback_markdown: Option<String>,
}

impl DocCommentRenderInputUnit {
    pub fn kind(&self) -> DocCommentKind {
        self.kind
    }

    pub fn body_source(&self) -> &str {
        &self.body_source
    }

    /// Construct one ordinary Yumark literal for this unit.
    ///
    /// The closing brace replaces the doc-comment delimiter boundary. Blocks
    /// whose grammar needs a line terminator keep exactly one. Fence and quote
    /// parsers also require that separator; their extra rendered boundary is
    /// identified separately by [`Self::rendered_markdown_suffix_to_trim`].
    pub fn to_synthetic_yumark_literal(&self) -> Result<String, DocUnitLiteralMappingError> {
        self.literal_closing_boundary?;
        let mut body = self.body_source.as_str();
        match self.kind {
            DocCommentKind::Line => {
                body = body.strip_prefix(' ').unwrap_or(body);
            }
            DocCommentKind::Block => {
                while let Some(rest) = body.strip_prefix("\r\n") {
                    body = rest;
                }
                while let Some(rest) = body.strip_prefix('\n') {
                    body = rest;
                }
            }
        }

        let line_ending = if body.ends_with("\r\n") { "\r\n" } else { "\n" };
        body = body.trim_end_matches(['\r', '\n']);

        let mut literal = String::with_capacity(body.len() + line_ending.len() + 3);
        literal.push_str("'{");
        literal.push_str(body);
        literal.push_str(line_ending);
        literal.push('}');
        Ok(literal)
    }

    /// Renderer suffix contributed by the synthetic literal boundary.
    pub fn rendered_markdown_suffix_to_trim(
        &self,
    ) -> Result<&'static str, DocUnitLiteralMappingError> {
        match self.literal_closing_boundary? {
            LiteralClosingBoundary::LineTerminated => Ok(""),
            LiteralClosingBoundary::StructuralSeparator => Ok("\n"),
        }
    }

    /// Static bytes for this unit when literal construction is unavailable.
    pub fn static_fallback_markdown(&self) -> Option<&str> {
        self.static_fallback_markdown.as_deref()
    }

    fn from_doc_comment_unit(unit: &DocCommentUnit) -> Self {
        let mut body_source = String::new();
        for doc in unit
            .node()
            .children()
            .filter(|child| child.kind() == SyntaxKind::YmDoc)
        {
            for token in doc
                .descendants_with_tokens()
                .filter_map(NodeOrToken::into_token)
            {
                if token.kind() != SyntaxKind::LineDocPrefix {
                    body_source.push_str(token.text());
                }
            }
        }
        let literal_closing_boundary = literal_closing_boundary(unit, &body_source);
        let static_fallback_markdown = literal_closing_boundary
            .is_err()
            .then(|| render_doc_unit_markdown(unit));
        Self {
            kind: unit.kind(),
            body_source,
            literal_closing_boundary,
            static_fallback_markdown,
        }
    }
}

/// Why an otherwise syntax-safe doc unit cannot become an ordinary literal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DocUnitLiteralMappingError {
    EmptyOrBoundaryOnlyUnit,
    MissingTerminalStructure,
    UnsupportedTerminalStructure { kind: SyntaxKind },
}

impl std::fmt::Display for DocUnitLiteralMappingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyOrBoundaryOnlyUnit => {
                f.write_str("doc unit contains no literal-renderable content")
            }
            Self::MissingTerminalStructure => f.write_str("doc unit has no terminal Yumark node"),
            Self::UnsupportedTerminalStructure { kind } => {
                write!(f, "unsupported terminal Yumark structure {kind:?}")
            }
        }
    }
}

impl std::error::Error for DocUnitLiteralMappingError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum LiteralClosingBoundary {
    LineTerminated,
    StructuralSeparator,
}

fn literal_closing_boundary(
    unit: &DocCommentUnit,
    body_source: &str,
) -> Result<LiteralClosingBoundary, DocUnitLiteralMappingError> {
    if body_source.chars().all(char::is_whitespace) {
        return Err(DocUnitLiteralMappingError::EmptyOrBoundaryOnlyUnit);
    }

    let terminal_kind = unit
        .node()
        .children()
        .filter(|child| child.kind() == SyntaxKind::YmDoc)
        .flat_map(|doc| doc.children())
        .last()
        .map(|node| node.kind())
        .ok_or(DocUnitLiteralMappingError::MissingTerminalStructure)?;
    match terminal_kind {
        SyntaxKind::YmParagraph
        | SyntaxKind::YmHeading
        | SyntaxKind::YmList
        | SyntaxKind::YmSectionClose => Ok(LiteralClosingBoundary::LineTerminated),
        SyntaxKind::YmCodeFence | SyntaxKind::YmQuoteBlock => {
            Ok(LiteralClosingBoundary::StructuralSeparator)
        }
        kind => Err(DocUnitLiteralMappingError::UnsupportedTerminalStructure { kind }),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use parser::sink::YulangLanguage;
    use rowan::SyntaxNode;
    use sources::Name;

    use super::*;

    fn render_input(src: &str) -> DocCommentRenderInput {
        let doc = value_doc(src);
        assert!(doc_comment_is_safe_for_yumark_literal_reparse(&doc));
        DocCommentRenderInput::from_safe_doc_comment(&doc)
    }

    fn value_doc(src: &str) -> DocComment {
        let cst = SyntaxNode::<YulangLanguage>::new_root(parser::parse_module_to_green(src));
        let lower = crate::module_map::lower_module_map_with_source(&cst, src);
        let root = lower.modules.root_id();
        let def = lower.modules.value_decls(root, &Name("x".into()))[0].def;
        lower
            .modules
            .def_doc_comment(def)
            .expect("doc comment should attach to x")
            .clone()
    }

    fn unit_contents(input: &DocCommentRenderInput) -> Vec<(DocCommentKind, &str)> {
        input
            .units()
            .iter()
            .map(|unit| (unit.kind(), unit.body_source()))
            .collect()
    }

    #[test]
    fn preserves_unit_sequence_and_exact_logical_body_sources() {
        let cases = [
            (
                "single line",
                "-- hello\nmy x = 1\n",
                vec![(DocCommentKind::Line, " hello")],
            ),
            (
                "multi-line block",
                "---\nfirst\nsecond\n---\nmy x = 1\n",
                // The CST keeps the terminal structural separator. Deciding
                // how it maps into a literal boundary belongs to Slice 5.
                vec![(DocCommentKind::Block, "\nfirst\nsecond\n\n")],
            ),
            (
                "heading",
                "---\n# Title\n---\nmy x = 1\n",
                vec![(DocCommentKind::Block, "\n# Title\n")],
            ),
            (
                "list",
                "---\n- one\n- two\n---\nmy x = 1\n",
                vec![(DocCommentKind::Block, "\n- one\n- two\n")],
            ),
            (
                "fence",
                "---\n```text\nalpha\nbeta\n```\n---\nmy x = 1\n",
                vec![(DocCommentKind::Block, "\n```text\nalpha\nbeta\n```\n")],
            ),
            (
                "quote",
                "---\n> quoted\n---\nmy x = 1\n",
                vec![(DocCommentKind::Block, "\n> quoted\n\n")],
            ),
            (
                "CRLF",
                "---\r\n# Title\r\n---\r\nmy x = 1\r\n",
                vec![(DocCommentKind::Block, "\r\n# Title\r\n")],
            ),
        ];

        for (name, src, expected) in cases {
            let input = render_input(src);
            let actual = unit_contents(&input);
            assert_eq!(actual, expected, "{name}");
        }

        assert_eq!(
            unit_contents(&render_input("-- first\n-- second\nmy x = 1\n")),
            vec![(DocCommentKind::Line, " first\nsecond")]
        );
    }

    #[test]
    fn content_key_has_cache_equality_and_hash_semantics() {
        let first = render_input("-- same text\nmy x = 1\n");
        let identical = render_input("-- same text\nmy x = 1\n");
        let different = render_input("-- different text\nmy x = 1\n");

        assert_eq!(first.key(), identical.key());
        assert_ne!(first.key(), different.key());

        let mut cache = HashMap::new();
        cache.insert(first.key().clone(), "rendered");
        assert_eq!(cache.get(identical.key()), Some(&"rendered"));
        assert_eq!(cache.get(different.key()), None);
    }
}
