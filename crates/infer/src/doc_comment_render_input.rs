//! Owned, cache-ready input for lazy Yumark doc-comment rendering.
//!
//! This module preserves source fragments without deciding how to join or
//! delimit them. Synthetic ordinary-literal construction belongs to the next
//! mapping stage.

use parser::lex::SyntaxKind;

use crate::doc_comment_render::doc_comment_is_safe_for_yumark_literal_reparse;
use crate::{DocComment, DocCommentKind, DocCommentUnit};

/// An owned safe-subset doc comment awaiting Yumark literal construction.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DocCommentRenderInput {
    key: DocCommentRenderInputKey,
}

impl DocCommentRenderInput {
    /// Copy the exact body fragments of a doc comment accepted by the Slice 1
    /// safe-subset check.
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

/// One doc-comment unit with its delimiter-free, unnormalized source body.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DocCommentRenderInputUnit {
    kind: DocCommentKind,
    body_source: String,
}

impl DocCommentRenderInputUnit {
    pub fn kind(&self) -> DocCommentKind {
        self.kind
    }

    pub fn body_source(&self) -> &str {
        &self.body_source
    }

    fn from_doc_comment_unit(unit: &DocCommentUnit) -> Self {
        let mut body_source = String::new();
        for doc in unit
            .node()
            .children()
            .filter(|child| child.kind() == SyntaxKind::YmDoc)
        {
            body_source.push_str(&doc.text().to_string());
        }
        Self {
            kind: unit.kind(),
            body_source,
        }
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
    fn preserves_unit_sequence_and_exact_unmapped_body_sources() {
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
            vec![
                (DocCommentKind::Line, " first"),
                (DocCommentKind::Line, " second"),
            ]
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
