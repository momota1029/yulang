//! Static Yumark doc-comment rendering for editor features.
//!
//! This renderer intentionally walks doc-comment CST directly instead of
//! evaluating `std::text::yumark`. Unknown Yumark constructs fall back to their
//! raw source text so hover can show unsupported commands honestly instead of
//! dropping them.

use parser::lex::SyntaxKind;
use parser::sink::YulangLanguage;
use rowan::{NodeOrToken, SyntaxNode};

use crate::{DocComment, DocCommentKind, DocCommentUnit};

type Cst = SyntaxNode<YulangLanguage>;

pub fn render_doc_comment_markdown(doc: &DocComment) -> String {
    doc.units().iter().map(render_doc_unit_markdown).collect()
}

#[derive(Clone, Copy)]
struct SequenceOptions {
    include_newlines: bool,
    trim_trailing_line_breaks: bool,
}

impl SequenceOptions {
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

fn render_doc_unit_markdown(unit: &DocCommentUnit) -> String {
    let mut rendered = String::new();
    for doc in unit
        .node()
        .children()
        .filter(|child| child.kind() == SyntaxKind::YmDoc)
    {
        rendered.push_str(&render_yumark_node(&doc));
    }
    if rendered.is_empty() {
        unit.node().text().to_string()
    } else {
        trim_doc_comment_boundary(&mut rendered, unit.kind());
        rendered
    }
}

fn render_yumark_node(node: &Cst) -> String {
    match node.kind() {
        SyntaxKind::YmDoc => render_sequence(node, SequenceOptions::INLINE),
        SyntaxKind::YmParagraph => {
            let mut rendered = render_sequence(node, SequenceOptions::BLOCK_CONTENT);
            rendered.push_str("\n\n");
            rendered
        }
        SyntaxKind::YmEmphasis => {
            let mut rendered = String::from("*");
            rendered.push_str(&render_sequence(node, SequenceOptions::INLINE));
            rendered.push('*');
            rendered
        }
        SyntaxKind::YmStrong => {
            let mut rendered = String::from("**");
            rendered.push_str(&render_sequence(node, SequenceOptions::INLINE));
            rendered.push_str("**");
            rendered
        }
        SyntaxKind::YmHeading => render_heading(node),
        SyntaxKind::YmBlankLine => "\n".to_string(),
        SyntaxKind::YmSectionClose => render_section_close(node),
        SyntaxKind::YmList => {
            let mut rendered = render_sequence(node, SequenceOptions::INLINE);
            rendered.push('\n');
            rendered
        }
        SyntaxKind::YmListItem => render_list_item(node),
        SyntaxKind::YmListItemBody => render_sequence(node, SequenceOptions::BLOCK_CONTENT),
        SyntaxKind::YmCodeFence => render_code_fence(node),
        SyntaxKind::YmQuoteBlock => {
            let mut rendered = String::from("> ");
            rendered.push_str(&render_sequence(node, SequenceOptions::INLINE));
            rendered.push('\n');
            rendered
        }
        _ => node.text().to_string(),
    }
}

fn render_heading(node: &Cst) -> String {
    let Some(marker) = token_text(node, &[SyntaxKind::YmHashSigil]) else {
        return node.text().to_string();
    };
    let mut rendered = marker;
    rendered.push_str(&render_sequence(node, SequenceOptions::LINE_CONTENT));
    rendered.push_str("\n\n");
    rendered
}

fn render_section_close(node: &Cst) -> String {
    let Some(marker) = token_text(node, &[SyntaxKind::YmHashDotSigil]) else {
        return node.text().to_string();
    };
    let mut rendered = marker;
    rendered.push_str(&render_sequence(node, SequenceOptions::LINE_CONTENT));
    rendered.push('\n');
    rendered
}

fn render_list_item(node: &Cst) -> String {
    let Some(marker) = token_text(
        node,
        &[SyntaxKind::YmListDashSigil, SyntaxKind::YmListNumSigil],
    ) else {
        return node.text().to_string();
    };
    let mut children = render_sequence(node, SequenceOptions::BLOCK_CONTENT);
    trim_trailing_line_breaks(&mut children);
    let mut rendered = marker;
    rendered.push_str(&children);
    rendered.push('\n');
    rendered
}

fn render_code_fence(node: &Cst) -> String {
    let text = node.text().to_string();
    let Some((info, body)) = split_code_fence_node_text(&text) else {
        return text;
    };
    let mut rendered = String::from("```");
    rendered.push_str(&info);
    rendered.push('\n');
    rendered.push_str(&body);
    rendered.push_str("\n```\n\n");
    rendered
}

fn render_sequence(node: &Cst, options: SequenceOptions) -> String {
    let mut rendered = String::new();
    let mut text = String::new();
    let mut skip_newlines_after_child = false;
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) => {
                let kind = token.kind();
                if skip_newlines_after_child && kind == SyntaxKind::YmNewline {
                    continue;
                }
                skip_newlines_after_child = false;
                if token_is_yumark_text(kind, options.include_newlines) {
                    text.push_str(token.text());
                } else if token_is_yumark_syntax(kind) {
                    continue;
                } else {
                    text.push_str(token.text());
                }
            }
            NodeOrToken::Node(child) => {
                if is_empty_yumark_paragraph(&child) {
                    continue;
                }
                flush_text(&mut rendered, &mut text, options);
                if is_supported_yumark_node(child.kind()) {
                    let child_rendered = render_yumark_node(&child);
                    skip_newlines_after_child =
                        child_rendered.ends_with('\n') || child_rendered.ends_with('\r');
                    rendered.push_str(&child_rendered);
                } else {
                    let raw = child.text().to_string();
                    skip_newlines_after_child = raw.ends_with('\n') || raw.ends_with('\r');
                    rendered.push_str(&raw);
                }
            }
        }
    }
    flush_text(&mut rendered, &mut text, options);
    rendered
}

fn trim_doc_comment_boundary(rendered: &mut String, kind: DocCommentKind) {
    match kind {
        DocCommentKind::Line => {
            if rendered.starts_with(' ') {
                rendered.drain(..1);
            }
        }
        DocCommentKind::Block => {
            while rendered.starts_with("\r\n") {
                rendered.drain(..2);
            }
            while rendered.starts_with('\n') {
                rendered.drain(..1);
            }
        }
    }
}

fn is_supported_yumark_node(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::YmDoc
            | SyntaxKind::YmParagraph
            | SyntaxKind::YmEmphasis
            | SyntaxKind::YmStrong
            | SyntaxKind::YmHeading
            | SyntaxKind::YmBlankLine
            | SyntaxKind::YmSectionClose
            | SyntaxKind::YmList
            | SyntaxKind::YmListItem
            | SyntaxKind::YmListItemBody
            | SyntaxKind::YmCodeFence
            | SyntaxKind::YmQuoteBlock
    )
}

fn flush_text(rendered: &mut String, text: &mut String, options: SequenceOptions) {
    if options.trim_trailing_line_breaks {
        trim_trailing_line_breaks(text);
    }
    if !text.is_empty() {
        rendered.push_str(text);
        text.clear();
    }
}

fn token_text(node: &Cst, kinds: &[SyntaxKind]) -> Option<String> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| kinds.contains(&token.kind()))
        .map(|token| token.text().to_string())
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

fn is_empty_yumark_paragraph(node: &Cst) -> bool {
    node.kind() == SyntaxKind::YmParagraph
        && node.children_with_tokens().all(|item| match item {
            NodeOrToken::Token(token) => {
                token_is_yumark_syntax(token.kind()) || token_is_line_break_space(&token)
            }
            NodeOrToken::Node(child) => is_empty_yumark_paragraph(&child),
        })
}

fn token_is_line_break_space(token: &rowan::SyntaxToken<YulangLanguage>) -> bool {
    token.kind() == SyntaxKind::Space && token.text().chars().all(|ch| matches!(ch, '\n' | '\r'))
}

fn token_is_yumark_text(kind: SyntaxKind, include_newlines: bool) -> bool {
    matches!(kind, SyntaxKind::YmText | SyntaxKind::Space)
        || (include_newlines && kind == SyntaxKind::YmNewline)
}

fn token_is_yumark_syntax(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::DocComment
            | SyntaxKind::MarkLitStart
            | SyntaxKind::MarkLitEnd
            | SyntaxKind::YmStarSigil
            | SyntaxKind::YmStrongSigil
            | SyntaxKind::YmHashSigil
            | SyntaxKind::YmHashDotSigil
            | SyntaxKind::YmListDashSigil
            | SyntaxKind::YmListNumSigil
            | SyntaxKind::YmChevronPrefixSigil
            | SyntaxKind::YmFenceSigil
            | SyntaxKind::YmDocBlockSigil
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
mod tests {
    use super::*;

    use sources::Name;

    fn render_value_doc(src: &str) -> String {
        let cst = SyntaxNode::new_root(parser::parse_module_to_green(src));
        let lower = crate::module_map::lower_module_map_with_source(&cst, src);
        let root = lower.modules.root_id();
        let def = lower.modules.value_decls(root, &Name("x".into()))[0].def;
        let doc = lower
            .modules
            .def_doc_comment(def)
            .expect("doc comment should attach to x");
        render_doc_comment_markdown(doc)
    }

    #[test]
    fn renders_line_doc_paragraph_text() {
        assert_eq!(
            render_value_doc("-- hello world\nmy x = 1\n"),
            "hello world\n\n"
        );
    }

    #[test]
    fn renders_consecutive_line_doc_units_in_source_order() {
        assert_eq!(
            render_value_doc("-- first\n-- second\nmy x = 1\n"),
            "first\n\nsecond\n\n"
        );
    }

    #[test]
    fn renders_emphasis() {
        assert_eq!(render_value_doc("-- *soft*\nmy x = 1\n"), "*soft*\n\n");
    }

    #[test]
    fn renders_strong() {
        assert_eq!(render_value_doc("-- **loud**\nmy x = 1\n"), "**loud**\n\n");
    }

    #[test]
    fn renders_heading() {
        assert_eq!(
            render_value_doc("---\n## Title\n---\nmy x = 1\n"),
            "## Title\n\n"
        );
    }

    #[test]
    fn renders_blank_line_between_paragraphs() {
        assert_eq!(
            render_value_doc("---\nfirst\n\nsecond\n---\nmy x = 1\n"),
            "first\n\n\nsecond\n\n"
        );
    }

    #[test]
    fn renders_section_close() {
        assert_eq!(render_value_doc("---\n#.\n---\nmy x = 1\n"), "#.\n");
    }

    #[test]
    fn renders_list_block_items_and_bodies() {
        assert_eq!(
            render_value_doc("---\n- one\n- *two*\n---\nmy x = 1\n"),
            "- one\n\n- *two*\n\n"
        );
    }

    #[test]
    fn renders_code_fence_with_raw_body() {
        assert_eq!(
            render_value_doc("---\n```text\nalpha\nbeta\n```\n---\nmy x = 1\n"),
            "```text\nalpha\nbeta\n```\n\n"
        );
    }

    #[test]
    fn renders_yulang_code_fence_body_as_raw_source() {
        assert_eq!(
            render_value_doc("---\n```yulang\nmy inside = 1\ninside\n```\n---\nmy x = 1\n"),
            "```yulang\nmy inside = 1\ninside\n```\n\n"
        );
    }

    #[test]
    fn renders_quote_block() {
        assert_eq!(
            render_value_doc("---\n> quoted\n---\nmy x = 1\n"),
            "> quoted\n\n\n"
        );
    }

    #[test]
    fn renders_rich_combined_doc_comment() {
        assert_eq!(
            render_value_doc(
                "---\n# Title\nA *soft* and **strong** paragraph.\n\n- item one\n- item **two**\n```text\nbody\n```\n> quoted\n#.\n---\nmy x = 1\n",
            ),
            "# Title\n\nA *soft* and **strong** paragraph.\n\n\n- item one\n\n- item **two**\n\n```text\nbody\n```\n\n> quoted\n\n\n#.\n"
        );
    }

    #[test]
    fn unsupported_command_like_text_renders_as_raw_text() {
        assert_eq!(
            render_value_doc("---\n\\cmd()\n---\nmy x = 1\n"),
            "\\cmd()\n\n"
        );
    }

    #[test]
    fn unsupported_inline_expr_node_renders_as_raw_text() {
        assert_eq!(
            render_value_doc("-- ![alt](url)\nmy x = 1\n"),
            "![alt](url)\n\n"
        );
    }
}
