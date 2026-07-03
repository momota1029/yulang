use std::collections::BTreeSet;

use parser::lex::SyntaxKind;
use parser::sink::YulangLanguage;
use rowan::SyntaxNode;

fn parse_module(source: &str) -> SyntaxNode<YulangLanguage> {
    SyntaxNode::<YulangLanguage>::new_root(parser::parse_module_to_green_with_ops(
        source,
        parser::op::standard_op_table(),
    ))
}

fn has_invalid_token(root: &SyntaxNode<YulangLanguage>) -> bool {
    root.descendants()
        .any(|node| node.kind() == SyntaxKind::InvalidToken)
}

#[test]
fn parse_module_recovers_incomplete_eof_forms() {
    let cases = [
        ("unterminated string", "my message = \"unterminated", true),
        ("trailing path separator", "my y = std::foo::", true),
        ("unterminated block doc", "---", false),
        ("nested unclosed groups", "my xs = ([std::foo::", true),
        ("lambda intro at eof", "my f = \\", true),
        ("string escape at eof", "my s = \"abc\\", true),
    ];

    for (name, source, expect_invalid) in cases {
        let root = parse_module(source);
        assert_eq!(root.text().to_string(), source, "{name}");
        if expect_invalid {
            assert!(has_invalid_token(&root), "{name} should leave InvalidToken");
        }
    }
}

#[test]
fn parse_module_prefix_totality_for_representative_fixtures() {
    let fixtures = [
        (
            "runtime/result_api.yu",
            include_str!("../../../tests/yulang/regressions/runtime/result_api.yu"),
        ),
        (
            "runtime/file_text_with_commit.yu",
            include_str!("../../../tests/yulang/regressions/runtime/file_text_with_commit.yu"),
        ),
        (
            "adversarial/parameterized_effect_capture.yu",
            include_str!(
                "../../../tests/yulang/yulang-adversarial-corpus/03_parameterized_effect_capture.yu"
            ),
        ),
    ];

    for (name, source) in fixtures {
        for byte in sampled_char_boundaries(source) {
            let prefix = &source[..byte];
            let parsed = std::panic::catch_unwind(|| {
                let _ =
                    parser::parse_module_to_green_with_ops(prefix, parser::op::standard_op_table());
            });
            assert!(
                parsed.is_ok(),
                "{name} prefix ending at byte {byte} panicked; tail: {:?}",
                tail_context(prefix)
            );
        }
    }
}

fn sampled_char_boundaries(source: &str) -> Vec<usize> {
    let mut boundaries = source
        .char_indices()
        .map(|(byte, _)| byte)
        .chain(std::iter::once(source.len()))
        .collect::<Vec<_>>();
    boundaries.dedup();

    if boundaries.len() <= 2_000 {
        return boundaries;
    }

    let mut sampled = BTreeSet::new();
    let last = boundaries.len() - 1;
    for n in 0..2_000 {
        sampled.insert(boundaries[n * last / 1_999]);
    }
    for byte in boundaries.iter().rev().take(200) {
        sampled.insert(*byte);
    }
    sampled.into_iter().collect()
}

fn tail_context(source: &str) -> String {
    let tail = source.chars().rev().take(40).collect::<Vec<_>>();
    tail.into_iter().rev().collect()
}
