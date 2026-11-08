//! Shared adversarial inputs for the in-process and subprocess stack contracts.
use std::sync::Arc;
use yu_syntax::{ParsedFile, SyntaxDiagnosticCause, SyntaxEnvironment, parse_file, scan_header};

pub const KINDS: &[&str] = &[
    "parentheses",
    "brackets",
    "braces",
    "mixed",
    "lambda",
    "if",
    "indent",
    "list",
    "record",
    "tuple",
    "type-call",
    "type-apply",
    "type-arrow",
    "type-tuple",
    "type-record",
    "pattern",
    "pattern-list",
    "pattern-record",
    "pattern-alternation",
    "yumark-inline",
    "yumark-command",
    "yumark-embedded",
    "mod",
    "use",
    "interpolation",
    "rule",
    "rule-capture",
    "for",
    "case",
    "catch",
    "access",
    "type-access",
    "pattern-access",
    "derives",
];

pub fn source(kind: &str, depth: usize, balanced: bool) -> String {
    if kind == "yumark-empty-arguments" {
        return format!(
            "---\n\\if(say: x{}{}\n---\nmy after = 0\n",
            ",".repeat(depth),
            if balanced { "x){body}" } else { "" }
        );
    }
    if kind == "indent" {
        let mut source = String::new();
        for level in 0..depth {
            source.extend(std::iter::repeat_n(' ', level));
            source.push_str("say:\n");
        }
        if balanced {
            source.extend(std::iter::repeat_n(' ', depth));
            source.push_str("x\n");
        }
        source.push_str("my after = 0\n");
        return source;
    }
    let (header, open, atom, close, trailer) = match kind {
        "parentheses" => ("", "(", "x", ")", ""),
        "brackets" => ("", "[", "x", "]", ""),
        "braces" => ("", "{", "x", "}", ""),
        "mixed" => ("", "([{", "x", "}])", ""),
        "lambda" => ("", "\\x -> ", "x", "", ""),
        "if" => ("", "if c: ", "x", " else y", ""),
        "list" => ("", "[x, ", "x", "]", ""),
        "record" => ("", "{ a = ", "x", "}", ""),
        "tuple" => ("", "(x, ", "x", ")", ""),
        "type-call" => ("type T = ", "F(", "T", ")", ""),
        "type-apply" => ("type T = ", "F (", "T", ")", ""),
        "type-arrow" => ("type T = ", "T -> ", "T", "", ""),
        "type-tuple" => ("type T = ", "(T, ", "T", ")", ""),
        "type-record" => ("type T = ", "{ a: ", "T", "}", ""),
        "pattern" => ("my ", "(", "x", ")", " = x"),
        "pattern-list" => ("my ", "[", "x", "]", " = x"),
        "pattern-record" => ("my ", "{ a = ", "x", "}", " = x"),
        "pattern-alternation" => ("my ", "x | ", "x", "", " = x"),
        "yumark-inline" => ("--", "[", "x", "]", ""),
        "yumark-command" => ("---\n", "\\c{", "x", "}", "\n---"),
        "yumark-embedded" => ("--", "\\ref({--", "x", "})", ""),
        "mod" => ("", "mod a {", "x", "}", ""),
        "use" => ("use ", "{", "a", "}", ""),
        "interpolation" => ("", "\"%{", "x", "}\"", ""),
        "rule" => ("rule {", "(", "x", ")", "}"),
        "rule-capture" => ("rule {", "x = ", "x", "", "}"),
        "for" => ("", "for x in xs: ", "x", "", ""),
        "case" => ("", "case x { A -> ", "x", "}", ""),
        "catch" => ("", "catch x { A -> ", "x", "}", ""),
        "colon-arguments" => ("say: ", "x, ", "x", "", ""),
        "access" => ("x", ".x", "", "", ""),
        "type-access" => ("type T = T", "::T", "", "", ""),
        "pattern-access" => ("my x", "::x", "", "", " = x"),
        "derives" => ("type T ", "derives X ", "", "", " = T"),
        _ => panic!("unknown nesting kind {kind}"),
    };
    let mut source = String::from(header);
    source.push_str(&open.repeat(depth));
    if balanced || !close.is_empty() {
        source.push_str(atom);
    }
    if balanced {
        source.push_str(&close.repeat(depth));
    }
    source.push_str(trailer);
    source.push_str("\nmy after = 0\n");
    source
}

#[inline(never)]
pub fn parse(source: &str) -> ParsedFile {
    let source: Arc<str> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
}

pub fn check(source: &str) -> bool {
    let parsed = parse(source);
    let root = parsed.source_root();
    let mut offset = 0;
    for token in root
        .syntax()
        .descendants_with_tokens()
        .filter_map(|e| e.into_token())
    {
        let text = token.text();
        assert_eq!(text, &source[offset..offset + text.len()]);
        assert_eq!(usize::from(token.text_range().start()), offset);
        offset += text.len();
    }
    assert_eq!(offset, source.len(), "lossless CST");
    let diagnostics = parsed
        .syntax_diagnostics()
        .expect("total diagnostic projection");
    let limited = diagnostics
        .iter()
        .filter(|diagnostic| {
            matches!(diagnostic.cause(),
        SyntaxDiagnosticCause::Structural(s) if s.message() == Some("nesting too deep"))
        })
        .count();
    let regions = root
        .syntax()
        .descendants()
        .filter(|node| node.kind() == yu_syntax::SyntaxKind::NestingTooDeep)
        .count();
    assert_eq!(limited, regions, "one nesting diagnostic per opaque region");
    limited != 0
}

pub fn stress() {
    for balanced in [true, false] {
        check(&source("yumark-empty-arguments", 100_000, balanced));
    }
    let flat = format!("type T = F {}T\n", "arg ".repeat(100_000));
    assert!(!check(&flat), "flat type arguments remain iterative");
    for &kind in KINDS {
        // See notes/questions/2026-11-08-recovery-p0-indentation-stress.md:
        // 100,000 strictly increasing columns cannot fit Rowan's TextSize.
        let depth = if kind == "indent" { 1_024 } else { 100_000 };
        for balanced in [true, false] {
            eprintln!("STRESS {kind} depth={depth} balanced={balanced}");
            let limited = check(&source(kind, depth, balanced));
            assert!(limited, "{kind} did not reach a nesting guard");
        }
    }
}
