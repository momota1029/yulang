#[path = "../../examples/support/nesting_cases.rs"]
mod cases;

#[test]
fn every_recursive_family_recovers_at_its_stack_budget_boundary() {
    crate::nesting::take_metrics();
    for &kind in cases::KINDS {
        for balanced in [true, false] {
            // Locate the build-specific byte-budget boundary using one fixed
            // call path. The boundary need not be the same in debug/release.
            let limited = |depth| cases::check(&cases::source(kind, depth, balanced));
            if matches!(kind, "yumark-inline" | "yumark-command") {
                let above = crate::nesting::ITERATIVE_LIMIT;
                assert!(!limited(above - 1), "{kind} below iterative limit");
                assert!(limited(above), "{kind} at iterative limit");
                eprintln!(
                    "BOUNDARY {kind} balanced={balanced}: {}/{}",
                    above - 1,
                    above
                );
                continue;
            }
            let mut above = 1;
            while above < 32_768 && !limited(above) {
                above *= 2;
            }
            assert!(limited(above), "unguarded {kind}");
            let mut below = 0;
            while above - below > 1 {
                let mid = (above + below) / 2;
                if limited(mid) {
                    above = mid;
                } else {
                    below = mid;
                }
            }
            assert!(!limited(below), "{kind} below boundary");
            assert!(limited(above), "{kind} above boundary");
            eprintln!("BOUNDARY {kind} balanced={balanced}: {below}/{above}");
        }
    }
    let (step, used) = crate::nesting::take_metrics();
    eprintln!(
        "STACK budget={} max_guard_gap={step} max_checked_use={used} remaining_512KiB={} gap_margin={:.2}",
        crate::nesting::STACK_BUDGET,
        512 * 1024 - used,
        (512 * 1024 - used) as f64 / step as f64
    );
    assert!(
        used + 4 * step < 512 * 1024,
        "four unchecked segments fit the reserve"
    );
}

#[test]
fn hundred_thousand_levels_exit_normally_in_subprocesses() {
    for small_stack in [false, true] {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "tests::nesting::subprocess_worker",
                "--nocapture",
            ])
            .env(
                "YULANG_NESTING_CHILD",
                if small_stack { "small" } else { "ordinary" },
            )
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "normal exit required, small_stack={small_stack}, status={}\n{}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn subprocess_worker() {
    let Ok(mode) = std::env::var("YULANG_NESTING_CHILD") else {
        return;
    };
    if mode == "small" {
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(stress_worker)
            .unwrap()
            .join()
            .unwrap();
    } else {
        stress_worker();
    }
}

#[test]
fn limited_regions_return_to_the_enclosing_sequence() {
    use crate::{SyntaxKind, SyntaxNode};
    for kind in [
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
        "mod",
        "use",
        "for",
        "case",
        "catch",
        "rule",
    ] {
        for balanced in [true, false] {
            let source = cases::source(kind, 1_024, balanced);
            assert!(cases::check(&source), "{kind}: exercised recovery");
            let parsed = cases::parse(&source);
            assert!(
                parsed
                    .source_root()
                    .syntax()
                    .children()
                    .any(|node| node.kind() == SyntaxKind::BindingStatement
                        && node.text().to_string() == "my after = 0"),
                "{kind} balanced={balanced}: following root binding survives"
            );
        }
    }
    for kind in [
        "parentheses",
        "brackets",
        "braces",
        "mixed",
        "list",
        "tuple",
    ] {
        let nested = cases::source(kind, 1_024, true);
        let nested = nested.strip_suffix("\nmy after = 0\n").unwrap();
        let source = format!("f({nested}, later)\n");
        assert!(cases::check(&source));
        let parsed = cases::parse(&source);
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert!(
            root.descendants_with_tokens()
                .filter_map(|e| e.into_token())
                .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == "later"),
            "{kind}: following call argument survives"
        );
    }
}

#[test]
fn unclosed_nested_yumark_commands_balance_output_before_the_limit() {
    let source = "---\n\\c{\\c{\\c{x\n---\nmy after = 0\n";
    assert!(!cases::check(source));
    let parsed = cases::parse(source);
    assert_eq!(
        parsed
            .source_root()
            .syntax()
            .children()
            .filter(|node| node.kind() == crate::SyntaxKind::BindingStatement)
            .count(),
        1
    );
}

fn stress_worker() {
    cases::stress();
    for balanced in [true, false] {
        let source = format!(
            "f: x,{}{}",
            ",".repeat(100_000),
            if balanced { "x" } else { "" }
        );
        let (green, _) = super::support::run(&source);
        assert_eq!(green.to_string(), source);
        let diagnostics = super::support::structural_diagnostics(&green);
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.message() == Some("nesting too deep"))
                .count(),
            1
        );
    }
}

#[test]
fn empty_colon_slots_without_a_sequence_owner_are_guarded() {
    for depth in [1, 100_000] {
        let source = format!("f: x,{}x", ",".repeat(depth));
        let (green, _) = super::support::run(&source);
        assert_eq!(green.to_string(), source);
        let diagnostics = super::support::structural_diagnostics(&green);
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.message() == Some("nesting too deep"))
                .count(),
            usize::from(depth == 100_000)
        );
    }
}

#[test]
fn foreign_yumark_prefixes_do_not_split_a_nesting_diagnostic() {
    use crate::SyntaxKind;
    let mut output = rowan::GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    output.start_node(SyntaxKind::NestingTooDeep.into());
    output.token(SyntaxKind::Error.into(), "(\n");
    output.token(SyntaxKind::YmQuotePrefix.into(), "> ");
    output.token(SyntaxKind::Error.into(), "(x)");
    output.finish_node();
    output.finish_node();
    let green = output.finish();
    let diagnostics = super::support::structural_diagnostics(&green);
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].message(), Some("nesting too deep"));
    assert_eq!(diagnostics[0].range(), &(0..7));
    assert_eq!(green.to_string(), "(\n> (x)");
}
