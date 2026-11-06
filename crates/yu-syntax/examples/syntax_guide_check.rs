//! Check the `yulang` code blocks of the syntax guide against the real parser.
//!
//! Run (from the repository root):
//!
//! ```text
//! cargo run -p yu-syntax --example syntax_guide_check -- syntax-guide/ja/src/
//! cargo run -p yu-syntax --example syntax_guide_check -- syntax-guide/ja/src/whitespace.md --tree
//! ```
//!
//! Arguments: one or more Markdown files or directories (directories are
//! scanned for `*.md`, non-recursively, in sorted order). `--tree` also prints
//! the full CST of every block. `--quiet` prints only the summary table.
//!
//! What it does:
//! - Extracts every fenced block whose info string is exactly `yulang`.
//!   Blocks inside a longer fence (e.g. a four-backtick `text` block that
//!   documents the directive format) are content of that fence and skipped.
//! - Reads an optional directive on the last non-blank line before the fence:
//!   `<!-- check: parse-ok -->` or `<!-- check: parse-error; shape: ... -->`.
//!   No directive means `parse-ok`. `shape:` is only echoed, not compared.
//! - Blocks containing the literal `...` are classified `placeholder`.
//! - Every other block is parsed as one whole source file with `parse_file`.
//!   The block's own leading operator declarations are honoured (via
//!   `scan_header`); in addition the file is parsed in an imported syntax
//!   environment built from `PRELUDE` below, a stand-in for the std prelude
//!   operator table (the real prelude does not exist on this branch).
//! - A block "has recovery" when `structural_recoveries()` or
//!   `syntax_diagnostics()` is non-empty.
//! - For each top-level statement it prints a compact shape of the CST
//!   (node kinds with token text as leaves, trivia removed) so a human can
//!   compare the grouping with the guide's comment. Note: the CST keeps an
//!   operator chain flat (`OperatorChain(a InfixOperatorUse(|) b ...)`), so
//!   infix precedence is NOT visible here; application (`MlArgument`,
//!   `CallTail`, `ColonApplicationTail`, `FieldTail`, ...) is. Records and
//!   blocks are both `BracedStatementBlockExpression`; only the separator
//!   token (`,` vs `;`) differs.
//!
//! Exit status: 1 if any block that should parse has recovery (or a
//! `parse-error` block parsed cleanly), otherwise 0.

use std::{
    fmt::Write as _,
    path::{Path, PathBuf},
    sync::Arc,
};

use yu_syntax::{
    HeaderInfo, SourceRevision, SyntaxDependencyProvenance, SyntaxDependencySlot,
    SyntaxDiagnosticCause, SyntaxEnvironment, SyntaxEnvironmentKey, SyntaxKind, SyntaxNode,
    parse_file, scan_header,
};

/// Stand-in prelude operator table. Binding powers: bigger binds tighter.
/// `|` is the weakest (spec 3.9); `not` / `+` / suffix `..` use the values
/// shown in spec 1.5; the rest are plausible guesses.
const PRELUDE: &str = "\
pub infix (|) 1.0.0 1.0.1 = pipe
pub lazy infix (or) 2.0.0 2.0.1 = or
pub lazy infix (and) 3.0.0 3.0.1 = and
pub infix (==) 4.0.0 4.0.1 = eq
pub infix (<) 4.0.0 4.0.1 = lt
pub infix (..) 4.5.0 4.5.1 = range
pub infix (+) 5.0.0 5.0.1 = add
pub infix (-) 5.0.0 5.0.1 = sub
pub infix (*) 6.0.0 6.0.1 = mul
pub prefix (-) 8.0.0 = neg
pub prefix (not) 8.0.0 = not
pub suffix (..) 8.0.0 = from
";

#[derive(Clone, Copy, PartialEq, Eq)]
enum Expect {
    Ok,
    Error,
}

struct Block {
    file: PathBuf,
    /// 1-based Markdown line of the first content line.
    line: usize,
    directive: Option<String>,
    expect: Expect,
    code: String,
}

struct Row {
    file: String,
    line: usize,
    status: &'static str,
    detail: String,
}

fn main() {
    let mut paths = Vec::new();
    let (mut tree, mut quiet) = (false, false);
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--tree" => tree = true,
            "--quiet" => quiet = true,
            _ => paths.push(PathBuf::from(arg)),
        }
    }
    if paths.is_empty() {
        eprintln!("usage: syntax_guide_check <file.md|dir>... [--tree] [--quiet]");
        std::process::exit(2);
    }

    let mut rows = Vec::new();
    for file in markdown_files(&paths) {
        let text = std::fs::read_to_string(&file).expect("read markdown file");
        for block in extract_blocks(&file, &text) {
            rows.push(check(&block, tree, quiet));
        }
    }

    println!("\n== summary ==");
    println!("{:<16} {:>5}  {:<11} detail", "file", "line", "status");
    for row in &rows {
        println!(
            "{:<16} {:>5}  {:<11} {}",
            row.file, row.line, row.status, row.detail
        );
    }
    let count = |s: &str| rows.iter().filter(|r| r.status == s).count();
    println!(
        "\ntotal {}: ok {}, recovery {}, unexpected-ok {}, expected-error {}, placeholder {}",
        rows.len(),
        count("ok"),
        count("recovery"),
        count("unexpected-ok"),
        count("expected-err"),
        count("placeholder"),
    );
    if count("recovery") + count("unexpected-ok") > 0 {
        std::process::exit(1);
    }
}

/// Builds the imported environment from `PRELUDE`, leaving out every prelude
/// line whose fixity and spelling the block declares itself (otherwise the
/// parser reports `ConflictingOperatorFixity` for the block's own
/// declarations, which is an artefact of this tool, not of the guide).
fn prelude_environment(local: &HeaderInfo) -> SyntaxEnvironment {
    let declared: Vec<String> = local
        .operators()
        .iter()
        .map(|op| {
            format!(
                "{} ({})",
                format!("{:?}", op.fixity()).to_lowercase(),
                op.name()
            )
        })
        .collect();
    let prelude: String = PRELUDE
        .lines()
        .filter(|line| !declared.iter().any(|d| line.contains(d.as_str())))
        .map(|line| format!("{line}\n"))
        .collect();
    let header = scan_header(Arc::from(prelude.as_str()));
    assert_eq!(
        header.operators().len(),
        prelude.lines().count(),
        "prelude header scan"
    );
    let slot = SyntaxDependencySlot::from_index(0).unwrap();
    let provenance = Arc::from([SyntaxDependencyProvenance::new(
        Arc::from("guide-prelude"),
        SourceRevision::UNTRACKED,
    )]);
    SyntaxEnvironment::from_imported_headers(
        SyntaxEnvironmentKey::from_fingerprint(1),
        [(slot, &header)],
        provenance,
    )
    .expect("prelude environment")
}

fn markdown_files(paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for path in paths {
        if path.is_dir() {
            let mut entries: Vec<_> = std::fs::read_dir(path)
                .expect("read dir")
                .filter_map(|e| e.ok().map(|e| e.path()))
                .filter(|p| p.extension().is_some_and(|x| x == "md"))
                .collect();
            entries.sort();
            out.extend(entries);
        } else {
            out.push(path.clone());
        }
    }
    out
}

/// Extracts `yulang` fences. A fence opened with N backticks closes only on a
/// line of at least N backticks, so nested fences inside a longer one are
/// treated as plain content.
fn extract_blocks(file: &Path, text: &str) -> Vec<Block> {
    let lines: Vec<&str> = text.lines().collect();
    let mut blocks = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim_start();
        let ticks = trimmed.chars().take_while(|&c| c == '`').count();
        if ticks < 3 {
            i += 1;
            continue;
        }
        let info = trimmed[ticks..].trim();
        let start = i + 1;
        let mut end = start;
        while end < lines.len() {
            let t = lines[end].trim();
            if t.len() >= ticks && t.chars().all(|c| c == '`') {
                break;
            }
            end += 1;
        }
        if info == "yulang" {
            let directive = lines[..i]
                .iter()
                .rev()
                .find(|l| !l.trim().is_empty())
                .and_then(|l| parse_directive(l));
            let expect = match &directive {
                Some(d) if d.contains("parse-error") => Expect::Error,
                _ => Expect::Ok,
            };
            let mut code = lines[start..end.min(lines.len())].join("\n");
            code.push('\n');
            blocks.push(Block {
                file: file.to_path_buf(),
                line: start + 1,
                directive,
                expect,
                code,
            });
        }
        i = end + 1;
    }
    blocks
}

fn parse_directive(line: &str) -> Option<String> {
    let inner = line
        .trim()
        .strip_prefix("<!--")?
        .strip_suffix("-->")?
        .trim();
    Some(inner.strip_prefix("check:")?.trim().to_string())
}

fn check(block: &Block, tree: bool, quiet: bool) -> Row {
    let name = block
        .file
        .file_name()
        .unwrap()
        .to_string_lossy()
        .into_owned();
    let first = block.code.lines().next().unwrap_or("").trim().to_string();
    let mut row = Row {
        file: name.clone(),
        line: block.line,
        status: "ok",
        detail: first,
    };
    if !quiet {
        println!("--- {}:{} ---", block.file.display(), block.line);
        if let Some(d) = &block.directive {
            println!("directive: {d}");
        }
        print!("{}", block.code);
    }
    if block.code.contains("...") {
        row.status = "placeholder";
        row.detail = format!("contains `...`: {}", row.detail);
        if !quiet {
            println!("=> placeholder (not parsed)\n");
        }
        return row;
    }

    let source: Arc<str> = Arc::from(block.code.as_str());
    let header = Arc::new(scan_header(source.clone()));
    let env = Arc::new(prelude_environment(&header));
    let parsed = parse_file(source.clone(), header, env);
    let recoveries = parsed.structural_recoveries();
    let diagnostics = parsed.syntax_diagnostics();
    let root = SyntaxNode::new_root(parsed.green().clone());

    let mut problems = Vec::new();
    for r in &recoveries {
        problems.push(format!(
            "recovery {:?} at {} {:?} path={:?}",
            r.kind(),
            position(&block.code, block.line, r.range().start),
            &block.code[r.range().clone()],
            r.path()
        ));
    }
    match &diagnostics {
        Ok(list) => {
            for d in list {
                let mut s = format!(
                    "diagnostic {:?} at {} {:?}",
                    d.identity().kind(),
                    position(&block.code, block.line, d.primary().start),
                    &block.code[d.primary().clone()],
                );
                if let Some(slot) = d.identity().slot() {
                    let _ = write!(s, " slot={:?}/{:?}", slot.owner(), slot.role());
                }
                if let SyntaxDiagnosticCause::Structural(sd) = d.cause() {
                    if let Some(exp) = sd.expectations() {
                        let _ = write!(s, " expected={exp:?}");
                    }
                }
                problems.push(s);
            }
        }
        Err(e) => problems.push(format!("syntax_diagnostics() failed: {e:?}")),
    }

    let has_problem = !problems.is_empty();
    row.status = match (block.expect, has_problem) {
        (Expect::Ok, false) => "ok",
        (Expect::Ok, true) => "recovery",
        (Expect::Error, true) => "expected-err",
        (Expect::Error, false) => "unexpected-ok",
    };
    if let Some(first_problem) = problems.first() {
        row.detail = format!("{} ({} issue(s))", first_problem, problems.len());
    }

    if !quiet {
        for p in &problems {
            println!("  {p}");
        }
        for stmt in root.children() {
            let start = usize::from(stmt.text_range().start());
            println!(
                "  shape@{}: {}",
                position(&block.code, block.line, start),
                shape(&stmt)
            );
        }
        if tree {
            println!("{root:#?}");
        }
        println!("=> {}\n", row.status);
    }
    row
}

/// `md-line:col` of a byte offset inside the block.
fn position(code: &str, first_line: usize, offset: usize) -> String {
    let before = &code[..offset.min(code.len())];
    let line = before.matches('\n').count();
    let col = before.rsplit('\n').next().unwrap_or("").chars().count() + 1;
    format!("L{}:{}", first_line + line, col)
}

/// Compact S-expression of a node: `Kind(child child ...)`, with non-trivia
/// tokens shown as their text. Single-child wrapper nodes are kept so that
/// grouping stays visible.
fn shape(node: &SyntaxNode) -> String {
    let mut out = format!("{:?}(", node.kind());
    let mut first = true;
    for child in node.children_with_tokens() {
        let piece = match child {
            rowan::NodeOrToken::Node(n) => shape(&n),
            rowan::NodeOrToken::Token(t) => {
                if matches!(
                    t.kind(),
                    SyntaxKind::Whitespace
                        | SyntaxKind::Newline
                        | SyntaxKind::LineComment
                        | SyntaxKind::BlockComment
                ) {
                    continue;
                }
                format!("{:?}", t.text())
            }
        };
        if !first {
            out.push(' ');
        }
        first = false;
        out.push_str(&piece);
    }
    out.push(')');
    out
}
