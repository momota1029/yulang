//! Read-only LS recovery audit. Run from the repository root, offline, in release.
//! No fingerprints are generated or updated. See notes/audit/ls-recovery-audit.md.
#[allow(dead_code)]
#[path = "support/recovery_corpus.rs"]
mod corpus;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};
use yu_syntax::{ParsedFile, SyntaxDiagnosticCause, SyntaxKind as K, SyntaxNode};

fn trivia(k: K) -> bool {
    matches!(
        k,
        K::Whitespace | K::Newline | K::LineComment | K::BlockComment
    )
}

// Compare structure and significant spelling, ignoring trivia ownership at EOF.
fn shape(n: &SyntaxNode) -> String {
    let mut s = String::new();
    for e in n.preorder_with_tokens() {
        match e {
            rowan::WalkEvent::Enter(e) if !trivia(e.kind()) => {
                s.push_str(&format!("({:?}", e.kind()));
                if let Some(t) = e.as_token() {
                    s.push_str(&format!("{:?}", t.text()));
                }
            }
            rowan::WalkEvent::Leave(e) if !trivia(e.kind()) => s.push(')'),
            _ => {}
        }
    }
    s
}

#[derive(Clone)]
struct Statement {
    start: usize,
    end: usize,
    signature: String,
    nested: bool,
}

fn statements(root: &SyntaxNode) -> Vec<Statement> {
    root.descendants()
        .filter(|n| n.parent().is_some_and(|p| p.kind() == K::Root) || n.kind() == K::Statement)
        .filter_map(|n| {
            let tokens: Vec<_> = n
                .descendants_with_tokens()
                .filter_map(|e| e.into_token())
                .filter(|t| !trivia(t.kind()) && !t.text().is_empty())
                .collect();
            let start = usize::from(tokens.first()?.text_range().start());
            let end = usize::from(tokens.last()?.text_range().end());
            let parents: Vec<_> = n.ancestors().skip(1).map(|p| p.kind()).collect();
            Some(Statement {
                start,
                end,
                signature: format!("{parents:?}:{}", shape(&n)),
                nested: n.parent().unwrap().kind() != K::Root,
            })
        })
        .collect()
}

#[derive(Default)]
struct Stats {
    parses: usize,
    panics: usize,
    loss: usize,
    token_ranges: usize,
    diagnostic_errors: usize,
    over_100ms: usize,
    max_us: u128,
    max_case: String,
}

struct Auditor {
    stats: Stats,
    active: Arc<Mutex<(Instant, String)>>,
}

impl Auditor {
    fn parse(&mut self, case: &corpus::Case, code: &str, label: &str) -> Option<ParsedFile> {
        let name = format!("{} {label}", case.name);
        *self.active.lock().unwrap() = (Instant::now(), name.clone());
        self.stats.parses += 1;
        let begin = Instant::now();
        let result = std::panic::catch_unwind(|| {
            let p = corpus::parse(case, code);
            let root = SyntaxNode::new_root(p.green().clone());
            let loss = root.to_string() != code;
            let ranges = root
                .descendants_with_tokens()
                .filter_map(|e| e.into_token())
                .any(|t| {
                    code.get(usize::from(t.text_range().start())..usize::from(t.text_range().end()))
                        != Some(t.text())
                });
            (p, loss, ranges)
        });
        let us = begin.elapsed().as_micros();
        if us > self.stats.max_us {
            self.stats.max_us = us;
            self.stats.max_case = name.clone();
        }
        self.stats.over_100ms += usize::from(us > 100_000);
        // The watchdog covers parser + tree checks; analysis between calls is idle.
        *self.active.lock().unwrap() = (Instant::now(), String::new());
        match result {
            Ok((p, loss, ranges)) => {
                self.stats.loss += usize::from(loss);
                self.stats.token_ranges += usize::from(ranges);
                if loss || ranges {
                    println!("INTEGRITY {name} loss={loss} ranges={ranges} source={code:?}");
                }
                Some(p)
            }
            Err(_) => {
                self.stats.panics += 1;
                println!("PANIC {name} source={code:?}");
                None
            }
        }
    }

    fn diagnostics(&mut self, p: &ParsedFile) -> Vec<yu_syntax::SyntaxDiagnostic> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| p.syntax_diagnostics())) {
            Ok(Ok(d)) => d,
            other => {
                self.stats.diagnostic_errors += 1;
                println!("DIAGNOSTIC_ERROR source={:?} result={other:?}", p.source());
                Vec::new()
            }
        }
    }
}

fn files(path: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(path).unwrap() {
        let p = entry.unwrap().path();
        if p.is_dir() {
            files(&p, out);
        } else {
            out.push(p);
        }
    }
}

fn xml_text(s: &str) -> String {
    s.replace("&#10;", "\n")
        .replace("&#13;", "\r")
        .replace("&#9;", "\t")
        .replace("&quot;", "\"")
        .replace("&apos;", "'")
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&amp;", "&")
}

// Include all .yu files, yulang fences, reference text fences and reconstructed
// reference XML token streams. Inline reference spans are additional fragments.
// Keep rejected candidates visible; syntactic acceptance is not semantic validity.
fn candidates() -> Vec<corpus::Case> {
    let mut out = Vec::new();
    for dir in [
        "spec",
        "tests/contracts/phase2-parser",
        "web/playground/examples",
        "syntax-reference",
        "syntax-guide",
    ] {
        let mut paths = Vec::new();
        files(Path::new(dir), &mut paths);
        paths.sort();
        for path in paths {
            let name = path.to_string_lossy();
            let text = std::fs::read_to_string(&path).unwrap();
            if path.extension().is_some_and(|e| e == "yu") {
                out.push(corpus::Case {
                    name: name.into(),
                    code: text,
                    markdown: false,
                });
                continue;
            }
            if !path.extension().is_some_and(|e| e == "md") {
                continue;
            }
            let reference = name.starts_with("syntax-reference/");
            let lines: Vec<_> = text.lines().collect();
            let mut i = 0;
            while i < lines.len() {
                let line = lines[i].trim_start();
                let ticks = line.chars().take_while(|c| *c == '`').count();
                if ticks >= 3 {
                    let info = line[ticks..].trim();
                    let start = i + 1;
                    let mut end = start;
                    while end < lines.len() {
                        let l = lines[end].trim();
                        if l.len() >= ticks && l.chars().all(|c| c == '`') {
                            break;
                        }
                        end += 1;
                    }
                    // CommonMark removes the opening fence's indentation.
                    let indent = lines[i].len() - line.len();
                    let block = lines[start..end]
                        .iter()
                        .map(|l| {
                            let strip = l.bytes().take(indent).take_while(|b| *b == b' ').count();
                            &l[strip..]
                        })
                        .collect::<Vec<_>>()
                        .join("\n");
                    let code = if info == "yulang" || (reference && info == "text") {
                        Some(format!("{block}\n"))
                    } else if reference && info == "xml" {
                        let mut code = String::new();
                        for chunk in block.split("text=\"").skip(1) {
                            if let Some((value, _)) = chunk.split_once('"') {
                                code.push_str(&xml_text(value));
                            }
                        }
                        (!code.is_empty()).then_some(code)
                    } else {
                        None
                    };
                    if let Some(code) = code {
                        out.push(corpus::Case {
                            name: format!("{name}:{}:{info}", start + 1),
                            code,
                            markdown: true,
                        });
                    }
                    i = end + 1;
                } else {
                    if reference {
                        let spans: Vec<_> = line.split('`').collect();
                        for (j, span) in spans.iter().enumerate().filter(|(j, _)| j % 2 == 1) {
                            if !span.is_empty() {
                                out.push(corpus::Case {
                                    name: format!("{name}:{}:inline{j}", i + 1),
                                    code: span.to_string(),
                                    markdown: true,
                                });
                            }
                        }
                    }
                    i += 1;
                }
            }
        }
    }
    out
}

fn diagnostic_description(d: &yu_syntax::SyntaxDiagnostic) -> String {
    match d.cause() {
        SyntaxDiagnosticCause::Structural(s) => format!(
            "{:?}@{:?} slot={:?} expected={:?} path={:?}",
            s.kind(),
            s.range(),
            d.identity().slot(),
            s.expectations(),
            s.path()
        ),
        c => format!("{c:?}"),
    }
}

#[derive(Default)]
struct Measure {
    n: usize,
    earlier: usize,
    earlier_lost: usize,
    later: usize,
    later_lost: usize,
    damaged: usize,
    nested_lost: usize,
    diagnostics: usize,
    multi: usize,
    max_diag: usize,
    marked: usize,
    eof_marked: usize,
    expected: usize,
    worst: Vec<(usize, usize, String)>,
    root_earlier: [usize; 2],
    root_later: [usize; 2],
    panics: usize,
    cascade: Vec<(usize, usize, String)>,
    clean_edits: usize,
    clean_collateral: usize,
}

fn compare(
    m: &mut Measure,
    original: &[Statement],
    root: &SyntaxNode,
    point: usize,
    removed: usize,
    shift: isize,
    prefix: bool,
) -> usize {
    let actual = statements(root);
    let mut lost = 0;
    for old in original {
        let earlier = old.end < point;
        let later = !prefix && old.start > point + removed;
        if !earlier && !later {
            continue;
        }
        let start = if later {
            old.start.checked_add_signed(shift).unwrap()
        } else {
            old.start
        };
        let kept = actual
            .iter()
            .any(|new| new.start == start && new.signature == old.signature);
        if earlier {
            m.earlier += 1;
            m.earlier_lost += usize::from(!kept);
        }
        if later {
            m.later += 1;
            m.later_lost += usize::from(!kept);
        }
        if !old.nested {
            let counts = if earlier {
                &mut m.root_earlier
            } else {
                &mut m.root_later
            };
            counts[0] += usize::from(!kept);
            counts[1] += 1;
        }
        m.nested_lost += usize::from(!kept && old.nested);
        lost += usize::from(!kept);
    }
    m.damaged += usize::from(lost > 0);
    lost
}

fn save_worst(m: &mut Measure, lost: usize, diag: usize, detail: String) {
    m.cascade.push((lost, diag, detail.clone()));
    m.cascade.sort_by(|a, b| {
        b.1.cmp(&a.1)
            .then_with(|| b.0.cmp(&a.0))
            .then_with(|| a.2.cmp(&b.2))
    });
    m.cascade.truncate(5);
    m.worst.push((lost, diag, detail));
    m.worst.sort_by(|a, b| {
        b.0.cmp(&a.0)
            .then_with(|| b.1.cmp(&a.1))
            .then_with(|| a.2.cmp(&b.2))
    });
    m.worst.truncate(5);
}

fn record_diagnostics(m: &mut Measure, d: &[yu_syntax::SyntaxDiagnostic]) {
    m.diagnostics += d.len();
    m.multi += usize::from(d.len() > 1);
    m.max_diag = m.max_diag.max(d.len());
}

fn print_measure(name: &str, m: &Measure) {
    println!(
        "MEASURE {name} n={} earlier_lost={}/{} later_lost={}/{} nested_lost={} edits_with_collateral={} diagnostics={} multi={} max_diag={} marked={} eof_marked={} eof_expected={}",
        m.n,
        m.earlier_lost,
        m.earlier,
        m.later_lost,
        m.later,
        m.nested_lost,
        m.damaged,
        m.diagnostics,
        m.multi,
        m.max_diag,
        m.marked,
        m.eof_marked,
        m.expected
    );
    for (lost, diag, s) in &m.worst {
        println!("WORST {name} collateral={lost} diagnostics={diag} {s}");
    }
    println!(
        "ROOT_ONLY {name} earlier_lost={}/{} later_lost={}/{} panics={} clean_edits={} clean_with_collateral={}",
        m.root_earlier[0],
        m.root_earlier[1],
        m.root_later[0],
        m.root_later[1],
        m.panics,
        m.clean_edits,
        m.clean_collateral
    );
    for (lost, diag, s) in &m.cascade {
        println!("CASCADE {name} collateral={lost} diagnostics={diag} {s}");
    }
}

fn typing(a: &mut Auditor) {
    for code in [
        "x.",
        "x. ",
        "x::",
        "use a::",
        "'",
        "$",
        "&",
        "x |",
        "for x in",
        "if",
        "if c:",
        "case v:",
        "catch x:",
        "say:\n",
        "(",
        "[",
        "{",
        "f(",
        "f(a, ",
        "{ name = ",
        "my { name, ",
        "my (x, ",
        "my x: ",
        "x: ",
        "type T = ",
        "\"unterminated",
        "\"abc\\",
        "x if",
        "x if ",
        "x if c",
        "say: a if",
        "say: a if c",
        "x if c:",
        "x if c else y",
        "my a = (1\nsay: 2\nmy c = 3\n",
        "my a = [1\nfor x in xs: x\nmy c = 3\n",
        "my a = \"oops\nmy b = 2\nmy c = 3\n",
        "my a = 1\nmy b = x.\nmy c = 3\n",
        "my '",
        "my $",
        "my x = &",
        "type T = '",
        "type T = $",
        "case v: x ->",
        "catch x: p ->",
        "my before = 0\nx if\nmy after = 1\n",
        "f(x if, y)",
        "say: a if\nmy after = 1\n",
        "my a = 1\n)\nmy b = 2\nmy c = 3\n",
        "my a = (1\n2\n3\n",
        "my a = {1\n2\n3\n",
        "my a = 1\nmy b = 2\n---",
        "not f x\n-",
        "---\n\\if@(c){yes}\n---\n",
    ] {
        let case = corpus::Case {
            name: "typing".into(),
            code: code.into(),
            markdown: true,
        };
        if let Some(p) = a.parse(&case, code, "") {
            let root = SyntaxNode::new_root(p.green().clone());
            let d = a.diagnostics(&p);
            let cursor = rowan::TextSize::try_from(code.len()).unwrap();
            let paths: Vec<_> = root
                .token_at_offset(cursor)
                .into_iter()
                .map(|t| {
                    format!(
                        "{:?}@{:?}:{:?}",
                        t.kind(),
                        t.text_range(),
                        t.parent()
                            .unwrap()
                            .ancestors()
                            .map(|n| n.kind())
                            .collect::<Vec<_>>()
                    )
                })
                .collect();
            println!(
                "TYPING source={code:?} cursor={paths:?}\n  tree={}\n  diagnostics={:?}",
                shape(&root),
                d.iter().map(diagnostic_description).collect::<Vec<_>>()
            );
        }
    }
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.get(1).is_some_and(|s| s == "--stress") {
        let depth: usize = args[2].parse().unwrap();
        let code = format!("{}x{}", "(".repeat(depth), ")".repeat(depth));
        let case = corpus::Case {
            name: "depth".into(),
            code,
            markdown: false,
        };
        let p = corpus::parse(&case, &case.code);
        println!("DEPTH {depth} parsed");
        assert_eq!(p.green().to_string(), case.code);
        println!("DEPTH {depth} ok");
        return;
    }
    let active = Arc::new(Mutex::new((Instant::now(), String::new())));
    let watch = active.clone();
    std::thread::spawn(move || {
        loop {
            std::thread::sleep(Duration::from_millis(100));
            let current = watch.lock().unwrap();
            if !current.1.is_empty() && current.0.elapsed() > Duration::from_secs(5) {
                eprintln!("TIMEOUT >5s {}", current.1);
                std::process::exit(124);
            }
        }
    });
    let mut a = Auditor {
        stats: Stats::default(),
        active,
    };
    if args.get(1).is_some_and(|s| s == "--file") {
        let code = std::fs::read_to_string(&args[2]).unwrap();
        let case = corpus::Case {
            name: args[2].clone(),
            code: code.clone(),
            markdown: true,
        };
        if let Some(p) = a.parse(&case, &code, "file") {
            println!("{:#?}", SyntaxNode::new_root(p.green().clone()));
            for d in a.diagnostics(&p) {
                println!("{}", diagnostic_description(&d));
            }
        } else {
            std::process::exit(1);
        }
        return;
    }
    typing(&mut a);
    if args.get(1).is_some_and(|s| s == "--typing") {
        if a.stats.panics + a.stats.loss + a.stats.token_ranges + a.stats.diagnostic_errors > 0 {
            std::process::exit(1);
        }
        return;
    }
    let begin = Instant::now();
    let mut clean = Vec::new();
    let mut seen = BTreeSet::new();
    let mut inventory: BTreeMap<String, [usize; 3]> = BTreeMap::new();
    for case in candidates() {
        let group = case.name.split('/').next().unwrap().to_string();
        inventory.entry(group.clone()).or_default()[0] += 1;
        if let Some(p) = a.parse(&case, &case.code, "baseline") {
            let d = a.diagnostics(&p);
            if d.is_empty() {
                inventory.entry(group.clone()).or_default()[1] += 1;
                if seen.insert((case.markdown, case.code.clone())) {
                    inventory.entry(group).or_default()[2] += 1;
                    println!(
                        "CORPUS {} bytes={} hash={:016x}",
                        case.name,
                        case.code.len(),
                        corpus::hash(case.code.as_bytes())
                    );
                    clean.push(case);
                }
            } else {
                println!(
                    "EXCLUDED {} diagnostics={} source={:?}",
                    case.name,
                    d.len(),
                    case.code
                );
            }
        }
    }
    println!("INVENTORY group=[candidates,clean,unique] {inventory:?}");
    let mut measures: BTreeMap<String, Measure> = BTreeMap::new();
    let mut eof: BTreeMap<String, usize> = BTreeMap::new();
    let mut sample_count = 0;
    for (index, case) in clean.iter().enumerate() {
        let p = a.parse(case, &case.code, "full").unwrap();
        let root = SyntaxNode::new_root(p.green().clone());
        let original = statements(&root);
        let tokens: Vec<_> = root
            .descendants_with_tokens()
            .filter_map(|e| e.into_token())
            .collect();
        let mut boundaries = BTreeSet::from([0, case.code.len()]);
        for t in &tokens {
            boundaries.insert(usize::from(t.text_range().start()));
            boundaries.insert(usize::from(t.text_range().end()));
        }
        let byte_sample = index < 24 || (!case.code.is_ascii() && sample_count < 40);
        sample_count += usize::from(byte_sample);
        let mut cuts: Vec<_> = boundaries.iter().map(|p| (*p, "token-prefix")).collect();
        if byte_sample {
            cuts.extend(case.code.char_indices().map(|(p, _)| (p, "scalar-prefix")));
            cuts.push((case.code.len(), "scalar-prefix"));
        }
        for (point, mode) in cuts {
            let source = &case.code[..point];
            measures.entry(mode.into()).or_default().n += 1;
            if let Some(p) = a.parse(case, source, &format!("{mode}@{point}")) {
                let root = SyntaxNode::new_root(p.green().clone());
                let d = a.diagnostics(&p);
                let m = measures.entry(mode.into()).or_default();
                record_diagnostics(m, &d);
                let lost = compare(m, &original, &root, point, 0, 0, true);
                m.marked += usize::from(!d.is_empty());
                let at_end: Vec<_> = d
                    .iter()
                    .filter(|d| {
                        source
                            .get(d.primary().end..)
                            .is_some_and(|s| s.trim().is_empty())
                    })
                    .collect();
                m.eof_marked += usize::from(!at_end.is_empty());
                m.expected += usize::from(at_end.iter().any(|d| matches!(d.cause(), SyntaxDiagnosticCause::Structural(s) if s.expectations().is_some())));
                if mode == "token-prefix" {
                    for d in at_end {
                        *eof.entry(
                            diagnostic_description(d)
                                .split(" path=")
                                .next()
                                .unwrap()
                                .to_string(),
                        )
                        .or_default() += 1;
                    }
                }
                if lost > 0 {
                    save_worst(
                        m,
                        lost,
                        d.len(),
                        format!(
                            "{} cut={point} source={source:?} tree={}",
                            case.name,
                            shape(&root)
                        ),
                    );
                }
            } else {
                measures.entry(mode.into()).or_default().panics += 1;
            }
        }
        for t in tokens
            .iter()
            .filter(|t| !trivia(t.kind()) && !t.text().is_empty())
        {
            let point = usize::from(t.text_range().start());
            let end = usize::from(t.text_range().end());
            let source = format!("{}{}", &case.code[..point], &case.code[end..]);
            mutation(
                &mut a,
                measures.entry("delete-token".into()).or_default(),
                case,
                &original,
                &source,
                point,
                end - point,
                -((end - point) as isize),
                "delete",
            );
        }
        for point in boundaries
            .into_iter()
            .filter(|p| *p > 0 && *p < case.code.len())
        {
            for stray in ["@", ")", "]", "}", "(", "[", "{"] {
                let source = format!("{}{stray}{}", &case.code[..point], &case.code[point..]);
                let mode = if matches!(stray, "(" | "[" | "{") {
                    "insert-opener"
                } else {
                    "insert-stray"
                };
                mutation(
                    &mut a,
                    measures.entry(mode.into()).or_default(),
                    case,
                    &original,
                    &source,
                    point,
                    0,
                    1,
                    stray,
                );
            }
        }
    }
    println!(
        "SAMPLE scalar_files={sample_count} unique_files={} bytes={}",
        clean.len(),
        clean.iter().map(|c| c.code.len()).sum::<usize>()
    );
    for (name, m) in &measures {
        print_measure(name, m);
    }
    // Aggregate by expectation rather than byte range, retained above for human inspection.
    let mut groups: BTreeMap<String, usize> = BTreeMap::new();
    for (desc, count) in eof {
        let key = desc.split(" slot=").nth(1).unwrap_or(&desc).to_string();
        *groups.entry(key).or_default() += count;
    }
    for (desc, count) in groups {
        println!("EOF_EXPECTATION count={count} {desc}");
    }
    println!(
        "TOTAL parses={} panics={} loss={} token_range_errors={} diagnostic_errors={} over100ms={} max_us={} max_case={:?} elapsed_s={:.3}",
        a.stats.parses,
        a.stats.panics,
        a.stats.loss,
        a.stats.token_ranges,
        a.stats.diagnostic_errors,
        a.stats.over_100ms,
        a.stats.max_us,
        a.stats.max_case,
        begin.elapsed().as_secs_f64()
    );
    if a.stats.panics + a.stats.loss + a.stats.token_ranges + a.stats.diagnostic_errors > 0 {
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_arguments)]
fn mutation(
    a: &mut Auditor,
    m: &mut Measure,
    case: &corpus::Case,
    original: &[Statement],
    source: &str,
    point: usize,
    removed: usize,
    shift: isize,
    label: &str,
) {
    m.n += 1;
    if let Some(p) = a.parse(case, source, &format!("{label}@{point}")) {
        let root = SyntaxNode::new_root(p.green().clone());
        let d = a.diagnostics(&p);
        record_diagnostics(m, &d);
        let lost = compare(m, original, &root, point, removed, shift, false);
        m.clean_edits += usize::from(d.is_empty());
        m.clean_collateral += usize::from(d.is_empty() && lost > 0);
        save_worst(
            m,
            lost,
            d.len(),
            format!(
                "{} edit={label}@{point} source={source:?} tree={}",
                case.name,
                shape(&root)
            ),
        );
    } else {
        m.panics += 1;
    }
}
