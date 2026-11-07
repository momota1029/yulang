//! Exhaustive WP-18 recovery measurement. Run from the worktree root:
//! cargo run --offline --release -q -p yu-syntax --example recovery_mutation
//!
//! Eligible positions are all UTF-8 scalar boundaries, including inside literal
//! and comment text: delete each `)]}`, insert each of `([{` at every boundary
//! (including EOF), truncate at every strictly interior boundary of each line
//! (CRLF is one line ending). Each mutation starts from the original source.
//! A later statement starts strictly after the edit byte. It is preserved only
//! at its shifted source offset, with identical full CST kinds and token text,
//! including trivia. Fractions are averaged over mutations with later statements;
//! vacuous mutations are counted separately. Truncation deliberately counts the
//! removed suffix as lost; it is a totality control, not a suffix-preservation claim.

#[path = "support/recovery_corpus.rs"]
mod corpus;

use std::{collections::BTreeMap, path::Path, time::Instant};
use yu_syntax::SyntaxNode;

#[derive(Default)]
struct Measure {
    total: usize,
    measured: usize,
    sum: f64,
    preserved: usize,
    later: usize,
    majority_lost: usize,
    worst: Vec<(usize, usize, String, usize)>,
}

fn main() {
    let start = Instant::now();
    let cases = corpus::corpus(Path::new("."));
    // Baseline generation is explicit and occurs before parser changes. Never
    // refresh this file to make the corpus regression test pass.
    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(path, corpus::fingerprints(&cases)).unwrap();
    }
    let mut measures: [Measure; 3] = Default::default();
    let mut clean = 0;
    let mut bytes = 0;
    for case in &cases {
        bytes += case.code.len();
        let parsed = corpus::parse(case, &case.code);
        clean += usize::from(corpus::valid(&parsed));
        let root = SyntaxNode::new_root(parsed.green().clone());
        let statements: Vec<_> = root
            .children()
            .map(|node| {
                (
                    usize::from(node.text_range().start()),
                    corpus::fingerprint(&node),
                )
            })
            .collect();
        for (position, ch) in case.code.char_indices() {
            if matches!(ch, ')' | ']' | '}') {
                let mut edited = case.code.clone();
                edited.remove(position);
                measure(&mut measures[0], case, &statements, &edited, position, -1);
            }
        }
        for position in case
            .code
            .char_indices()
            .map(|(p, _)| p)
            .chain([case.code.len()])
        {
            for opener in ['(', '[', '{'] {
                let mut edited = case.code.clone();
                edited.insert(position, opener);
                measure(&mut measures[1], case, &statements, &edited, position, 1);
            }
        }
        let mut line_start = 0;
        for line in case.code.split_inclusive('\n') {
            let content = line.trim_end_matches(['\r', '\n']);
            for (offset, _) in content.char_indices().skip(1) {
                let position = line_start + offset;
                measure(
                    &mut measures[2],
                    case,
                    &statements,
                    &case.code[..position],
                    position,
                    0,
                );
            }
            line_start += line.len();
        }
    }
    println!(
        "corpus: {} cases, {clean} clean, {} bytes",
        cases.len(),
        bytes
    );
    println!(
        "| mutation | total | with later statements | mean preserved | preserved/later | >half lost |"
    );
    println!("| --- | ---: | ---: | ---: | ---: | ---: |");
    for (name, m) in ["delete closer", "insert opener", "truncate mid-line"]
        .iter()
        .zip(&measures)
    {
        println!(
            "| {name} | {} | {} | {:.6}% | {}/{} | {} |",
            m.total,
            m.measured,
            m.sum / m.measured as f64 * 100.0,
            m.preserved,
            m.later,
            m.majority_lost
        );
    }
    for (name, m) in ["delete closer", "insert opener", "truncate mid-line"]
        .iter()
        .zip(&mut measures)
    {
        m.worst.sort_by(|a, b| {
            (a.0 * b.1)
                .cmp(&(b.0 * a.1))
                .then_with(|| b.1.cmp(&a.1))
                .then_with(|| a.2.cmp(&b.2))
                .then_with(|| a.3.cmp(&b.3))
        });
        println!("\n{name}: worst 10 (ties: most later statements, file, byte position)");
        for (preserved, later, file, position) in m.worst.iter().take(10) {
            println!(
                "{file} byte={position}: {preserved}/{later} ({:.6}%)",
                *preserved as f64 / *later as f64 * 100.0
            );
        }
    }
    println!("runtime: {:.3}s", start.elapsed().as_secs_f64());
}

fn measure(
    m: &mut Measure,
    case: &corpus::Case,
    original: &[(usize, u64)],
    edited: &str,
    point: usize,
    shift: isize,
) {
    m.total += 1;
    // Parse even vacuous cases: the mutation enumeration also checks totality.
    let parsed = std::panic::catch_unwind(|| corpus::parse(case, edited)).unwrap_or_else(|panic| {
        eprintln!(
            "mutation panic: {} byte={point} shift={shift} source={edited:?}",
            case.name
        );
        std::panic::resume_unwind(panic)
    });
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(
        root.to_string(),
        edited,
        "losslessness: {} byte={point}",
        case.name
    );
    let later: Vec<_> = original
        .iter()
        .filter(|(start, _)| *start > point)
        .collect();
    if later.is_empty() {
        return;
    }
    let actual: BTreeMap<_, _> = root
        .children()
        .map(|node| {
            (
                usize::from(node.text_range().start()),
                corpus::fingerprint(&node),
            )
        })
        .collect();
    let preserved = later
        .iter()
        .filter(|(start, fingerprint)| {
            actual.get(&start.checked_add_signed(shift).unwrap()) == Some(fingerprint)
        })
        .count();
    m.measured += 1;
    m.sum += preserved as f64 / later.len() as f64;
    m.preserved += preserved;
    m.later += later.len();
    m.majority_lost += usize::from(2 * preserved < later.len());
    m.worst
        .push((preserved, later.len(), case.name.clone(), point));
}
