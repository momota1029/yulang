//! Shared deterministic WP-18 corpus and baseline fingerprint encoding.
use std::{
    fmt::Write as _,
    path::{Path, PathBuf},
    sync::Arc,
};
use yu_syntax::{
    HeaderInfo, ParsedFile, SourceRevision, SyntaxDependencyProvenance, SyntaxDependencySlot,
    SyntaxEnvironment, SyntaxEnvironmentKey, SyntaxNode, parse_file, scan_header,
};

pub struct Case {
    pub name: String,
    pub code: String,
    pub markdown: bool,
}

pub fn parse(case: &Case, code: &str) -> ParsedFile {
    let source: Arc<str> = Arc::from(code);
    let header = Arc::new(scan_header(source.clone()));
    let env = if case.markdown {
        prelude_environment(&header)
    } else {
        SyntaxEnvironment::empty()
    };
    parse_file(source, header, Arc::new(env))
}

pub fn valid(parsed: &ParsedFile) -> bool {
    parsed.structural_recoveries().is_empty() && parsed.syntax_diagnostics().unwrap().is_empty()
}

pub fn corpus(root: &Path) -> Vec<Case> {
    let mut cases = Vec::new();
    for (directory, extension) in [
        ("syntax-guide/ja/src", "md"),
        ("spec", "md"),
        ("tests/contracts/phase2-parser", "yu"),
        ("web/playground/examples", "yu"),
    ] {
        let mut files = Vec::new();
        collect(&root.join(directory), extension, &mut files);
        files.sort();
        for file in files {
            let text = std::fs::read_to_string(&file).unwrap();
            let name = file
                .strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            if extension == "yu" {
                cases.push(Case {
                    name,
                    code: text,
                    markdown: false,
                });
                continue;
            }
            let lines: Vec<_> = text.lines().collect();
            let mut index = 0;
            while index < lines.len() {
                let trimmed = lines[index].trim_start();
                let ticks = trimmed.chars().take_while(|c| *c == '`').count();
                if ticks < 3 {
                    index += 1;
                    continue;
                }
                let info = trimmed[ticks..].trim();
                let start = index + 1;
                let mut end = start;
                while end < lines.len() {
                    let t = lines[end].trim();
                    if t.len() >= ticks && t.chars().all(|c| c == '`') {
                        break;
                    }
                    end += 1;
                }
                if info == "yulang" {
                    let case = Case {
                        name: format!("{name}:{}", start + 1),
                        code: format!("{}\n", lines[start..end].join("\n")),
                        markdown: true,
                    };
                    if valid(&parse(&case, &case.code)) {
                        cases.push(case);
                    }
                }
                index = end + 1;
            }
        }
    }
    cases
}

fn collect(path: &Path, extension: &str, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(path).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect(&path, extension, out);
        } else if path.extension().is_some_and(|ext| ext == extension) {
            out.push(path);
        }
    }
}

/// Stable FNV-1a, explicit event tags, kind, arity and token byte lengths.
/// Includes every trivia/recovery token and every node; no tree text is stored.
pub fn fingerprint(root: &SyntaxNode) -> u64 {
    let mut bytes = Vec::new();
    for event in root.preorder_with_tokens() {
        match event {
            rowan::WalkEvent::Enter(element) => {
                bytes.push(if element.as_node().is_some() { 1 } else { 2 });
                bytes.extend_from_slice(&(element.kind() as u16).to_le_bytes());
                if let Some(token) = element.as_token() {
                    bytes.extend_from_slice(&(token.text().len() as u64).to_le_bytes());
                    bytes.extend_from_slice(token.text().as_bytes());
                }
            }
            rowan::WalkEvent::Leave(_) => bytes.push(3),
        }
    }
    hash(&bytes)
}

pub fn hash(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf29ce484222325, |h, b| {
        (h ^ u64::from(*b)).wrapping_mul(0x100000001b3)
    })
}

pub fn fingerprints(cases: &[Case]) -> String {
    let mut result = String::from("# WP-18 phase 1: file/block, source FNV-1a, full CST FNV-1a\n");
    for case in cases {
        let parsed = parse(case, &case.code);
        if valid(&parsed) {
            writeln!(
                result,
                "{}\t{:016x}\t{:016x}",
                case.name,
                hash(case.code.as_bytes()),
                fingerprint(&SyntaxNode::new_root(parsed.green().clone()))
            )
            .unwrap();
        }
    }
    result
}

const PRELUDE: &str = "\
pub infix (|) 1.0.0 1.0.1 = pipe
pub lazy infix (or) 2.0.0 2.0.1 = or
pub lazy infix (and) 3.0.0 3.0.1 = and
pub infix (==) 4.0.0 4.0.1 = eq
pub infix (<) 4.0.0 4.0.1 = lt
pub infix (>) 4.0.0 4.0.1 = gt
pub infix (..) 4.5.0 4.5.1 = range
pub infix (+) 5.0.0 5.0.1 = add
pub infix (-) 5.0.0 5.0.1 = sub
pub infix (*) 6.0.0 6.0.1 = mul
pub prefix (-) 8.0.0 = neg
pub prefix (not) 8.0.0 = not
pub suffix (..) 8.0.0 = from
";

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
