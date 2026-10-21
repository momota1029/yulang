//! Exact source bytes for the R149 Yulang2 standard-library closure.

const BUNDLE: &[u8] = include_bytes!("../pinned_stdlib.bin");
const MAGIC: &[u8; 8] = b"YU2STD\0\x01";

#[derive(Clone, Debug)]
pub(crate) struct PinnedSource {
    pub(crate) path: &'static str,
    pub(crate) git_blob: [u8; 20],
    pub(crate) text: &'static str,
}

/// Parse-owned source inventory for one exact pinned module. This is test
/// evidence for source identity and syntax positions only; it does not resolve
/// a role or select an implementation.
#[cfg(test)]
pub(crate) struct ParsedRoleInventory {
    pub(crate) source: PinnedSource,
    pub(crate) identity: yu_hir::ModuleIdentity,
    pub(crate) parsed: yu_syntax::ParsedFile,
    pub(crate) declaration_ranges: Vec<(yu_syntax::SyntaxKind, std::ops::Range<usize>)>,
    pub(crate) diagnostics: Vec<ParsedSyntaxDiagnostic>,
}

#[cfg(test)]
pub(crate) struct ParsedSyntaxDiagnostic {
    pub(crate) range: std::ops::Range<usize>,
    pub(crate) excerpt: String,
    pub(crate) category: String,
    pub(crate) parent: String,
    pub(crate) ordinal: Option<u32>,
}

#[cfg(test)]
pub(crate) fn parse_role_inventory(
    module: &str,
    environment: std::sync::Arc<yu_syntax::SyntaxEnvironment>,
) -> Result<ParsedRoleInventory, String> {
    use yu_hir::{FileId, FileKey, ModuleIdentity};
    use yu_syntax::{SourceText, SyntaxKind, SyntaxNode, parse_file, scan_header};

    let source = source_for_module(module)
        .map_err(|error| format!("pinned source bundle: {error:?}"))?
        .ok_or_else(|| format!("missing pinned module {module}"))?;
    let text: std::sync::Arc<SourceText> = std::sync::Arc::from(source.text);
    let parsed = parse_file(
        text.clone(),
        std::sync::Arc::new(scan_header(text)),
        environment,
    );
    let diagnostics = parsed
        .syntax_diagnostics()
        .map_err(|error| format!("syntax diagnostics: {error:?}"))?
        .into_iter()
        .map(|diagnostic| {
            use yu_syntax::SyntaxDiagnosticCause;
            let range = diagnostic.primary().clone();
            let mut excerpt_end = range.end.min(range.start.saturating_add(160));
            while !source.text.is_char_boundary(excerpt_end) {
                excerpt_end -= 1;
            }
            let excerpt = source.text[range.start..excerpt_end].to_owned();
            match diagnostic.cause() {
                SyntaxDiagnosticCause::Structural(structural) => ParsedSyntaxDiagnostic {
                    range,
                    excerpt,
                    category: format!("{:?}", structural.kind()),
                    parent: format!("{:?}", structural.parent()),
                    ordinal: Some(structural.ordinal()),
                },
                SyntaxDiagnosticCause::ConflictingOperatorFixity(_) => ParsedSyntaxDiagnostic {
                    range,
                    excerpt,
                    category: "ConflictingOperatorFixity".to_owned(),
                    parent: "operator environment".to_owned(),
                    ordinal: None,
                },
            }
        })
        .collect::<Vec<_>>();
    let root = SyntaxNode::new_root(parsed.green().clone());
    let declaration_ranges = root
        .descendants()
        .filter(|node| {
            matches!(node.kind(), SyntaxKind::RoleDeclaration | SyntaxKind::ImplDeclaration)
        })
        .map(|node| {
            (
                node.kind(),
                usize::from(node.text_range().start())..usize::from(node.text_range().end()),
            )
        })
        .collect();
    let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
        "yulang2-pinned-stdlib",
        source.path,
    )));
    Ok(ParsedRoleInventory {
        source,
        identity,
        parsed,
        declaration_ranges,
        diagnostics,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum BundleError {
    BadMagic,
    Truncated,
    InvalidUtf8,
    TrailingBytes,
    MissingModule {
        module: String,
        declared_from: String,
    },
    UnresolvedImport {
        path: String,
        imported_from: String,
    },
    UnreachableSource(String),
    SyntaxEnvironment {
        module: String,
        error: String,
    },
}

pub(crate) fn sources() -> Result<Vec<PinnedSource>, BundleError> {
    if BUNDLE.get(..MAGIC.len()) != Some(MAGIC) {
        return Err(BundleError::BadMagic);
    }
    let mut cursor = MAGIC.len();
    let count = read_u32(&mut cursor)? as usize;
    let mut sources = Vec::with_capacity(count);
    for _ in 0..count {
        let path_len = read_u16(&mut cursor)? as usize;
        let blob_bytes = take(&mut cursor, 20)?;
        let mut git_blob = [0; 20];
        git_blob.copy_from_slice(blob_bytes);
        let text_len = read_u32(&mut cursor)? as usize;
        let path = std::str::from_utf8(take(&mut cursor, path_len)?)
            .map_err(|_| BundleError::InvalidUtf8)?;
        let text = std::str::from_utf8(take(&mut cursor, text_len)?)
            .map_err(|_| BundleError::InvalidUtf8)?;
        sources.push(PinnedSource {
            path,
            git_blob,
            text,
        });
    }
    if cursor != BUNDLE.len() {
        return Err(BundleError::TrailingBytes);
    }
    Ok(sources)
}

#[cfg(test)]
pub(crate) fn source_for_module(module: &str) -> Result<Option<PinnedSource>, BundleError> {
    let path = format!("lib/{}.yu", module.replace("::", "/"));
    Ok(sources()?.into_iter().find(|source| source.path == path))
}

pub(crate) fn resolve_implicit_stdlib() -> Result<std::sync::Arc<[PinnedSource]>, BundleError> {
    use std::sync::{Arc, OnceLock};

    static RESOLVED: OnceLock<Result<Arc<[PinnedSource]>, BundleError>> = OnceLock::new();
    RESOLVED
        .get_or_init(|| resolve_implicit_stdlib_uncached().map(Arc::from))
        .clone()
}

pub(crate) fn syntax_environment_for_source(
    source: &PinnedSource,
    all_sources: &[PinnedSource],
) -> Result<yu_syntax::SyntaxEnvironment, BundleError> {
    use std::collections::{HashMap, HashSet};
    use std::sync::Arc;
    use yu_syntax::{
        HeaderImportForm, HeaderImportRouteSeparator, SourceRevision,
        SyntaxDependencyProvenance, SyntaxDependencySlot, SyntaxEnvironment,
        SyntaxEnvironmentKey, SourceText, scan_header,
    };

    let source_by_path = all_sources
        .iter()
        .map(|source| (source.path, source))
        .collect::<HashMap<_, _>>();
    let text: Arc<SourceText> = Arc::from(source.text);
    let header = scan_header(Arc::clone(&text));
    let mut seen = HashSet::new();
    let mut imported = Vec::new();
    for import in header.imports() {
        if !matches!(import.form(), HeaderImportForm::Plain | HeaderImportForm::Mod)
            || import.path().first().map(String::as_str) != Some("std")
            || import
                .route()
                .separators()
                .iter()
                .any(|separator| *separator != HeaderImportRouteSeparator::ColonColon)
        {
            continue;
        }
        let target = resolve_import_module(import.path(), |candidate| {
            source_by_path.contains_key(source_path(candidate).as_str())
        })
        .ok_or_else(|| BundleError::UnresolvedImport {
            path: import.path().join("::"),
            imported_from: source.path.to_owned(),
        })?;
        if !seen.insert(target.clone()) {
            continue;
        }
        let path = source_path(&target);
        let dependency = source_by_path
            .get(path.as_str())
            .copied()
            .ok_or_else(|| BundleError::UnresolvedImport {
                path: target.clone(),
                imported_from: source.path.to_owned(),
            })?;
        let dependency_text: Arc<SourceText> = Arc::from(dependency.text);
        imported.push((dependency, scan_header(dependency_text)));
    }

    let mut provenance = Vec::new();
    let mut dependencies = Vec::new();
    let mut hash_value = 0xcbf29ce484222325u64;
    let mut mix = |bytes: &[u8]| {
        for byte in bytes {
            hash_value ^= u64::from(*byte);
            hash_value = hash_value.wrapping_mul(0x100000001b3);
        }
    };
    mix(source.path.as_bytes());
    mix(&source.git_blob);
    for (index, (dependency, dependency_header)) in imported.iter().enumerate() {
        let slot = SyntaxDependencySlot::from_index(index).ok_or_else(|| {
            BundleError::SyntaxEnvironment {
                module: source.path.to_owned(),
                error: "syntax dependency slot overflow".to_owned(),
            }
        })?;
        provenance.push(SyntaxDependencyProvenance::new(
            Arc::from(dependency.path),
            SourceRevision::from_fingerprint(fingerprint(&dependency.git_blob)),
        ));
        dependencies.push((slot, dependency_header));
        mix(dependency.path.as_bytes());
        mix(&dependency.git_blob);
    }
    drop(mix);
    SyntaxEnvironment::from_imported_headers(
        SyntaxEnvironmentKey::from_fingerprint(hash_value),
        dependencies,
        Arc::from(provenance),
    )
    .map_err(|error| BundleError::SyntaxEnvironment {
        module: source.path.to_owned(),
        error: format!("{error:?}"),
    })
}

fn resolve_implicit_stdlib_uncached() -> Result<Vec<PinnedSource>, BundleError> {
    use std::collections::{HashMap, HashSet, VecDeque};
    use yu_syntax::{
        HeaderImportForm, HeaderImportRouteSeparator, SyntaxEnvironment, SyntaxKind, SyntaxNode,
        parse_file, scan_header,
    };

    let all_sources = sources()?;
    let source_by_path = all_sources
        .iter()
        .map(|source| (source.path, source))
        .collect::<HashMap<_, _>>();
    let mut seen = HashSet::new();
    let mut pending = VecDeque::new();
    enqueue_module("std".to_owned(), &mut seen, &mut pending);
    let mut resolved = Vec::new();

    while let Some(module) = pending.pop_front() {
        let path = source_path(&module);
        let source =
            source_by_path
                .get(path.as_str())
                .ok_or_else(|| BundleError::MissingModule {
                    module: module.clone(),
                    declared_from: "implicit std root".to_owned(),
                })?;
        resolved.push((*source).clone());

        let text: std::sync::Arc<yu_syntax::SourceText> = std::sync::Arc::from(source.text);
        let header = scan_header(std::sync::Arc::clone(&text));
        let parsed = parse_file(
            text,
            std::sync::Arc::new(header.clone()),
            std::sync::Arc::new(SyntaxEnvironment::empty()),
        );
        let root = SyntaxNode::new_root(parsed.green().clone());

        for declaration in root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::ModDeclaration)
        {
            let Some(name) = declaration
                .children_with_tokens()
                .filter_map(|child| child.into_token())
                .find(|token| token.kind() == SyntaxKind::Identifier)
            else {
                continue;
            };
            let child_module = format!("{module}::{}", name.text());
            let child_path = source_path(&child_module);
            if !source_by_path.contains_key(child_path.as_str()) {
                return Err(BundleError::MissingModule {
                    module: child_module,
                    declared_from: path,
                });
            }
            enqueue_module(child_module, &mut seen, &mut pending);
        }

        for import in header.imports() {
            if !matches!(
                import.form(),
                HeaderImportForm::Plain | HeaderImportForm::Mod
            ) || import.path().first().map(String::as_str) != Some("std")
                || import
                    .route()
                    .separators()
                    .iter()
                    .any(|separator| *separator != HeaderImportRouteSeparator::ColonColon)
            {
                continue;
            }
            let segments = import.path();
            let target = resolve_import_module(segments, |candidate| {
                source_by_path.contains_key(source_path(candidate).as_str())
            });
            let Some(target) = target else {
                return Err(BundleError::UnresolvedImport {
                    path: segments.join("::"),
                    imported_from: path,
                });
            };
            enqueue_module(target, &mut seen, &mut pending);
        }
    }

    if resolved.len() != all_sources.len() {
        let resolved_paths = resolved
            .iter()
            .map(|source| source.path)
            .collect::<HashSet<_>>();
        if let Some(missing) = all_sources
            .iter()
            .find(|source| !resolved_paths.contains(source.path))
        {
            return Err(BundleError::UnreachableSource(missing.path.to_owned()));
        }
    }
    Ok(resolved)
}

fn source_path(module: &str) -> String {
    format!("lib/{}.yu", module.replace("::", "/"))
}

fn resolve_import_module(
    segments: &[String],
    mut has_source: impl FnMut(&str) -> bool,
) -> Option<String> {
    (2..=segments.len())
        .rev()
        .map(|length| segments[..length].join("::"))
        .find(|candidate| has_source(candidate))
}

fn enqueue_module(
    module: String,
    seen: &mut std::collections::HashSet<String>,
    pending: &mut std::collections::VecDeque<String>,
) {
    if seen.insert(module.clone()) {
        pending.push_back(module);
    }
}

pub(crate) fn fingerprint(blob: &[u8; 20]) -> u64 {
    u64::from_be_bytes(
        blob[..8]
            .try_into()
            .expect("Git object ID prefix is eight bytes"),
    )
}

fn take(cursor: &mut usize, length: usize) -> Result<&'static [u8], BundleError> {
    let end = cursor.checked_add(length).ok_or(BundleError::Truncated)?;
    let bytes = BUNDLE.get(*cursor..end).ok_or(BundleError::Truncated)?;
    *cursor = end;
    Ok(bytes)
}

fn read_u16(cursor: &mut usize) -> Result<u16, BundleError> {
    let bytes = take(cursor, 2)?;
    Ok(u16::from_be_bytes([bytes[0], bytes[1]]))
}

fn read_u32(cursor: &mut usize) -> Result<u32, BundleError> {
    let bytes = take(cursor, 4)?;
    Ok(u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_bundled_source_matches_its_pinned_git_blob() {
        let sources = sources().expect("pinned source bundle parses");
        assert_eq!(sources.len(), 40);
        for source in sources {
            assert_eq!(
                git_blob_id(source.text.as_bytes()),
                source.git_blob,
                "{}",
                source.path
            );
            assert!(source.path.starts_with("lib/std/") || source.path == "lib/std.yu");
        }
    }

    #[test]
    fn module_lookup_uses_the_authentic_core_operator_source() {
        let root = source_for_module("std")
            .expect("bundle parses")
            .expect("implicit std root is pinned");
        assert_eq!(root.path, "lib/std.yu");

        let source = source_for_module("std::core::ops")
            .expect("bundle parses")
            .expect("std::core::ops is pinned");
        assert_eq!(source.path, "lib/std/core/ops.yu");
        assert!(source.text.contains("pub infix (+) 5.0.0 5.0.1"));
        assert_eq!(
            hex(&source.git_blob),
            "575e6fb15ce2d91a39004bbc7b842fedb2d83fdf"
        );
    }

    #[test]
    fn implicit_root_resolves_exactly_the_pinned_module_graph() {
        let resolved = resolve_implicit_stdlib().expect("all pinned std references resolve");
        let all = sources().expect("pinned source bundle parses");
        let resolved_paths = resolved
            .iter()
            .map(|source| source.path)
            .collect::<std::collections::HashSet<_>>();
        let all_paths = all
            .iter()
            .map(|source| source.path)
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(resolved.len(), 40);
        assert_eq!(resolved_paths, all_paths);
        assert!(
            resolved
                .iter()
                .any(|source| source.path == "lib/std/prelude.yu")
        );
        assert!(
            resolved
                .iter()
                .any(|source| source.path == "lib/std/io/console.yu")
        );
    }

    #[test]
    fn unresolved_import_prefix_is_rejected() {
        let segments = ["std", "core", "fmt", "show"]
            .into_iter()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        assert_eq!(
            resolve_import_module(&segments, |module| module == "std::core"
                || module == "std::core::fmt"),
            Some("std::core::fmt".to_owned())
        );
        let missing = ["std", "missing", "item"].map(str::to_owned);
        assert_eq!(
            resolve_import_module(&missing, |module| module == "std"),
            None
        );
    }

    #[test]
    fn module_graph_queue_terminates_on_cycles_and_repeated_edges() {
        use std::collections::{HashMap, HashSet, VecDeque};

        let graph = HashMap::from([
            ("a", vec!["b", "c"]),
            ("b", vec!["a", "c"]),
            ("c", vec!["a"]),
        ]);
        let mut seen = HashSet::new();
        let mut pending = VecDeque::new();
        enqueue_module("a".to_owned(), &mut seen, &mut pending);
        while let Some(node) = pending.pop_front() {
            for child in &graph[node.as_str()] {
                enqueue_module((*child).to_owned(), &mut seen, &mut pending);
            }
        }
        assert_eq!(
            seen,
            HashSet::from(["a".to_owned(), "b".to_owned(), "c".to_owned()])
        );
    }

    fn git_blob_id(source: &[u8]) -> [u8; 20] {
        let mut message = format!("blob {}\0", source.len()).into_bytes();
        message.extend_from_slice(source);
        sha1(&message)
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    // Small test-only SHA-1 implementation, used to verify Git's blob identity
    // without invoking Git or relying on a network-fetched hash crate.
    fn sha1(message: &[u8]) -> [u8; 20] {
        let bit_len = (message.len() as u64) * 8;
        let mut data = message.to_vec();
        data.push(0x80);
        while data.len() % 64 != 56 {
            data.push(0);
        }
        data.extend_from_slice(&bit_len.to_be_bytes());
        let mut h = [
            0x6745_2301u32,
            0xefcd_ab89,
            0x98ba_dcfe,
            0x1032_5476,
            0xc3d2_e1f0,
        ];
        for chunk in data.chunks_exact(64) {
            let mut w = [0u32; 80];
            for (i, bytes) in chunk.chunks_exact(4).enumerate() {
                w[i] = u32::from_be_bytes(bytes.try_into().expect("four-byte word"));
            }
            for i in 16..80 {
                w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
            }
            let [mut a, mut b, mut c, mut d, mut e] = h;
            for (i, word) in w.into_iter().enumerate() {
                let (f, k) = match i {
                    0..=19 => ((b & c) | (!b & d), 0x5a82_7999),
                    20..=39 => (b ^ c ^ d, 0x6ed9_eba1),
                    40..=59 => ((b & c) | (b & d) | (c & d), 0x8f1b_bcdc),
                    _ => (b ^ c ^ d, 0xca62_c1d6),
                };
                let temp = a
                    .rotate_left(5)
                    .wrapping_add(f)
                    .wrapping_add(e)
                    .wrapping_add(k)
                    .wrapping_add(word);
                e = d;
                d = c;
                c = b.rotate_left(30);
                b = a;
                a = temp;
            }
            h[0] = h[0].wrapping_add(a);
            h[1] = h[1].wrapping_add(b);
            h[2] = h[2].wrapping_add(c);
            h[3] = h[3].wrapping_add(d);
            h[4] = h[4].wrapping_add(e);
        }
        let mut result = [0; 20];
        for (chunk, word) in result.chunks_exact_mut(4).zip(h) {
            chunk.copy_from_slice(&word.to_be_bytes());
        }
        result
    }
}
