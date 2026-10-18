use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};

use yu_hir::{
    FileId, FileKey, HirAvailabilityError, HirModule, ModuleIdentity, SemanticImports, lower_module,
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

fn parsed(text: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(text);
    parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn identity(path: &str) -> ModuleIdentity {
    ModuleIdentity::source_root(FileId::new(FileKey::new("semantic-import-binding", path)))
}

fn top_level_keys(parsed: &ParsedFile) -> Vec<yu_syntax::SourceNodeKey> {
    parsed
        .source_root()
        .children()
        .map(|node| node.key())
        .collect()
}

struct DropProbe(Arc<AtomicBool>);

impl Drop for DropProbe {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

fn assert_send_sync<T: Send + Sync>() {}

#[test]
fn matching_binding_is_retained_by_the_exact_hir_owner() {
    assert_send_sync::<HirModule>();
    let parsed = parsed("my answer = 42");
    let declaration = top_level_keys(&parsed).remove(0);
    let identity = identity("main.yu");
    let dropped = Arc::new(AtomicBool::new(false));
    let payload = Arc::new(DropProbe(dropped.clone()));
    let imports =
        SemanticImports::with_caller_evidence(&parsed, &identity, &declaration, payload.clone())
            .unwrap();
    drop(payload);

    let hir = lower_module(identity.clone(), &parsed, imports).unwrap();
    let binding = hir.caller_evidence().expect("caller payload retained");
    assert_eq!(binding.parse_root_key(), &parsed.source_root().key());
    assert_eq!(binding.declaration_key(), &declaration);
    assert_eq!(binding.module_identity(), &identity);
    assert!(binding.payload_is::<DropProbe>());
    assert!(!dropped.load(Ordering::SeqCst));

    drop(hir);
    assert!(dropped.load(Ordering::SeqCst));
}

#[test]
fn fresh_equal_text_parse_is_rejected() {
    let first = parsed("my answer = 42");
    let second = parsed("my answer = 42");
    let declaration = top_level_keys(&first).remove(0);
    let identity = identity("main.yu");
    let imports =
        SemanticImports::with_caller_evidence(&first, &identity, &declaration, Arc::new(()))
            .unwrap();

    assert_eq!(
        lower_module(identity, &second, imports),
        Err(HirAvailabilityError::ForeignCallerEvidenceSource),
    );
}

#[test]
fn foreign_source_key_is_rejected_at_binding_construction() {
    let first = parsed("my x = 1");
    let second = parsed("my y = 2");
    let foreign_key = top_level_keys(&first).remove(0);

    assert_eq!(
        SemanticImports::with_caller_evidence(
            &second,
            &identity("main.yu"),
            &foreign_key,
            Arc::new(()),
        )
        .unwrap_err(),
        HirAvailabilityError::ForeignCallerEvidenceSource,
    );
}

#[test]
fn mismatched_module_and_non_declaration_anchor_are_rejected() {
    let parsed = parsed("my answer = 42; 1");
    let keys = top_level_keys(&parsed);
    let main_identity = identity("main.yu");
    let imports =
        SemanticImports::with_caller_evidence(&parsed, &main_identity, &keys[0], Arc::new(()))
            .unwrap();
    assert_eq!(
        lower_module(identity("other.yu"), &parsed, imports),
        Err(HirAvailabilityError::ForeignCallerEvidenceModule),
    );

    let imports =
        SemanticImports::with_caller_evidence(&parsed, &main_identity, &keys[1], Arc::new(()))
            .unwrap();
    assert_eq!(
        lower_module(main_identity, &parsed, imports),
        Err(HirAvailabilityError::CallerEvidenceNotDeclaration),
    );
}

#[test]
fn empty_imports_remain_unbound_and_compatible() {
    let parsed = parsed("my answer = 42");
    let hir = lower_module(identity("main.yu"), &parsed, SemanticImports::empty()).unwrap();
    assert!(hir.caller_evidence().is_none());
    assert_eq!(SemanticImports::empty(), SemanticImports::empty());
}
