#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

use std::sync::Arc;
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports, SourceRootId};
use yu_solver::shadow_apply::{CandidateError, CandidateInference, CandidateSourceValueIdentity};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
    Arc::new(yu_hir::lower_module(
        ModuleIdentity::source_root(FileId::new(FileKey::new("ordinary-expression", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap())
}

#[test]
fn original_name_roots_consume_backward_and_forward_published_targets() {
    for text in ["my target = 1; target", "target; my target = 1"] {
        let hir = module(text);
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        let expression = hir.items().iter().find_map(|item| match item {
            HirItem::Expression(expression) => Some(expression), _ => None,
        }).unwrap();
        let root = hir.expression_root(expression.occurrence()).unwrap().unwrap();
        assert!(hir.local_source_for(&SourceRootId::Expression(root.clone())).unwrap().is_some());
        assert_eq!(candidate.fresh_use(expression.occurrence()).unwrap().occurrence(), expression.occurrence());
        assert_eq!(hir.items().iter().filter(|item| matches!(item, HirItem::Binding(_))).count(), 1);
        for item in hir.items() {
            if let HirItem::Binding(binding) = item { assert!(candidate.export(binding.definition_root()).is_ok()); }
        }
    }
}

#[test]
fn apply_root_keeps_original_expression_value_and_source_owner() {
    let hir = module("id 1; my id x = x");
    let HirItem::Expression(expression) = &hir.items()[0] else { panic!("original root"); };
    let root = hir.expression_root(expression.occurrence()).unwrap().unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 1);
    let call = candidate.source_call(0).unwrap();
    assert_eq!(call.owner(), &SourceRootId::Expression(root.clone()));
    assert_eq!(&call.source().occurrence, expression.occurrence());
    let observed = candidate.intrusion_observation().unwrap();
    let event = observed.events().find(|event| event.checking.occurrence() == expression.occurrence()).unwrap();
    assert!(matches!(event.origin.identity, CandidateSourceValueIdentity::Expression(id) if id == root.occurrence()));
    assert!(matches!(event.receiver.identity, CandidateSourceValueIdentity::Module(_)));
    let foreign = module("id 1; my id x = x");
    assert!(foreign.local_source_for(&SourceRootId::Expression(root.clone())).is_err());
    assert!(candidate.fresh_use(foreign.items().iter().find_map(|item| match item {
        HirItem::Expression(expr) => Some(expr.occurrence()), _ => None,
    }).unwrap()).is_none());
}

#[test]
fn expression_receivers_reuse_supported_nested_constructors() {
    for body in [
        r"(\x -> x) 1",
        "{ my id (x:int) = x; id 1 }",
        "{ my local:int = 1; local }",
        "catch 1 { x -> x }",
        "if true: 1 else: 2",
        "1",
    ] {
        let hir = module(&format!("{body}; my selected = 1"));
        let candidate = CandidateInference::solve(hir.clone()).unwrap_or_else(|error| panic!("{body}: {error:?}"));
        assert!(candidate.candidate_conflicts().is_empty(), "{body}");
        let binding = hir.items().iter().find_map(|item| match item { HirItem::Binding(binding) => Some(binding), _ => None }).unwrap();
        assert!(candidate.export(binding.definition_root()).is_ok());
    }
}

#[test]
fn unresolved_and_recovered_expression_roots_keep_explicit_refusal() {
    for text in ["missing; my selected = 1", "@; my selected = 1"] {
        assert!(matches!(CandidateInference::solve(module(text)), Err(CandidateError::Unsupported)));
    }
    let recovered = module("f(@missing); my selected = 1");
    let HirItem::Expression(expression) = &recovered.items()[0] else { panic!("admitted recovered expression"); };
    assert!(recovered.expression_root(expression.occurrence()).unwrap().is_some());
    assert!(matches!(CandidateInference::solve(recovered), Err(CandidateError::Unsupported)));
}

#[test]
fn opt_in_effect_declaration_items_and_expression_operation_roots_keep_their_owners() {
    // Act constructors use the existing opt-in source entrypoint.
    let source: Arc<SourceText> = Arc::from("act tick:\n    our next: () -> int\n\ntick::next(); my selected = 1");
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
    let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("ordinary-expression", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap());
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let call = candidate.source_call(0).unwrap();
    let root = call.owner().expression_root().expect("the operation call belongs to the original expression");
    assert!(hir.expression_root(root.occurrence()).unwrap().is_some());
    assert_eq!(hir.source_effect_declarations().len(), 1);
}
