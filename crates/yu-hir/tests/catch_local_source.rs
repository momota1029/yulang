#![cfg(feature = "shadow")]
use std::sync::Arc;
use yu_hir::shadow::{LocalSource, LocalSourceForm, LocalSourceResolution, LocalSourceScope, LocalSourceCatchValuePattern, LocalSourceCatchPattern, LocalSourceCatchPayloadPattern, SourceOperationResolution, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, HirAvailabilityError, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};
fn lower(text: &str) -> Result<HirModule, HirAvailabilityError> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("test", "catch.yu"))),
        &parsed,
        SemanticImports::empty(),
    )
}
fn sources(module: &HirModule) -> Vec<&LocalSource> {
    module
        .items()
        .iter()
        .filter_map(|item| {
            let HirItem::Binding(binding) = item else {
                return None;
            };
            module.local_source(binding.definition_root()).unwrap()
        })
        .collect()
}

#[test]
fn normal_arms_have_distinct_owned_binders_and_original_scrutinee() {
    let module = lower("my x = 1; my result = catch x { x -> x, x -> x, _ -> 2 }").unwrap();
    let source = sources(&module)[1];
    let expression = source.expression(source.body()).unwrap();
    let LocalSourceForm::Catch { scrutinee, arms } = &expression.form else { panic!("Catch"); };
    assert_eq!(arms.len(), 3);
    assert!(matches!(source.expression(scrutinee).unwrap().form, LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(_), .. }), "scrutinee: {:?}", source.expression(scrutinee).unwrap());
    let mut ids = Vec::new();
    for arm in &arms[..2] {
        let LocalSourceCatchPattern::Value(LocalSourceCatchValuePattern::Binder(binder)) = &arm.pattern else { panic!("binder"); };
        assert_eq!(binder.id.owner(), source.definition_root());
        assert_eq!(binder.id.arm_source(), &arm.source);
        let body = source.expression(&arm.body).unwrap();
        assert!(matches!(&body.form, LocalSourceForm::Name { resolution: LocalSourceResolution::CatchBinder(id), .. } if id == &binder.id));
        assert!(matches!(&body.scope, LocalSourceScope::CatchArm { catch, arm: position } if catch == source.body() && position == &arm.source));
        ids.push(binder.id.clone());
    }
    assert_ne!(ids[0], ids[1]);
    assert!(matches!(arms[2].pattern, LocalSourceCatchPattern::Value(LocalSourceCatchValuePattern::Wildcard)));
    assert!(source.bindings().is_empty());
    assert!(source.expressions().iter().all(|expr| module.owns_occurrence(&expr.occurrence)));
}

#[test]
fn nested_shadowing_and_sibling_scopes_restore_outer_resolution() {
    let module = lower("my x = 1; my result = { my y = catch x { x -> catch x { x -> x }, _ -> x }; x }").unwrap();
    let source = sources(&module)[1];
    let catches: Vec<_> = source.expressions().iter().filter_map(|expr| match &expr.form {
        LocalSourceForm::Catch { arms, .. } => Some(arms), _ => None,
    }).collect();
    assert_eq!(catches.len(), 2);
    let LocalSourceCatchPattern::Value(LocalSourceCatchValuePattern::Binder(outer)) = &catches[0][0].pattern else { panic!("outer binder"); };
    let LocalSourceCatchPattern::Value(LocalSourceCatchValuePattern::Binder(inner)) = &catches[1][0].pattern else { panic!("inner binder"); };
    assert_ne!(outer.id, inner.id);
    assert!(matches!(source.expression(&catches[0][1].body).unwrap().form, LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(_), .. }));
    let LocalSourceForm::Block { final_expression, .. } = &source.expression(source.body()).unwrap().form else { panic!("block"); };
    assert!(matches!(source.expression(final_expression).unwrap().form, LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(_), .. }));
}

#[test]
fn unfinished_handler_forms_are_private_unavailable() {
    for text in ["my result = catch 1 { 1 -> 2 }", "my result = catch 1 { x if true -> x }", "my result = catch 1 { op x, k -> x }"] {
        let formed = lower(text);
        assert!(formed.is_err() || sources(formed.as_ref().unwrap()).is_empty(), "{text}");
    }
}

#[test]
fn qualified_operation_payload_and_continuation_retain_distinct_arm_ownership() {
    let text = "act signal:\n    our ping: int -> int\n\nmy result = catch signal::ping 1 { signal::ping(x), k -> k x, value -> value }";
    let module = lower(text).unwrap();
    let source = sources(&module)[0];
    let LocalSourceForm::Catch { arms, .. } = &source.expression(source.body()).unwrap().form else { panic!("Catch"); };
    let LocalSourceCatchPattern::Operation { resolution: SourceOperationResolution::Resolved(declaration), operation_source, payloads, continuation } = &arms[0].pattern else { panic!("resolved operation"); };
    assert_ne!(operation_source, &arms[0].source);
    assert_eq!(declaration.spelling.as_ref(), "ping");
    let [LocalSourceCatchPayloadPattern::Value(LocalSourceCatchValuePattern::Binder(payload))] = payloads.as_slice() else { panic!("payload binder"); };
    let LocalSourceCatchValuePattern::Binder(continuation) = continuation else { panic!("continuation binder"); };
    assert_eq!(payload.id.ordinal(), 0);
    assert_eq!(continuation.id.ordinal(), 1);
    assert_ne!(payload.id, continuation.id);
    assert_ne!(payload.source, continuation.source);
    for binder in [payload, continuation] {
        assert_eq!(binder.id.owner(), source.definition_root());
        assert_eq!(binder.id.arm_source(), &arms[0].source);
        assert!(source.expressions().iter().any(|expr| matches!(&expr.form, LocalSourceForm::Name { resolution: LocalSourceResolution::CatchBinder(id), .. } if id == &binder.id)));
    }
    assert!(matches!(&arms[1].pattern, LocalSourceCatchPattern::Value(LocalSourceCatchValuePattern::Binder(_))));
}

#[test]
fn empty_operation_payload_retains_syntax_and_scopes_do_not_leak() {
    let module = lower("act signal:\n    our ping: () -> int\n\nmy k = 1; my result = catch signal::ping() { signal::ping(), k -> k 1, _ -> k }").unwrap();
    let source = sources(&module)[1];
    let LocalSourceForm::Catch { arms, .. } = &source.expression(source.body()).unwrap().form else { panic!("Catch"); };
    let LocalSourceCatchPattern::Operation { payloads, continuation, .. } = &arms[0].pattern else { panic!("operation"); };
    let [LocalSourceCatchPayloadPattern::Unit { source: call_source, range }] = payloads.as_slice() else { panic!("empty call syntax"); };
    assert_eq!(range.end - range.start, 2);
    assert_ne!(call_source, &arms[0].source);
    let LocalSourceCatchValuePattern::Binder(continuation) = continuation else { panic!("continuation"); };
    assert_eq!(continuation.id.ordinal(), 1);
    assert!(matches!(source.expression(&arms[1].body).unwrap().form, LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(_), .. }));
}

#[test]
fn operation_pattern_resolution_preserves_unresolved_and_private_members() {
    for (declarations, expected_private) in [("", false), ("act signal:\n    my ping: () -> int\n\n", true)] {
        let module = lower(&format!("{declarations}my result = catch 1 {{ signal::ping(), _ -> 1, value -> value }}")).unwrap();
        let source = sources(&module)[0];
        let LocalSourceForm::Catch { arms, .. } = &source.expression(source.body()).unwrap().form else { panic!("Catch"); };
        let LocalSourceCatchPattern::Operation { resolution, .. } = &arms[0].pattern else { panic!("operation"); };
        assert_eq!(matches!(resolution, SourceOperationResolution::Private), expected_private);
        if !expected_private { assert!(matches!(resolution, SourceOperationResolution::Unresolved)); }
    }
}
