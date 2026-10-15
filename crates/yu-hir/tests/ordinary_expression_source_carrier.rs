use std::sync::Arc;
use yu_hir::{
    FileId, FileKey, HirAvailabilityError, HirItem, HirModule, LocalSource,
    LocalSourceCatchPattern, LocalSourceCatchValuePattern, LocalSourceForm,
    LocalSourceNamedGroupOwner, LocalSourceResolution, ModuleIdentity, SemanticImports,
    SourceCarrierOutcome, SourceRootId, lower_module,
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

fn parsed(text: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(text);
    parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()))
}
fn identity() -> ModuleIdentity {
    ModuleIdentity::source_root(FileId::new(FileKey::new("expression-carrier", "source.yu")))
}
fn lower(text: &str) -> HirModule {
    lower_module(identity(), &parsed(text), SemanticImports::empty()).unwrap()
}
fn expression_owner(module: &HirModule, item: usize) -> SourceRootId {
    let HirItem::Expression(expression) = &module.items()[item] else { panic!("expression item"); };
    SourceRootId::Expression(module.expression_root(expression.occurrence()).unwrap().unwrap().clone())
}
fn supported<'a>(module: &'a HirModule, owner: &SourceRootId) -> &'a LocalSource {
    let SourceCarrierOutcome::Supported(source) = module.source_carrier_for(owner).unwrap().unwrap()
        else { panic!("supported carrier"); };
    assert_eq!(source.source_root(), owner);
    source
}

#[test]
fn direct_roots_keep_their_original_occurrences_and_source_order() {
    let parse = parsed("my x = 1; x; my id p = p; id 2; 3");
    let module = lower_module(identity(), &parse, SemanticImports::empty()).unwrap();
    assert_eq!(module.items().len(), 5);
    assert_eq!(module.source_carrier_outcomes().len(), 5);
    let HirItem::Binding(x) = &module.items()[0] else { panic!("binding"); };
    let HirItem::Binding(id) = &module.items()[2] else { panic!("binding"); };
    assert_eq!(module.source_carrier_outcomes()[0].0.definition_root(), Some(x.definition_root()));
    assert_eq!(module.source_carrier_outcomes()[2].0.definition_root(), Some(id.definition_root()));
    // The existing binding-carrier suffix still starts at the final ordinary
    // cursor and remains intact before expression children are appended.
    assert_eq!(module.local_source(x.definition_root()).unwrap().unwrap().expressions()[0].occurrence.ordinal(), 6);
    let named = module.local_source(id.definition_root()).unwrap().unwrap();
    assert_eq!(named.expressions().iter().map(|expression| expression.occurrence.ordinal()).collect::<Vec<_>>(), [7, 8]);
    let source_root = parse.source_root();
    let root_nodes: Vec<_> = source_root.children().collect();
    for item in [1, 3, 4] {
        let owner = expression_owner(&module, item);
        assert_eq!(&module.source_carrier_outcomes()[item].0, &owner);
        assert!(owner.definition_root().is_none());
        let root = owner.expression_root().unwrap();
        let HirItem::Expression(ordinary) = &module.items()[item] else { unreachable!(); };
        assert_eq!(root.occurrence(), ordinary.occurrence());
        assert_eq!(module.expression_source_key(root).unwrap(), Some(&root_nodes[item].key()));
        assert_eq!(root_nodes[item].syntax().kind(), SyntaxKind::OperatorChain);
        let source = supported(&module, &owner);
        assert!(source.definition_root().is_none());
        assert_eq!(&source.expression(source.body()).unwrap().occurrence, ordinary.occurrence());
        for expression in source.expressions() {
            assert_eq!(module.occurrence_source_key(&expression.occurrence).unwrap(), Some(&expression.source));
        }
    }
    let owner = expression_owner(&module, 1);
    let source = supported(&module, &owner);
    assert!(matches!(&source.expression(source.body()).unwrap().form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(actual), .. } if actual == x.id()));
}

#[test]
fn forward_references_and_expression_roots_do_not_consume_definition_ordinals() {
    let module = lower("later; my later = 1; 7; my later = 2");
    let definitions: Vec<_> = module.items().iter().filter_map(|item| match item {
        HirItem::Binding(binding) => Some(binding), _ => None,
    }).collect();
    assert_eq!(definitions.len(), 2);
    assert_eq!(definitions[0].id().same_name_ordinal(), 0);
    assert_eq!(definitions[1].id().same_name_ordinal(), 1);
    let owner = expression_owner(&module, 0);
    let source = supported(&module, &owner);
    assert!(matches!(&source.expression(source.body()).unwrap().form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Ambiguous, .. }));
    let module = lower("later; my later = 1");
    let owner = expression_owner(&module, 0);
    let source = supported(&module, &owner);
    let HirItem::Binding(later) = &module.items()[1] else { panic!("binding"); };
    assert!(matches!(&source.expression(source.body()).unwrap().form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(actual), .. } if actual == later.id()));
}

#[test]
fn expression_owned_locals_parameters_groups_catch_and_annotations_have_no_fake_definition() {
    let module = lower(r"{ my id x = x; catch id(1) { payload -> (\ignored -> payload) } }");
    let owner = expression_owner(&module, 0);
    let source = supported(&module, &owner);
    assert_eq!(source.bindings().len(), 1);
    let local = &source.bindings()[0];
    assert_eq!(local.id.source_root(), &owner);
    assert!(local.id.definition_root().is_none());
    assert_eq!(local.parameters[0].id.source_root(), &owner);
    assert!(local.parameters[0].id.definition_root().is_none());
    assert!(module.parameter_source_origin(&local.parameters[0].id).unwrap().is_some());
    assert_eq!(source.named_groups().len(), 1);
    let group = &source.named_groups()[0];
    assert_eq!(group.id.source_root(), &owner);
    assert!(matches!(&group.owner, LocalSourceNamedGroupOwner::Local(id) if id == &local.id));
    let mut inline = false;
    let mut catch = false;
    for expression in source.expressions() {
        if let LocalSourceForm::Lambda { parameter, .. } = &expression.form {
            assert_eq!(parameter.id.source_root(), &owner);
            assert!(parameter.id.definition_root().is_none());
            if parameter.spelling.as_ref() == "ignored" { inline = true; }
        }
        if let LocalSourceForm::Catch { arms, .. } = &expression.form {
            let LocalSourceCatchPattern::Value(LocalSourceCatchValuePattern::Binder(binder)) = &arms[0].pattern
                else { panic!("value binder"); };
            assert_eq!(binder.id.source_root(), &owner);
            assert!(binder.id.owner().is_none());
            catch = true;
        }
    }
    assert!(inline && catch);
    let module = lower("1 as int");
    let owner = expression_owner(&module, 0);
    let source = supported(&module, &owner);
    let LocalSourceForm::Ascription { annotation, .. } = &source.expression(source.body()).unwrap().form
        else { panic!("ascription"); };
    assert_eq!(annotation.source_root(), &owner);
    assert!(annotation.definition_root().is_none());
}

#[test]
fn only_actual_same_artifact_item_occurrences_yield_expression_roots() {
    let module = lower("(1); my value = 2");
    let owner = expression_owner(&module, 0);
    let root = owner.expression_root().unwrap();
    assert!(module.owns_expression_root(root));
    let source = supported(&module, &owner);
    let child = source.expressions().iter().find(|expression| &expression.occurrence != root.occurrence()).unwrap();
    assert!(module.expression_root(&child.occurrence).unwrap().is_none());
    let HirItem::Binding(binding) = &module.items()[1] else { panic!("binding"); };
    assert!(module.expression_root(binding.value().occurrence()).unwrap().is_none());
    let foreign = lower("(1); my value = 2");
    let foreign_owner = expression_owner(&foreign, 0);
    assert!(!module.owns_source_root(&foreign_owner));
    assert!(matches!(module.source_carrier_for(&foreign_owner), Err(HirAvailabilityError::InconsistentIdentity)));
    assert!(matches!(module.expression_root(foreign_owner.expression_root().unwrap().occurrence()), Err(HirAvailabilityError::InconsistentIdentity)));
}

#[test]
fn unsupported_and_recovered_expression_carriers_leave_later_roots_available() {
    for text in ["f(@missing); my later = 7", "{ my local x = x; (1, 2) }; my later = 7"] {
        let module = lower(text);
        let owner = expression_owner(&module, 0);
        assert!(matches!(module.source_carrier_for(&owner).unwrap(), Some(SourceCarrierOutcome::Unsupported(_))));
        assert!(module.local_source_for(&owner).unwrap().is_none());
        let HirItem::Binding(later) = &module.items()[1] else { panic!("later binding"); };
        let source = module.local_source(later.definition_root()).unwrap().unwrap();
        assert_eq!(source.expressions().len(), 1);
        assert_eq!(source.expressions()[0].occurrence.ordinal(), 2);
        assert!(source.bindings().is_empty());
    }
}

#[cfg(feature = "shadow")]
#[test]
fn opt_in_effectful_expression_uses_its_actual_root_and_resolved_declaration() {
    let parse = parsed("act io:\n    our tick: () -> int\nio::tick(); my selected = 1");
    let module = yu_hir::shadow::lower_module_with_local_source(identity(), &parse, SemanticImports::empty()).unwrap();
    let item = module.items().iter().position(|item| matches!(item, HirItem::Expression(_))).unwrap();
    let owner = expression_owner(&module, item);
    let source = supported(&module, &owner);
    assert!(source.expressions().iter().any(|expression| matches!(&expression.form,
        LocalSourceForm::Operation { resolution: yu_hir::SourceOperationResolution::Resolved(_) })));
    assert_eq!(module.items().iter().filter(|item| matches!(item, HirItem::Binding(_))).count(), 1);
    let HirItem::Expression(expression) = &module.items()[item] else { unreachable!(); };
    assert_eq!(&source.expression(source.body()).unwrap().occurrence, expression.occurrence());
}
