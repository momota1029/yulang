use super::*;

fn parsed(source: &str) -> yu_syntax::ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn source_hir(parsed: &yu_syntax::ParsedFile) -> Arc<HirModule> {
    Arc::new(
        yu_hir::shadow::lower_module_with_source_identity(
            ModuleIdentity::source_root(FileId::new(FileKey::new("test", "shadow-f5.yu"))),
            parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    )
}

fn roots(hir: &HirModule) -> impl Iterator<Item = &DefinitionRootId> {
    hir.items().iter().map(|item| match item {
        HirItem::Binding(binding) => binding.definition_root(),
        _ => panic!("test binding"),
    })
}

#[test]
fn equal_q_and_r_ordinals_retain_exact_member_scheme_namespaces() {
    for (source, recursive) in [
        ("my f x = x; my g y = y", false),
        ("my f x = g; my g y = f", true),
    ] {
        let hir = module(source, "shadow-f5-owners.yu");
        let solved = SolvedModule::solve(collect(hir.clone())).unwrap();
        let before = solved.counters();
        let observer = solved.shadow_closed_schemes();
        let mut roots = roots(&hir);
        let first = observer.for_root(roots.next().unwrap()).unwrap();
        let second = observer.for_root(roots.next().unwrap()).unwrap();
        assert!(!first.same_identity(second));
        if recursive {
            let a = first.recursive_binders().next().unwrap();
            let b = second.recursive_binders().next().unwrap();
            assert_eq!(a.ordinal(), b.ordinal());
            assert!(!a.same_identity(b));
            assert!(a.same_identity(first.recursive_binders().next().unwrap()));
            for binder in [a, b] {
                let (lower, upper) = binder.endpoints();
                let view = binder.scheme().endpoints();
                assert!(matches!(
                    view.positive_value(lower),
                    Ok(PositiveValueView::Function { .. })
                ));
                assert_eq!(view.negative_value(upper), Ok(NegativeValueView::Top));
                let PositiveValueView::Function { result, .. } =
                    view.positive_value(lower).unwrap()
                else {
                    panic!("recursive function")
                };
                let PositiveValueView::Function { result, .. } =
                    view.positive_value(result).unwrap()
                else {
                    panic!("mutual recursive function")
                };
                assert!(
                    matches!(view.positive_value(result), Ok(PositiveValueView::Recursive(id)) if id.ordinal() == binder.ordinal())
                );
            }
        } else {
            let a = first.quantifiers().next().unwrap();
            let b = second.quantifiers().next().unwrap();
            assert_eq!(a.ordinal(), b.ordinal());
            assert!(!a.same_identity(b));
            assert!(a.same_identity(first.quantifiers().next().unwrap()));
        }
        assert_eq!(solved.counters(), before);
    }
}

#[test]
fn source_resolution_uses_exact_root_and_rejects_foreign_artifacts() {
    use yu_hir::shadow::{ShadowArtifact, SourceIdentityError};
    let parsed = parsed("my head = tail; my tail x = x");
    let hir = source_hir(&parsed);
    let solved = SolvedModule::solve(collect(hir.clone())).unwrap();
    let shadow = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let foreign_shadow =
        ShadowArtifact::from_parsed(self::parsed("my head = tail; my tail x = x")).unwrap();
    let foreign_hir = source_hir(&parsed);
    let observer = solved.shadow_closed_schemes();
    let before = solved.counters();
    for root in roots(&hir) {
        let scheme = observer.for_root(root).unwrap();
        assert_eq!(scheme.owner(), root);
        assert_eq!(
            scheme.definition_source_position(&shadow),
            shadow.definition_source_position(&hir, root)
        );
        assert_eq!(
            shadow
                .position(&scheme.definition_source_position(&shadow).unwrap())
                .unwrap()
                .kind(),
            yu_syntax::SyntaxKind::BindingStatement
        );
        assert_eq!(
            scheme.definition_source_position(&foreign_shadow),
            Err(SourceIdentityError::ForeignParse)
        );
    }
    assert!(matches!(
        observer.for_root(roots(&foreign_hir).next().unwrap()),
        Err(ArtifactMismatch)
    ));
    let ordinary = module("my f x = x", "shadow-f5-ordinary.yu");
    let ordinary_solved = SolvedModule::solve(collect(ordinary.clone())).unwrap();
    assert_eq!(
        ordinary_solved
            .shadow_closed_schemes()
            .for_root(roots(&ordinary).next().unwrap())
            .unwrap()
            .definition_source_position(&shadow),
        Err(SourceIdentityError::MissingSource)
    );
    assert_eq!(solved.counters(), before);
}
