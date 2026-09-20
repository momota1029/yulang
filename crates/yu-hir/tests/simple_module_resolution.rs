use std::sync::Arc;

use yu_hir::{
    FileId, FileKey, HirErrorKind, HirItem, HirVisibility, ModuleIdentity, NameResolution,
    ResolvedExpr, SemanticImports, lower_module,
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

const FIXTURE: &str = include_str!("fixtures/simple_module_name_resolution.yu");

fn parsed(source: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
}

fn identity() -> ModuleIdentity {
    ModuleIdentity::source_root(FileId::new(FileKey::new("test", "simple.yu")))
}

#[test]
fn public_parser_preflight_and_fixture_resolution_are_recovery_free() {
    let parsed = parsed(FIXTURE);
    assert_eq!(parsed.green().to_string(), FIXTURE);
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    assert!(parsed.structural_recoveries().is_empty());

    let module = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
    let [HirItem::Binding(x), HirItem::Binding(y)] = module.items() else {
        panic!("two bindings")
    };
    assert_eq!(x.visibility(), HirVisibility::Private);
    assert!(
        matches!(x.value(), ResolvedExpr::Integer { spelling, range } if spelling == "1" && range == &(7..8))
    );
    assert!(matches!(
        y.value(),
        ResolvedExpr::Name { name, resolution: NameResolution::Resolved(def), range }
            if name.spelling() == "x" && range == &(17..18) && def == x.id()
    ));
    assert!(module.errors().is_empty());
    assert!(module.diagnostics().is_empty());
}

#[test]
fn forward_references_and_all_binding_visibilities_share_the_planned_namespace() {
    let module = lower_module(
        identity(),
        &parsed("pub z = x; our x = 1; my y = z"),
        SemanticImports::empty(),
    )
    .unwrap();
    let [
        HirItem::Binding(z),
        HirItem::Binding(x),
        HirItem::Binding(y),
    ] = module.items()
    else {
        panic!("bindings")
    };
    assert_eq!(z.visibility(), HirVisibility::Public);
    assert_eq!(x.visibility(), HirVisibility::Our);
    assert!(
        matches!(z.value(), ResolvedExpr::Name { resolution: NameResolution::Resolved(def), .. } if def == x.id())
    );
    assert!(
        matches!(y.value(), ResolvedExpr::Name { resolution: NameResolution::Resolved(def), .. } if def == z.id())
    );
}

#[test]
fn duplicate_names_are_ambiguous_and_unresolved_names_remain_names() {
    let module = lower_module(
        identity(),
        &parsed("my x = 1; my x = 2; my y = x; my z = nope"),
        SemanticImports::empty(),
    )
    .unwrap();
    assert!(
        module
            .errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::DuplicateDefinition)
    );
    assert!(
        module
            .errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::AmbiguousName)
    );
    assert!(
        module
            .errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::UnresolvedName)
    );
    let [_, _, HirItem::Binding(y), HirItem::Binding(z)] = module.items() else {
        panic!("bindings")
    };
    assert!(matches!(
        y.value(),
        ResolvedExpr::Name {
            resolution: NameResolution::Ambiguous,
            ..
        }
    ));
    assert!(matches!(
        z.value(),
        ResolvedExpr::Name {
            resolution: NameResolution::Unresolved,
            ..
        }
    ));
}

#[test]
fn malformed_bodies_keep_admitted_definition_identity() {
    let module = lower_module(
        identity(),
        &parsed("my x =; my y = x"),
        SemanticImports::empty(),
    )
    .unwrap();
    let [HirItem::Binding(x), HirItem::Binding(y)] = module.items() else {
        panic!("bindings")
    };
    assert!(matches!(x.value(), ResolvedExpr::Error { .. }));
    assert!(
        matches!(y.value(), ResolvedExpr::Name { resolution: NameResolution::Resolved(def), .. } if def == x.id())
    );
}

#[test]
fn recovery_projection_keeps_preorder_and_direct_root_attachment() {
    let parsed = parsed("my x = @; my y = 1");
    let recoveries = parsed.structural_recoveries();
    assert!(
        recoveries
            .windows(2)
            .all(|pair| pair[0].ordinal() < pair[1].ordinal())
    );
    assert!(
        recoveries
            .iter()
            .all(|recovery| recovery.direct_root_ordinal() == Some(0))
    );
    let module = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
    assert_eq!(
        module
            .errors()
            .iter()
            .filter(|error| error.kind() == HirErrorKind::InheritedRawError)
            .count(),
        recoveries.len()
    );
    let [HirItem::Binding(binding), _] = module.items() else {
        panic!("bindings")
    };
    let ResolvedExpr::Error { errors, .. } = binding.value() else {
        panic!("recovered body is an error value")
    };
    assert!(
        errors
            .windows(2)
            .all(|pair| pair[0].index() < pair[1].index())
    );
    assert_eq!(
        errors
            .iter()
            .filter(
                |id| module.errors()[id.index() as usize].kind() == HirErrorKind::InheritedRawError
            )
            .count(),
        recoveries.len()
    );
}

#[test]
fn plain_targets_only_admit_identifier_definitions() {
    let module = lower_module(
        identity(),
        &parsed("my (x, y) = 1; my $z = 2"),
        SemanticImports::empty(),
    )
    .unwrap();
    assert!(
        module
            .items()
            .iter()
            .all(|item| matches!(item, HirItem::Error { .. }))
    );
    assert_eq!(
        module
            .errors()
            .iter()
            .filter(|error| error.kind() == HirErrorKind::UnsupportedTarget)
            .count(),
        2
    );
}

#[test]
fn unique_definition_ids_ignore_trivia_and_differently_named_siblings() {
    let first = lower_module(
        identity(),
        &parsed("my x = 1; my y = 2"),
        SemanticImports::empty(),
    )
    .unwrap();
    let second = lower_module(
        identity(),
        &parsed("my y = 2;\n\nmy x = 1"),
        SemanticImports::empty(),
    )
    .unwrap();
    let [HirItem::Binding(first_x), _] = first.items() else {
        panic!("first x")
    };
    let [_, HirItem::Binding(second_x)] = second.items() else {
        panic!("second x")
    };
    assert_eq!(first_x.id(), second_x.id());
    assert_eq!(
        FileId::new(FileKey::new("one", "same.yu")),
        FileId::new(FileKey::new("one", "same.yu"))
    );
    assert_ne!(
        FileId::new(FileKey::new("one", "same.yu")),
        FileId::new(FileKey::new("two", "same.yu"))
    );
}

#[test]
fn structural_errors_keep_global_preorder_and_attachments() {
    let module = lower_module(
        identity(),
        &parsed("my {1, b} = 1; my y =; my z = y"),
        SemanticImports::empty(),
    )
    .unwrap();
    let errors = module.errors();
    assert!(matches!(
        (errors[0].kind(), errors[0].attachment()),
        (
            HirErrorKind::InheritedInvalid,
            yu_hir::HirErrorAttachment::DirectRootItem(0)
        )
    ));
    assert!(matches!(
        (errors[1].kind(), errors[1].attachment()),
        (
            HirErrorKind::InheritedMissing,
            yu_hir::HirErrorAttachment::Value(_)
        )
    ));
    assert!(
        errors[..2]
            .iter()
            .all(|error| error.origin() == yu_hir::HirErrorOrigin::Syntax)
    );
    assert!(
        errors[2..]
            .iter()
            .all(|error| error.origin() == yu_hir::HirErrorOrigin::Lowering)
    );
}

#[test]
fn recovery_bodies_do_not_lookup_retry_operands_and_keep_definitions() {
    let module = lower_module(
        identity(),
        &parsed("my x = @ y; my z = x"),
        SemanticImports::empty(),
    )
    .unwrap();
    let [HirItem::Binding(x), HirItem::Binding(z)] = module.items() else {
        panic!("direct bindings")
    };
    assert!(matches!(x.value(), ResolvedExpr::Error { errors, .. } if !errors.is_empty()));
    assert!(matches!(
        z.value(),
        ResolvedExpr::Name {
            resolution: NameResolution::Resolved(def),
            ..
        } if def == x.id()
    ));
    assert!(
        module
            .errors()
            .iter()
            .all(|error| error.kind() != HirErrorKind::UnresolvedName)
    );
}

#[test]
fn indented_and_unsupported_bodies_stay_error_values_without_nested_lowering() {
    let module = lower_module(
        identity(),
        &parsed("my x =\n  my y = nope\n  y\nmy z = x; my w = f 1"),
        SemanticImports::empty(),
    )
    .unwrap();
    let [
        HirItem::Binding(x),
        HirItem::Binding(z),
        HirItem::Binding(w),
    ] = module.items()
    else {
        panic!("only direct bindings")
    };
    assert!(matches!(x.value(), ResolvedExpr::Error { .. }));
    assert!(matches!(w.value(), ResolvedExpr::Error { .. }));
    assert!(matches!(
        z.value(),
        ResolvedExpr::Name {
            resolution: NameResolution::Resolved(def),
            ..
        } if def == x.id()
    ));
    assert!(
        module
            .errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::UnsupportedExpression)
    );
    assert!(
        module
            .errors()
            .iter()
            .all(|error| error.kind() != HirErrorKind::UnresolvedName)
    );
}

#[test]
fn recovery_bearing_indented_body_keeps_syntax_cause_then_one_outer_error() {
    let module = lower_module(
        identity(),
        &parsed("my outer =\n  my nested = nope\n  @\nmy use = outer"),
        SemanticImports::empty(),
    )
    .unwrap();
    let [HirItem::Binding(outer), HirItem::Binding(use_outer)] = module.items() else {
        panic!("direct bindings")
    };
    let ResolvedExpr::Error { errors, .. } = outer.value() else {
        panic!("recovery-bearing indented body is an error value")
    };

    assert_eq!(
        module
            .errors()
            .iter()
            .map(|error| {
                (
                    error.id().index(),
                    error.kind(),
                    error.origin(),
                    error.diagnostic().map(|id| id.index()),
                )
            })
            .collect::<Vec<_>>(),
        vec![
            (
                0,
                HirErrorKind::InheritedRawError,
                yu_hir::HirErrorOrigin::Syntax,
                None
            ),
            (
                1,
                HirErrorKind::UnsupportedExpression,
                yu_hir::HirErrorOrigin::Lowering,
                Some(0),
            ),
        ]
    );
    assert_eq!(
        errors.iter().map(|id| id.index()).collect::<Vec<_>>(),
        vec![0, 1]
    );
    assert!(module.errors().iter().all(
        |error| matches!(error.attachment(), yu_hir::HirErrorAttachment::Value(id) if id == outer.id())
    ));
    assert_eq!(module.diagnostics().len(), 1);
    assert_eq!(module.diagnostics()[0].id().index(), 0);
    assert_eq!(module.diagnostics()[0].error().index(), 1);
    assert_eq!(
        module.diagnostics()[0].kind(),
        HirErrorKind::UnsupportedExpression
    );
    assert!(
        module
            .errors()
            .iter()
            .all(|error| error.kind() != HirErrorKind::UnresolvedName)
    );
    assert!(matches!(
        use_outer.value(),
        ResolvedExpr::Name { resolution: NameResolution::Resolved(def), .. } if def == outer.id()
    ));
}

#[test]
fn recovery_targets_and_nested_bindings_never_enter_the_namespace() {
    let module = lower_module(
        identity(),
        &parsed("my @ x = 1; my outer =\n  my inner = 1\n  inner\nmy use = x"),
        SemanticImports::empty(),
    )
    .unwrap();
    let [
        HirItem::Error { .. },
        HirItem::Binding(outer),
        HirItem::Binding(use_x),
    ] = module.items()
    else {
        panic!("only direct roots")
    };
    assert!(matches!(outer.value(), ResolvedExpr::Error { .. }));
    assert!(matches!(
        use_x.value(),
        ResolvedExpr::Name {
            resolution: NameResolution::Unresolved,
            ..
        }
    ));
    assert_eq!(
        module
            .errors()
            .iter()
            .filter(|error| error.kind() == HirErrorKind::UnsupportedTarget)
            .count(),
        1
    );
}

#[test]
fn duplicate_and_ambiguous_use_errors_have_one_marker_per_occurrence() {
    let module = lower_module(
        identity(),
        &parsed("my x = 1; my x = 2; my y = x; my z = x"),
        SemanticImports::empty(),
    )
    .unwrap();
    assert_eq!(
        module
            .errors()
            .iter()
            .filter(|error| error.kind() == HirErrorKind::DuplicateDefinition)
            .count(),
        1
    );
    assert_eq!(
        module
            .errors()
            .iter()
            .filter(|error| error.kind() == HirErrorKind::AmbiguousName)
            .count(),
        2
    );
}

#[test]
fn admitted_definition_ids_survive_body_edits() {
    let valid = lower_module(identity(), &parsed("my x = 1"), SemanticImports::empty()).unwrap();
    let recovered =
        lower_module(identity(), &parsed("my x = @"), SemanticImports::empty()).unwrap();
    let [HirItem::Binding(valid_x)] = valid.items() else {
        panic!("valid binding")
    };
    let [HirItem::Binding(recovered_x)] = recovered.items() else {
        panic!("recovered binding")
    };
    assert_eq!(valid_x.id(), recovered_x.id());
    assert!(matches!(recovered_x.value(), ResolvedExpr::Error { .. }));
}

#[test]
fn recovery_lowering_is_deterministic() {
    let parsed = parsed("my x = @; my y = x");
    let first = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
    let second = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
    assert_eq!(first, second);
}
