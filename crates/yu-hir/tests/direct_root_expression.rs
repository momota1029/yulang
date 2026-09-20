use std::sync::Arc;

use yu_hir::{
    FileId, FileKey, HirErrorAttachment, HirErrorKind, HirErrorOrigin, HirItem, ModuleIdentity,
    NameResolution, ResolvedExpr, SemanticImports, lower_module,
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

const STARTUP_MINIMAL: &str =
    include_str!("../../../tests/perf/runtime/v0/startup/startup_minimal/main.yu");

fn parsed(source: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
}

fn identity() -> ModuleIdentity {
    ModuleIdentity::source_root(FileId::new(FileKey::new("test", "root-expression.yu")))
}

#[test]
fn startup_minimal_source_lowers_to_one_integer_expression() {
    let parsed = parsed(STARTUP_MINIMAL);
    assert_eq!(parsed.green().to_string(), STARTUP_MINIMAL);
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    assert!(parsed.structural_recoveries().is_empty());

    let module = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
    let [HirItem::Expression(ResolvedExpr::Integer { spelling, range })] = module.items() else {
        panic!("startup minimal is one direct-root integer expression")
    };
    assert_eq!(spelling, "42");
    assert_eq!(range, &(0..2));
    assert!(module.errors().is_empty());
    assert!(module.diagnostics().is_empty());
}

#[test]
fn direct_expressions_keep_source_order_and_resolve_the_complete_binding_namespace() {
    let module = lower_module(
        identity(),
        &parsed("x; my x = 1; 42; my y = x"),
        SemanticImports::empty(),
    )
    .unwrap();
    let [
        HirItem::Expression(ResolvedExpr::Name {
            resolution: NameResolution::Resolved(first_x),
            range: first_x_range,
            ..
        }),
        HirItem::Binding(x),
        HirItem::Expression(ResolvedExpr::Integer {
            spelling,
            range: integer_range,
        }),
        HirItem::Binding(y),
    ] = module.items()
    else {
        panic!("mixed direct roots retain their source order")
    };
    assert_eq!(first_x, x.id());
    assert_eq!(first_x_range, &(0..1));
    assert_eq!(spelling, "42");
    assert_eq!(integer_range, &(13..15));
    assert!(matches!(
        y.value(),
        ResolvedExpr::Name { resolution: NameResolution::Resolved(def), .. } if def == x.id()
    ));
    assert!(module.errors().is_empty());
}

#[test]
fn direct_identifier_after_a_unique_binding_resolves_backward() {
    let module =
        lower_module(identity(), &parsed("my x = 1; x"), SemanticImports::empty()).unwrap();
    let [
        HirItem::Binding(x),
        HirItem::Expression(ResolvedExpr::Name {
            resolution, range, ..
        }),
    ] = module.items()
    else {
        panic!("binding followed by a direct-root identifier")
    };
    assert_eq!(resolution, &NameResolution::Resolved(x.id().clone()));
    assert_eq!(range, &(10..11));
    assert!(module.errors().is_empty());
}

#[test]
fn direct_name_errors_attach_to_their_root_items_without_changing_binding_identity() {
    let module = lower_module(
        identity(),
        &parsed("missing; my x = 1; 42; my x = 2; x"),
        SemanticImports::empty(),
    )
    .unwrap();
    let [
        HirItem::Expression(ResolvedExpr::Name {
            resolution: NameResolution::Unresolved,
            ..
        }),
        HirItem::Binding(first_x),
        HirItem::Expression(ResolvedExpr::Integer { .. }),
        HirItem::Binding(second_x),
        HirItem::Expression(ResolvedExpr::Name {
            resolution: NameResolution::Ambiguous,
            ..
        }),
    ] = module.items()
    else {
        panic!("direct name errors remain expression items")
    };
    assert_eq!(first_x.id().same_name_ordinal(), 0);
    assert_eq!(second_x.id().same_name_ordinal(), 1);
    assert_eq!(
        module
            .errors()
            .iter()
            .map(|error| (error.kind(), error.attachment(), error.range().clone()))
            .collect::<Vec<_>>(),
        vec![
            (
                HirErrorKind::UnresolvedName,
                &HirErrorAttachment::DirectRootItem(0),
                0..7,
            ),
            (
                HirErrorKind::DuplicateDefinition,
                &HirErrorAttachment::Definition(second_x.id().clone()),
                26..27,
            ),
            (
                HirErrorKind::AmbiguousName,
                &HirErrorAttachment::DirectRootItem(4),
                33..34,
            ),
        ]
    );
}

#[test]
fn complex_and_recovery_direct_chains_have_distinct_error_ownership() {
    let complex = lower_module(identity(), &parsed("f 1"), SemanticImports::empty()).unwrap();
    let [HirItem::Expression(ResolvedExpr::Error { errors, range })] = complex.items() else {
        panic!("recovery-free complex chain remains an expression item")
    };
    assert_eq!(range, &(0..3));
    assert_eq!(errors.len(), 1);
    assert!(matches!(
        &complex.errors()[errors[0].index() as usize],
        error if error.kind() == HirErrorKind::UnsupportedExpression
            && error.attachment() == &HirErrorAttachment::DirectRootItem(0)
    ));

    let parsed = parsed("f(@missing)");
    assert_eq!(parsed.structural_recoveries().len(), 1);
    assert_eq!(
        parsed.structural_recoveries()[0].direct_root_ordinal(),
        Some(0)
    );
    let recovered = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
    let [HirItem::Expression(ResolvedExpr::Error { errors, .. })] = recovered.items() else {
        panic!("recovery-bearing chain remains an expression item")
    };
    let [error] = recovered.errors() else {
        panic!("the direct-root recovery has one inherited syntax cause")
    };
    assert_eq!(errors.as_ref(), &[error.id()]);
    assert_eq!(error.id().index(), 0);
    assert_eq!(error.origin(), HirErrorOrigin::Syntax);
    assert_eq!(error.kind(), HirErrorKind::InheritedRawError);
    assert_eq!(error.attachment(), &HirErrorAttachment::DirectRootItem(0));
    assert_eq!(error.range(), &(2..3));
    assert_eq!(error.diagnostic(), None);
    assert!(recovered.diagnostics().is_empty());
}

#[test]
fn direct_root_expression_and_error_lower_deterministically_from_one_parsed_file() {
    let parsed = parsed("missing; f 1");
    let first = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
    let second = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();

    assert_eq!(first, second);
    assert!(matches!(
        first.items(),
        [
            HirItem::Expression(ResolvedExpr::Name {
                resolution: NameResolution::Unresolved,
                ..
            }),
            HirItem::Expression(ResolvedExpr::Error { .. }),
        ]
    ));
    assert_eq!(
        first
            .errors()
            .iter()
            .map(|error| (error.id().index(), error.origin(), error.attachment()))
            .collect::<Vec<_>>(),
        vec![
            (
                0,
                HirErrorOrigin::Lowering,
                &HirErrorAttachment::DirectRootItem(0),
            ),
            (
                1,
                HirErrorOrigin::Lowering,
                &HirErrorAttachment::DirectRootItem(1),
            ),
        ]
    );
}

#[test]
fn operator_header_stays_unsupported_while_its_sibling_body_is_an_expression() {
    let module = lower_module(
        identity(),
        &parsed("infix (<+>) 40 41 = 42"),
        SemanticImports::empty(),
    )
    .unwrap();
    let [
        HirItem::Error { .. },
        HirItem::Expression(ResolvedExpr::Integer { spelling, range }),
    ] = module.items()
    else {
        panic!("operator header and its body are sibling direct roots")
    };
    assert_eq!(spelling, "42");
    assert_eq!(range, &(20..22));
    assert_eq!(
        module
            .errors()
            .iter()
            .map(|error| (error.kind(), error.attachment()))
            .collect::<Vec<_>>(),
        vec![(
            HirErrorKind::UnsupportedItem,
            &HirErrorAttachment::DirectRootItem(0)
        )]
    );
}
