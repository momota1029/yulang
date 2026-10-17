use std::sync::Arc;

use yu_hir::{
    FileId, FileKey, HirErrorId, HirErrorKind, HirItem, HirModule, ModuleIdentity, NameResolution,
    ResolvedExpr, SemanticImports, lower_module,
};
use yu_syntax::{ParsedFile, SourceNode, SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

fn parsed(source_text: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(source_text);
    parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()))
}

fn lower_parsed(parsed: &ParsedFile) -> HirModule {
    lower_module(
        ModuleIdentity::source_root(FileId::new(FileKey::new(
            "ordinary-application-admission",
            "admission.yu",
        ))),
        parsed,
        SemanticImports::empty(),
    ).unwrap()
}

fn lower(source_text: &str) -> HirModule { lower_parsed(&parsed(source_text)) }

fn source_nodes_of(root: SourceNode, kind: SyntaxKind, output: &mut Vec<SourceNode>) {
    if root.syntax().kind() == kind { output.push(root.clone()); }
    for child in root.children() { source_nodes_of(child, kind, output); }
}

fn binding<'a>(hir: &'a HirModule, name: &str) -> &'a yu_hir::HirBinding {
    hir.items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding),
            _ => None,
        })
        .unwrap()
}

fn visit<'a>(expression: &'a ResolvedExpr, found: &mut Vec<&'a ResolvedExpr>) {
    found.push(expression);
    match expression {
        ResolvedExpr::Apply { callee, argument, .. } => {
            visit(callee, found);
            visit(argument, found);
        }
        ResolvedExpr::Group { inner, .. } | ResolvedExpr::Lambda { body: inner, .. } => {
            visit(inner, found);
        }
        ResolvedExpr::Integer { .. } | ResolvedExpr::Name { .. } | ResolvedExpr::Error { .. } => {}
    }
}

fn apply_nodes(expression: &ResolvedExpr) -> Vec<&ResolvedExpr> {
    let mut nodes = Vec::new();
    visit(expression, &mut nodes);
    nodes
        .into_iter()
        .filter(|node| matches!(node, ResolvedExpr::Apply { .. }))
        .collect()
}

#[test]
fn fixed_source_is_admitted_through_ordinary_lowering() {
    let hir = lower("my id x = x; my apply f = f 1; my answer = apply id");
    assert!(hir.errors().is_empty());

    let apply = binding(&hir, "apply");
    let ResolvedExpr::Lambda { body, .. } = apply.value() else {
        panic!("formal binding remains a lambda");
    };
    let ResolvedExpr::Apply {
        source_form: SyntaxKind::MlArgument,
        callee,
        argument,
        errors,
        occurrence,
        ..
    } = body.as_ref()
    else {
        panic!("ordinary HIR retains the formal application");
    };
    assert!(errors.is_empty());
    assert!(matches!(callee.as_ref(), ResolvedExpr::Name {
        resolution: NameResolution::Parameter(_), ..
    }));
    assert!(matches!(argument.as_ref(), ResolvedExpr::Integer { spelling, .. } if spelling == "1"));
    assert!(hir.occurrence_source_key(occurrence).unwrap().is_some());
    assert_eq!(hir.source_carrier_outcomes().len(), 3);
    let maximum_carrier_ordinal = hir
        .source_carrier_outcomes()
        .iter()
        .filter_map(|(root, _)| root.definition_root())
        .flat_map(|root| hir.local_source(root).unwrap().unwrap().expressions().iter()
            .map(|expression| expression.occurrence.ordinal()))
        .max()
        .unwrap();
    for child in [callee.occurrence(), argument.occurrence()] {
        assert!(child.ordinal() > maximum_carrier_ordinal);
    }
}

#[test]
fn call_tail_group_and_nested_group_keep_distinct_occurrences() {
    let hir = lower(
        "my callee = f(x); my group_atom = f (x); my group = (f x); my nested = ((f x)); my root = ((f x))",
    );
    assert_eq!(hir.errors().len(), 10, "each undeclared callee and argument retains its diagnostic");
    assert!(hir.errors().iter().all(|error| error.kind() == HirErrorKind::UnresolvedName));
    for name in ["callee", "group_atom", "group", "nested", "root"] {
        let binding = binding(&hir, name);
        let mut nodes = Vec::new();
        visit(binding.value(), &mut nodes);
        let applies: Vec<_> = nodes
            .iter()
            .copied()
            .filter_map(|node| match node {
                ResolvedExpr::Apply { source_form, occurrence, errors, .. } => {
                    assert_eq!(errors.len(), 2, "unresolved callee and argument IDs stay attached");
                    assert!(hir.occurrence_source_key(occurrence).unwrap().is_some());
                    Some(*source_form)
                }
                _ => None,
            })
            .collect();
        assert_eq!(applies.len(), 1, "one retained Apply in {name}");
        if name == "callee" {
            assert_eq!(applies, [SyntaxKind::CallTail]);
        } else {
            assert_eq!(applies, [SyntaxKind::MlArgument]);
        }
        if name != "callee" {
            assert!(nodes.iter().any(|node| matches!(node, ResolvedExpr::Group { .. })));
        }
    }
    let root = binding(&hir, "root");
    let ResolvedExpr::Group { occurrence, inner, .. } = root.value() else {
        panic!("the outer retained Group owns the binding body root");
    };
    assert!(hir.occurrence_source_key(occurrence).unwrap().is_some());
    assert!(matches!(inner.as_ref(), ResolvedExpr::Group { .. }));
}

#[test]
fn unresolved_descendant_errors_are_materialized_once_per_apply_list() {
    let hir = lower("my spine = missing_a missing_b missing_c");
    assert_eq!(hir.errors().len(), 3);
    assert!(hir.errors().iter().all(|error| error.kind() == HirErrorKind::UnresolvedName));
    let applies = apply_nodes(binding(&hir, "spine").value());
    assert_eq!(applies.len(), 2);
    let references: usize = applies
        .iter()
        .map(|node| match node {
            ResolvedExpr::Apply { errors, .. } => errors.len(),
            _ => 0,
        })
        .sum();
    assert_eq!(references, 5, "physical R is two references plus three references");
    assert_eq!(references * std::mem::size_of::<HirErrorId>(), 5 * 4);
    let list_allocations = applies
        .iter()
        .filter(|node| matches!(node, ResolvedExpr::Apply { errors, .. } if !errors.is_empty()))
        .count();
    assert_eq!(list_allocations, 2);
    let outer = applies
        .iter()
        .find_map(|node| match node {
            ResolvedExpr::Apply { errors, callee, .. }
                if matches!(callee.as_ref(), ResolvedExpr::Apply { .. }) => Some(errors),
            _ => None,
        })
        .unwrap();
    assert_eq!(outer.len(), 3);
    assert_eq!(outer.iter().map(|id| id.index()).collect::<Vec<_>>(), [0, 1, 2]);

    let clean = lower("my clean = 1 2 3");
    let clean_applies = apply_nodes(binding(&clean, "clean").value());
    assert_eq!(clean_applies.len(), 2);
    assert!(clean_applies.iter().all(|node| matches!(node,
        ResolvedExpr::Apply { errors, .. } if errors.is_empty()
    )));
    assert_eq!(
        clean_applies
            .iter()
            .filter(|node| matches!(node, ResolvedExpr::Apply { errors, .. } if !errors.is_empty()))
            .count(),
        0,
        "empty error lists retain no HirErrorId reference storage"
    );
}

#[test]
fn grouped_unresolved_spines_forward_errors_without_changing_lists() {
    let hir = lower("my wrapped = ((missing_a missing_b)) missing_c");
    assert_eq!(hir.errors().len(), 3);
    let nodes = apply_nodes(binding(&hir, "wrapped").value());
    assert_eq!(nodes.len(), 2);
    let references: usize = nodes
        .iter()
        .map(|node| match node {
            ResolvedExpr::Apply { errors, .. } => errors.len(),
            _ => 0,
        })
        .sum();
    assert_eq!(references, 5);
    assert_eq!(references * std::mem::size_of::<HirErrorId>(), 5 * 4);
    assert_eq!(nodes.iter().filter(|node| matches!(node,
        ResolvedExpr::Apply { errors, .. } if !errors.is_empty()
    )).count(), 2);
    let all: Vec<_> = nodes
        .iter()
        .flat_map(|node| match node {
            ResolvedExpr::Apply { errors, .. } => errors.iter().map(|id| id.index()).collect::<Vec<_>>(),
            _ => Vec::new(),
        })
        .collect();
    assert!(all.contains(&0) && all.contains(&1) && all.contains(&2));
}

#[test]
fn ambiguous_operand_has_one_owned_event_and_is_referenced_once_per_descendant_list() {
    let hir = lower("my duplicate = 1; my duplicate = 2; my use = duplicate 1");
    let ambiguous: Vec<_> = hir.errors().iter()
        .filter(|error| error.kind() == HirErrorKind::AmbiguousName)
        .collect();
    assert_eq!(ambiguous.len(), 1);
    let applies = apply_nodes(binding(&hir, "use").value());
    assert_eq!(applies.len(), 1);
    let ResolvedExpr::Apply { callee, errors, .. } = applies[0] else { unreachable!() };
    assert!(matches!(callee.as_ref(), ResolvedExpr::Name {
        resolution: NameResolution::Ambiguous, ..
    }));
    assert_eq!(errors.as_ref(), [ambiguous[0].id()]);
}

#[test]
fn grouped_unresolved_nodes_keep_exact_distinct_parse_owned_keys() {
    let parsed = parsed("my grouped = (missing missing); my called = other(other)");
    let hir = lower_parsed(&parsed);
    assert_eq!(hir.errors().len(), 4);
    assert!(hir.errors().iter().all(|error| error.kind() == HirErrorKind::UnresolvedName));
    let ResolvedExpr::Group { occurrence: group_id, inner, .. } = binding(&hir, "grouped").value() else { panic!("Group root"); };
    let ResolvedExpr::Apply { source_form: SyntaxKind::MlArgument, occurrence: apply_id, callee, argument, errors, .. } = inner.as_ref() else { panic!("inner Apply"); };
    let (ResolvedExpr::Name { occurrence: callee_id, resolution: NameResolution::Unresolved, .. }, ResolvedExpr::Name { occurrence: argument_id, resolution: NameResolution::Unresolved, .. }) = (callee.as_ref(), argument.as_ref()) else { panic!("two unresolved names"); };
    assert_eq!(errors.iter().map(|id| id.index()).collect::<Vec<_>>(), [0, 1]);

    let ResolvedExpr::Apply { source_form: SyntaxKind::CallTail, occurrence: call_id, callee: call_callee, argument: call_argument, errors: call_errors, .. } = binding(&hir, "called").value() else { panic!("CallTail Apply"); };
    let (ResolvedExpr::Name { occurrence: call_callee_id, .. }, ResolvedExpr::Name { occurrence: call_argument_id, .. }) = (call_callee.as_ref(), call_argument.as_ref()) else { panic!("CallTail leaves"); };
    assert_eq!(call_errors.iter().map(|id| id.index()).collect::<Vec<_>>(), [2, 3]);

    let mut identifiers = Vec::new();
    source_nodes_of(parsed.source_root(), SyntaxKind::IdentifierExpression, &mut identifiers);
    let mut groups = Vec::new();
    source_nodes_of(parsed.source_root(), SyntaxKind::ParenthesizedExpression, &mut groups);
    let mut applications = Vec::new();
    source_nodes_of(parsed.source_root(), SyntaxKind::MlArgument, &mut applications);
    let mut call_tails = Vec::new();
    source_nodes_of(parsed.source_root(), SyntaxKind::CallTail, &mut call_tails);
    assert_eq!(identifiers.len(), 4);
    assert_eq!(groups.len(), 1);
    assert_eq!(applications.len(), 1);
    assert_eq!(call_tails.len(), 1);
    let identifier_keys: Vec<_> = identifiers.iter().map(|node| node.key()).collect();
    let group_key = groups[0].key();
    let application_key = applications[0].key();
    let call_tail_key = call_tails[0].key();
    assert_ne!(identifier_keys[0], identifier_keys[1]);
    assert_ne!(identifier_keys[2], identifier_keys[3]);
    assert_eq!(hir.occurrence_source_key(callee_id).unwrap(), Some(&identifier_keys[0]));
    assert_eq!(hir.occurrence_source_key(argument_id).unwrap(), Some(&identifier_keys[1]));
    assert_eq!(hir.occurrence_source_key(group_id).unwrap(), Some(&group_key));
    assert_eq!(hir.occurrence_source_key(apply_id).unwrap(), Some(&application_key));
    assert_eq!(hir.occurrence_source_key(call_callee_id).unwrap(), Some(&identifier_keys[2]));
    assert_eq!(hir.occurrence_source_key(call_argument_id).unwrap(), Some(&identifier_keys[3]));
    assert_eq!(hir.occurrence_source_key(call_id).unwrap(), Some(&call_tail_key));
}

#[test]
fn duplicate_event_precedes_staged_operand_diagnostics_and_lists_use_final_dense_ids() {
    let hir = lower("my x = 1; my x = missing missing; my later = later_missing");
    let kinds: Vec<_> = hir.errors().iter().map(|error| error.kind()).collect();
    assert_eq!(kinds, [HirErrorKind::DuplicateDefinition, HirErrorKind::UnresolvedName, HirErrorKind::UnresolvedName, HirErrorKind::UnresolvedName]);
    let duplicate_binding = hir.items().iter().filter_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == "x" => Some(binding),
        _ => None,
    }).nth(1).unwrap();
    let applies = apply_nodes(duplicate_binding.value());
    let outer = applies.iter().find_map(|node| match node {
        ResolvedExpr::Apply { errors, callee, .. } if matches!(callee.as_ref(), ResolvedExpr::Name { .. }) => Some(errors),
        _ => None,
    }).unwrap();
    assert_eq!(outer.iter().map(|id| id.index()).collect::<Vec<_>>(), [1, 2]);
    assert_eq!(hir.errors().iter().map(|error| error.id().index()).collect::<Vec<_>>(), [0, 1, 2, 3]);
}

#[test]
fn comma_bearing_call_tail_refuses_before_operand_resolution() {
    let hir = lower("my bad = f(missing,)");
    assert!(apply_nodes(binding(&hir, "bad").value()).is_empty());
    assert!(!hir.errors().iter().any(|error| error.kind() == HirErrorKind::UnresolvedName));
    assert!(hir.errors().iter().any(|error| error.kind() == HirErrorKind::UnsupportedExpression));

    let grouped = lower("my grouped_tuple = (missing, missing)");
    assert!(apply_nodes(binding(&grouped, "grouped_tuple").value()).is_empty());
    assert!(!grouped.errors().iter().any(|error| error.kind() == HirErrorKind::UnresolvedName));
}

#[test]
fn unsupported_and_recovery_bodies_keep_the_whole_body_refusal() {
    let unsupported = lower("my op = f(a, b)");
    assert!(apply_nodes(binding(&unsupported, "op").value()).is_empty());
    assert!(!unsupported.errors().iter().any(|error| error.kind() == HirErrorKind::UnresolvedName));
    assert_eq!(
        unsupported.errors().iter().filter(|error| error.kind() == HirErrorKind::UnsupportedExpression).count(),
        1
    );

    let recovered = lower("my prior = @; my broken = f(");
    let broken = binding(&recovered, "broken");
    assert!(apply_nodes(broken.value()).is_empty());
    assert!(matches!(broken.value(), ResolvedExpr::Error { errors, .. } if !errors.is_empty()),
        "preflight refusal retains its causal recovery IDs");
    assert!(!recovered.errors().iter().any(|error| error.kind() == HirErrorKind::UnresolvedName));
    assert!(recovered.errors().iter().any(|error| error.kind() == HirErrorKind::UnsupportedExpression));
    assert!(recovered.errors().iter().any(|error| matches!(
        error.kind(),
        HirErrorKind::InheritedMissing | HirErrorKind::InheritedRawError | HirErrorKind::InheritedInvalid
    )));
}
