#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

use std::sync::Arc;
use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports, SourceRootId};
use yu_solver::shadow_apply::{CandidateError, CandidateInference, CandidateSourceValueIdentity};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};
use yu_types::ComponentKind;

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
fn expression_origin_uses_freshen_one_definition_at_distinct_value_shapes() {
    let hir = module(r"my id x = x; id 1; id (\x -> x); my main = 7");
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 2);

    let definition = hir
        .items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "id" => Some(binding),
            _ => None,
        })
        .expect("source definition");
    let expressions: Vec<_> = hir
        .items()
        .iter()
        .filter_map(|item| match item {
            HirItem::Expression(expression) => Some(expression),
            _ => None,
        })
        .collect();
    assert_eq!(expressions.len(), 2);

    let mut local_rows_by_use = Vec::with_capacity(expressions.len());
    for expression in expressions {
        let root = hir
            .expression_root(expression.occurrence())
            .unwrap()
            .unwrap();
        let owner = SourceRootId::Expression(root.clone());
        let call = (0..candidate.source_call_count())
            .map(|index| candidate.source_call(index).unwrap())
            .find(|call| call.owner() == &owner)
            .expect("each expression retains its authentic Call owner");
        assert_eq!(&call.source().occurrence, expression.occurrence());

        let source = hir.local_source_for(&owner).unwrap().unwrap();
        let name_use = source
            .expressions()
            .iter()
            .find(|expression| matches!(
                &expression.form,
                LocalSourceForm::Name {
                    spelling,
                    resolution: LocalSourceResolution::ModuleDef(resolved),
                } if spelling.as_ref() == "id" && resolved == definition.id()
            ))
            .expect("the original resolved module-definition Name");
        let fresh_use = candidate
            .fresh_use(&name_use.occurrence)
            .expect("the original Name occurrence has a retained FreshUse route");
        assert_eq!(fresh_use.occurrence(), &name_use.occurrence);

        let local_rows: Vec<_> = fresh_use
            .rows()
            .filter(|row| row.source_row().is_local())
            .collect();
        for kind in [ComponentKind::Value, ComponentKind::Effect] {
            assert!(
                local_rows.iter().any(|row| row.kind() == kind),
                "each FreshUse image retains a local {kind:?} row"
            );
        }
        local_rows_by_use.push(local_rows);
    }

    let [first, second] = local_rows_by_use.as_slice() else {
        panic!("exactly two expression-origin FreshUse images");
    };
    for row in first {
        assert!(
            second.iter().all(|other| !row.same_identity(other)),
            "distinct expression-origin FreshUse images do not share local row identity"
        );
    }
}

#[test]
fn forward_alias_expression_uses_keep_distinct_fresh_instances() {
    let hir = module(r"alias 1; alias (\x -> x); my alias = id; my id x = x; my main = 7");
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 2);

    let definitions: Vec<_> = hir
        .items()
        .iter()
        .filter_map(|item| match item {
            HirItem::Binding(binding) => Some(binding),
            _ => None,
        })
        .collect();
    assert_eq!(definitions.len(), 3, "no synthetic binder is introduced");
    let alias = definitions
        .iter()
        .find(|binding| binding.name().spelling() == "alias")
        .expect("the source alias definition");
    assert!(definitions.iter().any(|binding| binding.name().spelling() == "id"));
    assert!(definitions
        .iter()
        .any(|binding| binding.name().spelling() == "main"));

    let expressions: Vec<_> = hir
        .items()
        .iter()
        .filter_map(|item| match item {
            HirItem::Expression(expression) => Some(expression),
            _ => None,
        })
        .collect();
    assert_eq!(expressions.len(), 2);

    let mut local_rows_by_use = Vec::with_capacity(expressions.len());
    for expression in expressions {
        let root = hir
            .expression_root(expression.occurrence())
            .unwrap()
            .expect("the expression keeps its authentic root");
        let owner = SourceRootId::Expression(root.clone());
        let call = (0..candidate.source_call_count())
            .map(|index| candidate.source_call(index).unwrap())
            .find(|call| call.owner() == &owner)
            .expect("each expression retains its authentic Call owner");
        assert_eq!(&call.source().occurrence, expression.occurrence());

        let source = hir.local_source_for(&owner).unwrap().unwrap();
        let name_use = source
            .expressions()
            .iter()
            .find(|expression| matches!(
                &expression.form,
                LocalSourceForm::Name {
                    spelling,
                    resolution: LocalSourceResolution::ModuleDef(resolved),
                } if spelling.as_ref() == "alias" && resolved == alias.id()
            ))
            .expect("the original resolved forward-alias Name");
        let fresh_use = candidate
            .fresh_use(&name_use.occurrence)
            .expect("the original Name occurrence retains its FreshUse route");
        assert_eq!(fresh_use.occurrence(), &name_use.occurrence);

        let local_rows: Vec<_> = fresh_use
            .rows()
            .filter(|row| row.source_row().is_local())
            .collect();
        for kind in [ComponentKind::Value, ComponentKind::Effect] {
            assert!(
                local_rows.iter().any(|row| row.kind() == kind),
                "each FreshUse image retains a local {kind:?} row"
            );
        }
        local_rows_by_use.push(local_rows);
    }

    let [first, second] = local_rows_by_use.as_slice() else {
        panic!("exactly two expression-origin FreshUse images");
    };
    for row in first {
        assert!(
            second.iter().all(|other| !row.same_identity(other)),
            "distinct expression-origin FreshUse images do not share local row identity"
        );
    }
}

#[test]
fn discarded_expression_conditions_still_contribute_type_conflicts() {
    for text in [
        "if 1: 1 else: 2;\nmy main = 7",
        "my main = 7;\nif 1: 1 else: 2",
    ] {
        let hir = module(text);
        let candidate = CandidateInference::solve(hir.clone())
            .unwrap_or_else(|error| panic!("{text}: {error:?}"));
        assert!(!candidate.candidate_conflicts().is_empty(), "{text}");

        let expression = hir
            .items()
            .iter()
            .find_map(|item| match item {
                HirItem::Expression(expression) => Some(expression),
                _ => None,
            })
            .expect("the conditional remains an authentic expression item");
        let root = hir
            .expression_root(expression.occurrence())
            .unwrap()
            .expect("the original expression root remains available");
        let owner = SourceRootId::Expression(root.clone());
        let local = hir
            .local_source_for(&owner)
            .unwrap()
            .expect("the authentic expression root retains local source");
        assert_eq!(root.occurrence(), expression.occurrence());
        assert!(candidate.candidate_conflicts().iter().any(|error| {
            local
                .expressions()
                .iter()
                .any(|expression| &expression.occurrence == error.occurrence().occurrence())
        }));

        let bindings: Vec<_> = hir
            .items()
            .iter()
            .filter_map(|item| match item {
                HirItem::Binding(binding) => Some(binding),
                _ => None,
            })
            .collect();
        assert_eq!(bindings.len(), 1, "no synthetic definition is introduced");
        assert_eq!(bindings[0].name().spelling(), "main");
    }
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
fn expression_only_modules_keep_authentic_owners_and_constraints() {
    for (text, has_conflict) in [
        (r"(\x -> x) 1; if true: true else: false", false),
        (r"(\x -> x) 1; if 1: true else: false", true),
    ] {
        let hir = module(text);
        assert_eq!(
            hir.items()
                .iter()
                .filter(|item| matches!(item, HirItem::Binding(_)))
                .count(),
            0,
            "expression-only input must not invent a binding"
        );
        let expressions: Vec<_> = hir
            .items()
            .iter()
            .filter_map(|item| match item {
                HirItem::Expression(expression) => Some(expression),
                _ => None,
            })
            .collect();
        assert_eq!(expressions.len(), 2);

        let owners: Vec<_> = expressions
            .iter()
            .map(|expression| {
                let root = hir
                    .expression_root(expression.occurrence())
                    .unwrap()
                    .unwrap()
                    .clone();
                assert_eq!(root.occurrence(), expression.occurrence());
                let owner = SourceRootId::Expression(root);
                let local = hir.local_source_for(&owner).unwrap().unwrap();
                assert!(local.expressions().iter().any(|local_expression| {
                    &local_expression.occurrence == expression.occurrence()
                }));
                owner
            })
            .collect();
        let [first_owner, second_owner] = owners.as_slice() else {
            panic!("both expression roots retain authentic owners");
        };
        let second_local = hir.local_source_for(second_owner).unwrap().unwrap();

        let candidate = CandidateInference::solve(hir.clone())
            .unwrap_or_else(|error| panic!("{text}: {error:?}"));
        assert_eq!(candidate.source_call_count(), 1);
        let call = candidate.source_call(0).unwrap();
        assert_eq!(call.owner(), first_owner);
        assert_eq!(&call.source().occurrence, expressions[0].occurrence());

        let conflicts = candidate.candidate_conflicts();
        if has_conflict {
            assert!(!conflicts.is_empty(), "{text}");
            assert!(conflicts.iter().all(|error| {
                second_local.expressions().iter().any(|expression| {
                    &expression.occurrence == error.occurrence().occurrence()
                })
            }));
        } else {
            assert!(conflicts.is_empty(), "{text}");
        }
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
