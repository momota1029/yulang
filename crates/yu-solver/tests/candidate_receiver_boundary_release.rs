#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

// Provisional source-attachment evidence only. No receiver expiry or Catch
// subtraction is enabled by these tests. Named provider headers replace the
// playground lambda spelling in these adapted construction controls. The
// nested capture uses the supported curried inner Lambda. The
// braced Catch scrutinee is grouped so its braces cannot start the arm list.
use std::sync::Arc;
use yu_hir::shadow::{LocalSourceForm, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.structural_recoveries().is_empty(), "{text}");
    Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "receiver-boundary",
                "source.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    )
}

const SOURCE: &str = "act signal:\n    our ping: () -> int\n\nmy g h x = catch ({ my direct = signal::ping(); h x }) { signal::ping(), _ -> 1, v -> v }\nmy callback_first i = signal::ping()\nmy callback_second i = signal::ping()\nmy first = catch g callback_first 0 { signal::ping(), _ -> 2, v -> v }\nmy second = catch g callback_second 0 { signal::ping(), _ -> 3, v -> v }";

#[test]
fn captured_formal_attaches_to_its_original_receiver_not_the_nested_lambda() {
    let hir = module(SOURCE);
    let candidate = CandidateInference::solve_scoped_experiment(hir.clone()).unwrap();
    let g = hir
        .items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "g" => Some(binding),
            _ => None,
        })
        .unwrap();
    let source = hir.local_source(g.definition_root()).unwrap().unwrap();
    let lambda = source.expression(source.body()).unwrap();
    let LocalSourceForm::Lambda { body, .. } = &lambda.form else {
        panic!("g receiver");
    };
    let body = source.expression(body).unwrap();
    let mut captured = 0;
    let mut direct = 0;
    for index in 0..candidate.source_call_count() {
        let call = candidate.source_call(index).unwrap();
        if call.lexical_formal_use().is_some_and(|name| {
            matches!(&name.form,
            LocalSourceForm::Name { spelling, .. } if spelling.as_ref() == "h")
        }) {
            let attachment = call.experimental_receiver_attachment().unwrap();
            assert_eq!(attachment.receiver_lambda(), &lambda.occurrence);
            assert_eq!(attachment.receiver_body(), &body.occurrence);
            assert_ne!(
                attachment.receiver_region(),
                attachment.lexical_region(),
                "captured h is used in the curried inner lambda region"
            );
            assert_eq!(
                call.directional_introduction().unwrap().original_lambda(),
                attachment.receiver_lambda()
            );
            let scope = attachment.original_scope();
            assert!(
                candidate
                    .scoped_scope_lineage()
                    .any(|(_, original, occurrence)| original == scope
                        && occurrence == &call.source().occurrence)
            );
            captured += 1;
        }
        if matches!(call.callee_source().form, LocalSourceForm::Operation { .. }) {
            assert!(
                call.experimental_receiver_attachment().is_none(),
                "direct body operations do not acquire a formal receiver attachment"
            );
            direct += 1;
        }
    }
    assert_eq!(captured, 1);
    assert!(direct >= 3);
}

#[test]
fn ordinary_candidate_does_not_construct_experimental_attachments() {
    let candidate = CandidateInference::solve(module(SOURCE)).unwrap();
    for index in 0..candidate.source_call_count() {
        assert!(
            candidate
                .source_call(index)
                .unwrap()
                .experimental_receiver_attachment()
                .is_none()
        );
    }
}

#[test]
fn captured_local_helper_keeps_structural_effect_copies_separate_from_value_demands() {
    let hir = module(
        "act signal:\n    our ping: () -> int\n\nmy invoke cb = cb 0\nmy g h = catch ({ my step i = h i; my direct = signal::ping(); invoke step }) { signal::ping(), _ -> 1, v -> v }\nmy callback_first i = signal::ping()\nmy callback_second i = signal::ping()\nmy first = catch g callback_first { signal::ping(), _ -> 2, v -> v }\nmy second = catch g callback_second { signal::ping(), _ -> 3, v -> v }",
    );
    let candidate = CandidateInference::solve_scoped_experiment(hir).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let mut captured = 0;
    for index in 0..candidate.source_call_count() {
        let call = candidate.source_call(index).unwrap();
        if call.lexical_formal_use().is_some_and(|name| {
            matches!(&name.form,
            LocalSourceForm::Name { spelling, .. } if spelling.as_ref() == "h")
        }) {
            let attachment = call.experimental_receiver_attachment().unwrap();
            assert_ne!(attachment.receiver_region(), attachment.lexical_region());
            assert_eq!(
                attachment.receiver_lambda(),
                call.directional_introduction().unwrap().original_lambda()
            );
            captured += 1;
        }
    }
    assert_eq!(captured, 1);
}

// This join records source construction facts only. It does not select an
// operational receiver, establish Oracle eligibility, or license a discharge.
#[derive(Debug)]
struct CalleeRouteObservation {
    occurrence: yu_hir::HirOccurrenceId,
    source: yu_syntax::SourceNodeKey,
    range: std::ops::Range<usize>,
    form: &'static str,
    block_bindings: Option<usize>,
}

struct NamedHeaderCallJoin {
    group: yu_hir::shadow::LocalSourceNamedGroupId,
    group_owner: yu_hir::shadow::LocalSourceNamedGroupOwner,
    group_formals: usize,
    introducing_lambda: yu_hir::HirOccurrenceId,
    terminal_lambda: yu_hir::HirOccurrenceId,
    terminal_body: yu_hir::HirOccurrenceId,
    lexical_group: yu_hir::shadow::LocalSourceNamedGroupId,
    lexical_owner: yu_hir::shadow::LocalSourceNamedGroupOwner,
    lexical_enclosing: Option<yu_hir::shadow::LocalSourceNamedGroupId>,
    route: Vec<CalleeRouteObservation>,
}

fn named_header_call_joins(
    hir: &HirModule,
    candidate: &CandidateInference,
    formal_spelling: &str,
) -> Vec<NamedHeaderCallJoin> {
    let mut joins = Vec::new();
    for index in 0..candidate.source_call_count() {
        let call = candidate.source_call(index).unwrap();
        let Some(formal) = call.formal_registration() else {
            continue;
        };
        if formal.spelling.as_ref() != formal_spelling {
            continue;
        }
        let source = hir.local_source(call.owner()).unwrap().unwrap();
        let introduction = call
            .directional_introduction()
            .expect("authentic omitted-formal introduction");
        assert_eq!(introduction.original_owner(), call.owner());
        assert_eq!(introduction.original_formal(), &formal.id);
        let members: Vec<_> = source
            .named_groups()
            .iter()
            .flat_map(|group| {
                group
                    .formals
                    .iter()
                    .filter(|member| member.parameter == formal.id)
                    .map(move |member| (group, member))
            })
            .collect();
        assert_eq!(
            members.len(),
            1,
            "formal identity determines one retained header member"
        );
        let (group, member) = members[0];
        let introducing = source.expression(&member.lambda).unwrap();
        assert_eq!(&introducing.occurrence, introduction.original_lambda());
        let LocalSourceForm::Lambda { parameter, .. } = &introducing.form else {
            panic!("introducing Lambda");
        };
        assert_eq!(parameter.id, formal.id);
        let terminal = source.expression(&group.terminal_lambda).unwrap();
        let LocalSourceForm::Lambda { body, .. } = &terminal.form else {
            panic!("terminal header Lambda");
        };
        assert_eq!(body, &group.terminal_body);
        let terminal_body = source.expression(&group.terminal_body).unwrap();
        let lexical_group = source
            .named_group(call.source().named_group.as_ref().unwrap())
            .unwrap();
        let lexical_name = call.lexical_formal_use().unwrap();
        let mut current = call.callee_source();
        let mut route = Vec::new();
        loop {
            let (form, block_bindings) = match &current.form {
                LocalSourceForm::Group { .. } => ("Group", None),
                LocalSourceForm::Ascription { .. } => ("Ascription", None),
                LocalSourceForm::Block { bindings, .. } => ("Block", Some(bindings.len())),
                LocalSourceForm::Name { .. } => ("Name", None),
                _ => panic!("unexpected authentic formal callee route"),
            };
            route.push(CalleeRouteObservation {
                occurrence: current.occurrence.clone(),
                source: current.source.clone(),
                range: current.range.clone(),
                form,
                block_bindings,
            });
            assert!(hir.owns_occurrence(&current.occurrence));
            assert!(current.range.start < current.range.end);
            let next = match &current.form {
                LocalSourceForm::Group { inner } | LocalSourceForm::Ascription { inner, .. } => {
                    inner
                }
                LocalSourceForm::Block {
                    final_expression, ..
                } => final_expression,
                LocalSourceForm::Name {
                    resolution: yu_hir::shadow::LocalSourceResolution::Parameter(id),
                    ..
                } => {
                    assert_eq!(id, &formal.id);
                    assert_eq!(current.occurrence, lexical_name.occurrence);
                    break;
                }
                _ => panic!("callee route must end at the exact registered formal Name"),
            };
            current = source.expression(next).unwrap();
        }
        for observation in &route {
            let actual = source
                .expressions()
                .iter()
                .find(|expression| expression.occurrence == observation.occurrence)
                .unwrap();
            assert_eq!(actual.source, observation.source);
            assert_eq!(actual.range, observation.range);
        }
        joins.push(NamedHeaderCallJoin {
            group: group.id.clone(),
            group_owner: group.owner.clone(),
            group_formals: group.formals.len(),
            introducing_lambda: introducing.occurrence.clone(),
            terminal_lambda: terminal.occurrence.clone(),
            terminal_body: terminal_body.occurrence.clone(),
            lexical_group: lexical_group.id.clone(),
            lexical_owner: lexical_group.owner.clone(),
            lexical_enclosing: lexical_group.enclosing.clone(),
            route,
        });
    }
    joins
}

#[test]
fn source_join_retains_compose_header_and_distinct_introducing_and_terminal_lambdas() {
    let hir = module("my compose f g x = f (g x)");
    let candidate = CandidateInference::solve_scoped_experiment(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    for formal in ["f", "g"] {
        let joins = named_header_call_joins(&hir, &candidate, formal);
        assert_eq!(joins.len(), 1);
        let join = &joins[0];
        assert_eq!(join.group_formals, 3);
        assert_ne!(join.introducing_lambda, join.terminal_lambda);
        assert_ne!(join.terminal_lambda, join.terminal_body);
        assert_eq!(join.group, join.lexical_group);
        assert!(matches!(
            join.group_owner,
            yu_hir::shadow::LocalSourceNamedGroupOwner::Definition(_)
        ));
    }
}

#[test]
fn source_join_keeps_captured_outer_formal_and_local_lexical_group_distinct() {
    let hir = module("my invoke cb = cb 0; my outer h x = { my step i = h i; invoke step }");
    let candidate = CandidateInference::solve_scoped_experiment(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let joins = named_header_call_joins(&hir, &candidate, "h");
    assert_eq!(joins.len(), 1);
    let join = &joins[0];
    assert_eq!(join.group_formals, 2);
    assert_ne!(join.introducing_lambda, join.terminal_lambda);
    assert_ne!(join.group, join.lexical_group);
    assert_eq!(join.lexical_enclosing.as_ref(), Some(&join.group));
    assert!(matches!(
        join.group_owner,
        yu_hir::shadow::LocalSourceNamedGroupOwner::Definition(_)
    ));
    assert!(matches!(
        join.lexical_owner,
        yu_hir::shadow::LocalSourceNamedGroupOwner::Local(_)
    ));
}

#[test]
fn source_join_retains_direct_and_nonempty_block_callee_routes_without_selecting_policy() {
    for (text, block_bindings) in [
        ("my outer f x = f x", None),
        ("my outer f x = ({ my unused = 0; f }) x", Some(1)),
    ] {
        let hir = module(text);
        let candidate = CandidateInference::solve_scoped_experiment(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        let joins = named_header_call_joins(&hir, &candidate, "f");
        assert_eq!(joins.len(), 1);
        let join = &joins[0];
        assert_eq!(join.group_formals, 2);
        assert_ne!(join.introducing_lambda, join.terminal_lambda);
        assert_eq!(join.group, join.lexical_group);
        assert_eq!(
            join.route.iter().find_map(|step| step.block_bindings),
            block_bindings
        );
        assert_eq!(join.route.last().unwrap().form, "Name");
    }
}

#[test]
fn source_join_preserves_group_ascription_and_zero_formal_initializer_context() {
    for (text, ascribed) in [
        ("my outer f x = ((f as int -> int)) x", true),
        ("my outer f x = { my value = f x; value }", false),
    ] {
        let hir = module(text);
        let candidate = CandidateInference::solve_scoped_experiment(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        let joins = named_header_call_joins(&hir, &candidate, "f");
        assert_eq!(joins.len(), 1);
        assert_eq!(joins[0].group, joins[0].lexical_group);
        if ascribed {
            assert!(joins[0].route.iter().any(|step| step.form == "Group"));
            assert!(joins[0].route.iter().any(|step| step.form == "Ascription"));
        } else {
            let source = hir
                .local_source(candidate.source_call(0).unwrap().owner())
                .unwrap()
                .unwrap();
            let value = source
                .bindings()
                .iter()
                .find(|binding| binding.spelling.as_ref() == "value")
                .unwrap();
            assert!(value.parameters.is_empty());
            assert_eq!(source.named_groups().len(), 1);
        }
    }
}

#[test]
fn source_join_ordinary_identity_names_gain_no_special_formal_introduction() {
    for identity in ["pass", "relay"] {
        let hir = module(&format!(
            "my {identity} value = value; my outer f x = {identity} (f x)"
        ));
        let candidate = CandidateInference::solve_scoped_experiment(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        let joins = named_header_call_joins(&hir, &candidate, "f");
        assert_eq!(joins.len(), 1);
        assert_eq!(joins[0].group, joins[0].lexical_group);
        let mut module_calls = 0;
        for index in 0..candidate.source_call_count() {
            let call = candidate.source_call(index).unwrap();
            if matches!(&call.callee_source().form, LocalSourceForm::Name { spelling, resolution: yu_hir::shadow::LocalSourceResolution::ModuleDef(_) }
                if spelling.as_ref() == identity)
            {
                assert!(call.formal_registration().is_none());
                assert!(call.directional_introduction().is_none());
                module_calls += 1;
            }
        }
        assert_eq!(module_calls, 1);
        // Absence of a formal introduction is not an absence-of-effects claim.
    }
}
