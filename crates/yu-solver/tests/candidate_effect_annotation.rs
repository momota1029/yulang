#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]
use std::sync::Arc;
use yu_hir::shadow::{
    LocalSourceForm, LocalSourceResolution, SourceAnnotationValue, lower_module_with_local_source,
};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateError, CandidateInference};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Result<Arc<HirModule>, yu_hir::HirAvailabilityError> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(
        parsed.structural_recoveries().is_empty(),
        "valid source fixture"
    );
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("effect-annotation", "source.yu"))),
        &parsed,
        SemanticImports::empty(),
    )
    .map(Arc::new)
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

#[test]
fn whole_binding_annotation_uses_real_declaration_and_keeps_bare_parameter_value_role() {
    let hir = module("act E\nmy id x: int -> [E] int = x").unwrap();
    let declarations = hir.source_effect_declarations();
    assert_eq!(declarations.len(), 1);
    let source = hir
        .local_source(binding(&hir, "id").definition_root())
        .unwrap()
        .unwrap();
    let annotation = source.annotation().unwrap();
    let SourceAnnotationValue::Function { argument, result } = &annotation.ty.value else {
        panic!("whole binding arrow")
    };
    assert!(matches!(argument.value, SourceAnnotationValue::Int));
    assert!(matches!(result.value, SourceAnnotationValue::Int));
    assert_eq!(
        result.effects.as_ref().unwrap().concrete,
        vec![declarations[0].id.clone()]
    );
    assert!(source.expressions().iter().any(|expression| matches!(&expression.form,
        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(_) } if spelling.as_ref() == "x")));
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 0);
    assert!(
        candidate
            .export(binding(&hir, "id").definition_root())
            .unwrap()
            .bounds()
            .any(|bound| bound.lower().children().is_some())
    );
}

#[test]
fn annotation_checks_whole_generated_lambda_and_preserves_fresh_alias_uses() {
    let hir =
        module("act E\nmy id x: int -> [E] int = x; my first = id 1; my second = id 1").unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    for name in ["first", "second"] {
        let graph = candidate
            .export(binding(&hir, name).definition_root())
            .unwrap();
        assert!(graph.bounds().any(|bound| bound.lower().leaf()
            == Some(yu_solver::shadow_apply::CandidateGraphLeaf::IntPositive)));
    }
    let wrong = module("act E\nmy ident y = y; my wrong x: int -> [E] int = ident").unwrap();
    let wrong = CandidateInference::solve(wrong).unwrap();
    assert!(
        !wrong.candidate_conflicts().is_empty(),
        "result-only annotation acceptance would miss the generated whole-lambda mismatch"
    );
}

#[test]
fn unresolved_ambiguous_and_unsupported_annotations_do_not_gain_permissions() {
    for text in [
        "act E\nmy id x: int -> [Missing] int = x",
        "act E\nact E\nmy id x: int -> [E] int = x",
        "act E(int)\nmy id x = x",
        "act E\nmy id x: Other -> [E] int = x",
        "act E\nmy higher f: (int -> [E] int) -> int = f 1",
    ] {
        match module(text) {
            Err(_) => {}
            Ok(hir) => assert!(
                matches!(
                    CandidateInference::solve(hir),
                    Err(CandidateError::Unsupported)
                ),
                "{text}"
            ),
        }
    }
    let a = module("act E\nmy id x: int -> [E] int = x").unwrap();
    let b = module("act E\nmy id x: int -> [E] int = x").unwrap();
    assert_ne!(
        a.source_effect_declarations()[0].id,
        b.source_effect_declarations()[0].id,
        "declaration identity retains the actual source owner, not the spelling"
    );
}

#[test]
fn local_covariant_effect_annotations_survive_use_and_reject_other_effects() {
    let accepted = module("act E\nmy value = { my local x: int -> [E] int = x; local }; my accepts: int -> [E] int = value").unwrap();
    let candidate = CandidateInference::solve(accepted).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());

    let rejected = module("act E\nact F\nmy value = { my local x: int -> [E] int = x; local }; my rejects: int -> [F] int = value").unwrap();
    let candidate = CandidateInference::solve(rejected).unwrap();
    assert!(!candidate.candidate_conflicts().is_empty(), "local E support remains visible at a later F-only boundary");
}

#[test]
fn local_symbolic_effect_tail_keeps_late_concrete_flow() {
    let accepted = module("act E\nmy id x: int -> [E] int = x\nmy outer = { my local: int -> ['a] int = id; local }; my accepts: int -> [E] int = outer").unwrap();
    let candidate = CandidateInference::solve(accepted).unwrap();
    assert!(candidate.candidate_conflicts().is_empty(), "{:?}", candidate.candidate_conflicts());

    let rejected = module("act E\nact F\nmy id x: int -> [E] int = x\nmy outer = { my local: int -> ['a] int = id; local }; my rejects: int -> [F] int = outer").unwrap();
    let candidate = CandidateInference::solve(rejected).unwrap();
    assert!(!candidate.candidate_conflicts().is_empty(), "late E through the local symbolic tail remains checked");
}

#[test]
fn local_symbolic_effect_tails_freshen_independently_per_use() {
    let hir = module("act E\nmy id x: int -> [E] int = x\nmy outer = { my local: int -> ['a] int = id; my first = local; my second = local; first }").unwrap();
    let source = hir.local_source(binding(&hir, "outer").definition_root()).unwrap().unwrap();
    let local = source.bindings().iter().find(|binding| binding.spelling.as_ref() == "local").unwrap();
    let uses: Vec<_> = source.expressions().iter().filter(|expr| matches!(&expr.form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &local.id)).collect();
    assert_eq!(uses.len(), 2);

    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let first = candidate.fresh_use(&uses[0].occurrence).unwrap();
    let second = candidate.fresh_use(&uses[1].occurrence).unwrap();
    let first_effects: Vec<_> = first.rows().filter(|row| row.source_row().is_local()
        && row.source_row().kind() == yu_types::ComponentKind::Effect).collect();
    let second_effects: Vec<_> = second.rows().filter(|row| row.source_row().is_local()
        && row.source_row().kind() == yu_types::ComponentKind::Effect).collect();
    assert_eq!(first_effects.len(), 2, "one annotation tail and its Function effect port");
    assert_eq!(second_effects.len(), 2, "one annotation tail and its Function effect port");
    for row in &first_effects {
        assert!(second_effects.iter().all(|other| !row.same_identity(other)), "the symbolic tail and its port are fresh per use");
    }
}

#[test]
fn empty_act_body_retains_an_ordinary_annotation_family() {
    let hir = module("act E {}\nmy id x: int -> [E] int = x").unwrap();
    assert_eq!(hir.source_effect_declarations().len(), 1);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 0);
    assert!(candidate.export(binding(&hir, "id").definition_root()).is_ok());
}

#[test]
fn exported_annotation_support_is_checked_by_an_outside_boundary() {
    let hir = module("act E\nact F\nmy id x: int -> [E] int = x; my accepts: int -> [E] int = id; my rejects: int -> [F] int = id").unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    let origin = binding(&hir, "id").definition_root();
    let rejecting = binding(&hir, "rejects").definition_root();
    let mut members = 0;
    for error in candidate.candidate_conflicts() {
        if let Ok(conflict) = candidate.effect_conflict(error.kind()) {
            let yu_solver::shadow_apply::CandidateEffectOperand::AnnotationMember {
                annotation,
                member,
                effect,
            } = conflict.operand
            else {
                panic!("permission is not an emitted event")
            };
            assert_eq!(annotation.owner, origin);
            assert_eq!(member, 0);
            assert_eq!(effect, &hir.source_effect_declarations()[0].id);
            assert_eq!(conflict.annotation.unwrap().owner, rejecting);
            members += 1;
        }
    }
    assert!(
        members > 0,
        "exported E must survive positive extrusion and fresh use to reject F-only boundary"
    );
}

#[test]
fn annotation_recursive_construction_depth_is_rejected_before_hir_publication() {
    // This checks the HIR guard on a parsed artifact, not default parser stack safety.
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            for ty in [
                format!("{}int{}", "(".repeat(127), ")".repeat(127)),
                format!("{}int", "int -> ".repeat(127)),
            ] {
                assert!(
                    module(&format!("my value: {ty} = 1")).is_ok(),
                    "depth 128 remains available"
                );
            }
            for ty in [
                format!("{}int{}", "(".repeat(128), ")".repeat(128)),
                format!("{}int", "int -> ".repeat(128)),
            ] {
                assert!(matches!(
                    module(&format!("my value: {ty} = 1")),
                    Err(yu_hir::HirAvailabilityError::StructuralProjection)
                ));
            }
        })
        .unwrap()
        .join()
        .unwrap();
}


#[test]
fn root_computation_rows_check_definition_and_local_initializers() {
    for body in [
        "my answer:[tick] int = tick::next()",
        "my answer = { my local:[tick] int = tick::next(); my alias = local; local }",
    ] {
        let hir = module(&format!("act tick:\n    our next: () -> int\n\n{body}")).unwrap();
        let candidate = CandidateInference::solve(hir).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{body}");
        assert_eq!(candidate.source_call_count(), 1);
    }
    for body in [
        "my answer:[other] int = tick::next()",
        "my answer:[] int = tick::next()",
        "my answer = { my local:[other] int = tick::next(); local }",
        "my answer = { my local:[] int = tick::next(); local }",
    ] {
        let hir = module(&format!("act other\nact tick:\n    our next: () -> int\n\n{body}")).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(!candidate.candidate_conflicts().is_empty(), "{body}");
        let row = hir.local_source(binding(&hir, "answer").definition_root()).unwrap().unwrap();
        let annotation = row.annotation().or_else(|| row.bindings().first().and_then(|local| local.annotation.as_ref())).unwrap();
        let position = &annotation.ty.effects.as_ref().unwrap().position;
        assert!(candidate.candidate_conflicts().iter().any(|error| {
            candidate.effect_conflict(error.kind()).is_ok_and(|conflict|
                conflict.annotation.is_some_and(|boundary| boundary.position == position))
        }), "conflict retains the actual root annotation position");
    }
}

#[test]
fn root_allowance_does_not_supply_effects_to_a_pure_computation() {
    for text in [
        "act E\nmy answer:[E] int = 1",
        "act E\nmy answer:[] int = { my local:[E] int = 1; my first = local; local }",
    ] {
        let candidate = CandidateInference::solve(module(text).unwrap()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_eq!(candidate.source_call_count(), 0);
    }
}


#[test]
fn root_symbolic_tail_carries_computation_effect_into_a_nested_function_port() {
    for allowed in [true, false] {
        let target = if allowed { "tick" } else { "other" };
        let hir = module(&format!(
            "act other\nact tick:\n    our next: () -> int\n\nmy value:['e] (int -> ['e] int) = {{ my ignored = tick::next(); my ident x = x; ident }}\nmy checked:int -> [{target}] int = value"
        )).unwrap();
        let source = hir.local_source(binding(&hir, "value").definition_root()).unwrap().unwrap();
        let annotation = source.annotation().unwrap();
        let SourceAnnotationValue::Function { result, .. } = &annotation.ty.value else { panic!("annotated Function"); };
        assert_eq!(annotation.ty.effects.as_ref().unwrap().variables, result.effects.as_ref().unwrap().variables);
        assert_eq!(annotation.ty.effects.as_ref().unwrap().variables.len(), 1);
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert_eq!(candidate.source_call_count(), 1);
        if allowed {
            assert!(candidate.candidate_conflicts().is_empty());
        } else {
            let checked = hir.local_source(binding(&hir, "checked").definition_root()).unwrap().unwrap();
            let SourceAnnotationValue::Function { result, .. } = &checked.annotation().unwrap().ty.value else { panic!("checking Function"); };
            let position = &result.effects.as_ref().unwrap().position;
            assert!(candidate.candidate_conflicts().iter().any(|error| {
                candidate.effect_conflict(error.kind()).is_ok_and(|conflict|
                    conflict.annotation.is_some_and(|boundary|
                        boundary.owner == binding(&hir, "checked").definition_root() && boundary.position == position))
            }), "root computation tick remains visible at the later other-only Function boundary");
        }
    }
}

#[test]
fn local_root_symbolic_tail_preserves_a_future_lower_from_an_actual_argument() {
    for allowed in [true, false] {
        let target = if allowed { "tick" } else { "other" };
        let hir = module(&format!(
            "act other\nact tick:\n    our next: () -> int\n\nmy maker f = {{ my local:['e] (int -> ['e] int) = {{ my ignored = f (); my ident x = x; ident }}; local }}\nmy late = maker tick::next\nmy checked:int -> [{target}] int = late"
        )).unwrap();
        let source = hir.local_source(binding(&hir, "maker").definition_root()).unwrap().unwrap();
        let local = source.bindings().iter().find(|local| local.spelling.as_ref() == "local").unwrap();
        let annotation = local.annotation.as_ref().unwrap();
        let SourceAnnotationValue::Function { result, .. } = &annotation.ty.value else { panic!("annotated Function"); };
        assert_eq!(annotation.ty.effects.as_ref().unwrap().variables, result.effects.as_ref().unwrap().variables);
        assert_eq!(annotation.ty.effects.as_ref().unwrap().variables.len(), 1);
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert_eq!(candidate.source_call_count(), 2);
        if allowed {
            assert!(candidate.candidate_conflicts().is_empty());
        } else {
            assert!(!candidate.candidate_conflicts().is_empty(), "future tick lower must reject other-only consumer");
            let checked = hir.local_source(binding(&hir, "checked").definition_root()).unwrap().unwrap();
            let SourceAnnotationValue::Function { result, .. } = &checked.annotation().unwrap().ty.value else { panic!("checking Function"); };
            let position = &result.effects.as_ref().unwrap().position;
            assert!(candidate.candidate_conflicts().iter().any(|error| {
                candidate.effect_conflict(error.kind()).is_ok_and(|conflict|
                    conflict.annotation.is_some_and(|boundary|
                        boundary.owner == binding(&hir, "checked").definition_root() && boundary.position == position))
            }), "future tick lower through maker's actual argument reaches the retained nested port check");
        }
    }
}


#[test]
fn concrete_root_member_stays_local_when_the_row_also_has_a_shared_tail() {
    for body in [
        "my value:[tick, 'e] (int -> ['e] int) = { my ignored = tick::next(); my ident x = x; ident }; my checked:int -> [] int = value",
        "my maker f = { my local:[tick, 'e] (int -> ['e] int) = { my ignored = f (); my ident x = x; ident }; local }; my late = maker tick::next; my checked:int -> [] int = late",
    ] {
        let hir = module(&format!("act tick:\n    our next: () -> int\n\n{body}")).unwrap();
        let candidate = CandidateInference::solve(hir).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "listed tick is consumed by the root allowance and must not enter its shared tail: {body}");
    }
}


#[test]
fn function_valued_initializer_checks_its_root_computation_row_separately() {
    for local in [false, true] {
        for allowance in ["tick", "", "other"] {
            let body = if local {
                format!("my answer = {{ my value:[{allowance}] (int -> [] int) = tick::make(); value }}")
            } else {
                format!("my answer:[{allowance}] (int -> [] int) = tick::make()")
            };
            let hir = module(&format!(
                "act other\nact tick:\n    our make: () -> (int -> int)\n\n{body}\nmy checked:int -> [] int = answer"
            )).unwrap();
            let source = hir.local_source(binding(&hir, "answer").definition_root()).unwrap().unwrap();
            let annotation = if local {
                source.bindings().iter().find(|binding| binding.spelling.as_ref() == "value").unwrap().annotation.as_ref().unwrap()
            } else {
                source.annotation().unwrap()
            };
            let root_row = annotation.ty.effects.as_ref().unwrap();
            let SourceAnnotationValue::Function { result, .. } = &annotation.ty.value else { panic!("Function-valued initializer annotation"); };
            let function_row = result.effects.as_ref().unwrap();
            assert!(function_row.concrete.is_empty() && function_row.variables.is_empty());
            assert_ne!(root_row.position, function_row.position);
            let candidate = CandidateInference::solve(hir.clone()).unwrap();
            assert_eq!(candidate.source_call_count(), 1);
            if allowance == "tick" {
                assert!(candidate.candidate_conflicts().is_empty(), "root tick evaluation must not pollute the returned Function's empty effect port: {body}");
            } else {
                let mut effect_conflicts = 0;
                for error in candidate.candidate_conflicts() {
                    if let Ok(conflict) = candidate.effect_conflict(error.kind()) {
                        let boundary = conflict.annotation.expect("explicit root annotation owns the conflict");
                        assert_eq!(boundary.owner, &annotation.owner);
                        assert_eq!(boundary.position, &root_row.position);
                        assert_ne!(boundary.position, &function_row.position);
                        effect_conflicts += 1;
                    }
                }
                assert!(effect_conflicts > 0, "the Function-valued initializer's tick evaluation violates its root row: {body}");
            }
        }
    }
}
