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
