#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]
use std::sync::Arc;
use yu_hir::{DefinitionRootId, FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution, lower_module_with_local_source};
use yu_solver::shadow_apply::{CandidateError, CandidateInference};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.structural_recoveries().is_empty());
    Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("local-self-recursion", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap())
}
fn root<'a>(hir: &'a HirModule, name: &str) -> &'a DefinitionRootId {
    hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding.definition_root()),
        _ => None,
    }).unwrap()
}

#[test]
fn recursive_occurrences_have_no_fresh_scheme_and_later_uses_are_independent() {
    let hir = module("my outer = { my loop x = loop x; my integer:int = loop 1; my identity x = x; my function:int -> int = loop identity; function }");
    let source = hir.local_source(root(&hir, "outer")).unwrap().unwrap();
    let local = source.bindings().iter().find(|binding| binding.spelling.as_ref() == "loop").unwrap();
    let uses: Vec<_> = source.expressions().iter().filter(|expression| matches!(&expression.form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &local.id)).collect();
    assert_eq!(uses.len(), 3);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let mut fresh = Vec::new();
    let mut open = 0;
    for expression in uses {
        if let Some(image) = candidate.fresh_use(&expression.occurrence) { fresh.push(image); }
        else { open += 1; }
    }
    assert_eq!(open, 1, "the recursive occurrence constrains the open initializer without capture/freshening");
    assert_eq!(fresh.len(), 2);
    let first: Vec<_> = fresh[0].rows().filter(|row| row.source_row().is_local()).collect();
    let second: Vec<_> = fresh[1].rows().filter(|row| row.source_row().is_local()).collect();
    assert!(!first.is_empty() && !second.is_empty());
    assert!(first.iter().all(|row| row.kind() == row.source_row().kind()));
    assert!(second.iter().all(|row| row.kind() == row.source_row().kind()));
    assert!(candidate.export(root(&hir, "outer")).is_ok());
}

#[test]
fn recursive_apply_occurrence_stays_open_while_sibling_helper_uses_execute() {
    let hir = module("my identity y = y\nmy outer = { my loop x = loop x; my first = loop identity; my second = loop identity; second }");
    let source = hir.local_source(root(&hir, "outer")).unwrap().unwrap();
    let local = source.bindings().iter().find(|binding| binding.spelling.as_ref() == "loop").unwrap();
    let recursive_apply = source.expressions().iter().find(|expression| matches!(&expression.form,
        LocalSourceForm::Apply { callee, .. }
            if source.expressions().get(callee.ordinal() as usize).is_some_and(|callee|
                matches!(&callee.form, LocalSourceForm::Name {
                    resolution: LocalSourceResolution::Local(id), ..
                } if id == &local.id))
    )).unwrap();
    let LocalSourceForm::Apply { callee, .. } = &recursive_apply.form else { unreachable!() };
    let recursive_name = &source.expressions()[callee.ordinal() as usize];
    let uses: Vec<_> = source.expressions().iter().filter(|expression| matches!(&expression.form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &local.id)).collect();
    assert_eq!(uses.len(), 3);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert!(candidate.fresh_use(&recursive_name.occurrence).is_none(),
        "the recursive Apply constrains the active helper root");
    let siblings: Vec<_> = uses.iter().filter(|use_expression|
        use_expression.occurrence != recursive_name.occurrence)
        .filter_map(|use_expression| candidate.fresh_use(&use_expression.occurrence)).collect();
    assert_eq!(siblings.len(), 2, "both later source occurrences execute through retained fresh-use routes");
    assert!(siblings.iter().all(|route| route.rows().all(|row| row.kind() == row.source_row().kind())));
}

#[test]
fn two_recursive_calls_constrain_one_monomorphic_initializer() {
    let hir = module("my outer = { my loop (x:int) = { my first = loop 1; my identity y = y; loop identity }; loop }");
    let source = hir.local_source(root(&hir, "outer")).unwrap().unwrap();
    let local = source.bindings().iter().find(|binding| binding.spelling.as_ref() == "loop").unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(!candidate.candidate_conflicts().is_empty(), "int and Function recursive arguments constrain the same monomorphic root");
    let recursive: Vec<_> = source.expressions().iter().filter(|expression| matches!(&expression.form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &local.id))
        .filter(|expression| candidate.fresh_use(&expression.occurrence).is_none()).collect();
    assert_eq!(recursive.len(), 2);
}

#[test]
fn nested_helper_uses_active_outer_root_without_freshening_it() {
    let hir = module("my outer = { my loop x = { my helper y = loop y; helper x }; loop }");
    let source = hir.local_source(root(&hir, "outer")).unwrap().unwrap();
    let local = source.bindings().iter().find(|binding| binding.spelling.as_ref() == "loop").unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let uses: Vec<_> = source.expressions().iter().filter(|expression| matches!(&expression.form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &local.id)).collect();
    assert_eq!(uses.len(), 2);
    assert_eq!(uses.iter().filter(|expression| candidate.fresh_use(&expression.occurrence).is_none()).count(), 1);
}

#[test]
fn sequential_visibility_and_plain_value_self_initialization_controls() {
    for text in [
        "my outer = { my earlier x = future x; my future x = x; future }",
        "my outer = { my value = value; value }",
    ] {
        let hir = module(text);
        for _ in 0..2 {
            assert!(matches!(CandidateInference::solve(hir.clone()), Err(CandidateError::Unsupported)));
        }
    }
    for text in [
        "my outer = { my loop loop = loop; loop 1 }",
        "my loop x = x; my outer = { my loop x = loop x; loop 1 }",
        "my outer = { my identity x = x; my integer:int = identity 1; my id x = x; my function:int -> int = identity id; function }",
    ] {
        let candidate = CandidateInference::solve(module(text)).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
    }
}

#[test]
fn recursive_initializer_preserves_annotation_and_effect_boundaries() {
    for allowance in ["E", ""] {
        let hir = module(&format!("act E:\n    our next: () -> int\n\nmy outer = {{ my loop x:int -> [{allowance}] int = {{ my ignored = E::next(); loop x }}; loop }}"));
        let candidate = CandidateInference::solve(hir).unwrap();
        assert_eq!(candidate.source_call_count(), 2);
        assert_eq!(candidate.candidate_conflicts().is_empty(), allowance == "E");
    }
    let candidate = CandidateInference::solve(module("my outer = { my loop x:int -> int = loop x; loop 1 }")).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
}
