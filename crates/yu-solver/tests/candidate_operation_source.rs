#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

use std::sync::Arc;
use yu_hir::shadow::{LocalSourceForm, SourceOperationResolution, lower_module_with_local_source};
use yu_hir::{DefinitionRootId, FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateEffectOperand, CandidateGraphExport, CandidateGraphLeaf, CandidateGraphNode, CandidateInference};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.structural_recoveries().is_empty(), "valid operation fixture");
    Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("operation-source", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap())
}
fn root<'a>(hir: &'a HirModule, name: &str) -> &'a DefinitionRootId {
    hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding.definition_root()),
        _ => None,
    }).unwrap()
}
fn lowers<'a>(graph: &CandidateGraphExport<'a>, start: CandidateGraphNode<'a>) -> Vec<CandidateGraphNode<'a>> {
    let mut pending = vec![start];
    let mut visited: Vec<CandidateGraphNode<'a>> = Vec::new();
    while let Some(node) = pending.pop() {
        if visited.iter().any(|prior| prior.same_identity(node)) { continue; }
        visited.push(node);
        if let Some(row) = node.row() {
            for bound in graph.bounds() {
                if bound.kind() == yu_types::ComponentKind::Value
                    && bound.upper().row().is_some_and(|upper| upper.same_identity(row)) {
                    pending.push(bound.lower());
                }
            }
        }
    }
    visited
}
#[test]
fn lookup_retains_actual_declaration_without_forming_a_call() {
    let hir = module("act tick:\n    our next: () -> int\n\nmy lookup = tick::next");
    let source = hir.local_source(root(&hir, "lookup")).unwrap().unwrap();
    let operation = source.expressions().iter().find_map(|expr| match &expr.form {
        LocalSourceForm::Operation { resolution: SourceOperationResolution::Resolved(declaration) } => Some(declaration),
        _ => None,
    }).unwrap();
    assert_eq!(operation.id.family, hir.source_effect_declarations()[0].id);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 0);
    let graph = candidate.export(root(&hir, "lookup")).unwrap();
    assert!(lowers(&graph, graph.root()).iter().filter_map(|node| node.children()).any(|ports|
        ports[0].leaf() == Some(CandidateGraphLeaf::UnitNegative)
            && ports[3].leaf() == Some(CandidateGraphLeaf::IntPositive)));
}
#[test]
fn polymorphic_operation_aliases_instantiate_independent_value_variables() {
    let hir = module("act echo:\n    our send: 'a -> 'a\n\nmy alias = echo::send; my first: () = alias(); my second: int = alias 1");
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 2);
    for (name, leaf) in [("first", CandidateGraphLeaf::UnitPositive), ("second", CandidateGraphLeaf::IntPositive)] {
        let graph = candidate.export(root(&hir, name)).unwrap();
        let result_lowers = lowers(&graph, graph.root());
        assert!(result_lowers.iter().any(|node| node.leaf() == Some(leaf)), "{name}");
        let foreign_leaf = if name == "first" { CandidateGraphLeaf::IntPositive } else { CandidateGraphLeaf::UnitPositive };
        assert!(!result_lowers.iter().any(|node| node.leaf() == Some(foreign_leaf)), "{name} must not contain the other instance's argument type");
    }
}
#[test]
fn empty_operation_calls_validate_the_real_unit_argument() {
    for (signature, valid) in [("() -> int", true), ("int -> int", false)] {
        let hir = module(&format!("act tick:\n    our next: {signature}\n\nmy answer = tick::next()"));
        let candidate = CandidateInference::solve(hir).unwrap();
        assert_eq!(candidate.source_call_count(), 1);
        assert_eq!(candidate.candidate_conflicts().is_empty(), valid);
    }
}
#[test]
fn aliased_interface_conflicts_retain_operation_members_and_reject_foreign_handles() {
    let text = "act E\nact F\nact tick:\n    our next: () -> [E] int\n\nmy lookup = tick::next; my alias = lookup; my accepted: () -> [tick, E] int = alias; my rejected: () -> [F] int = alias";
    let hir = module(text);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    let foreign = CandidateInference::solve(module(text)).unwrap();
    let source = hir.local_source(root(&hir, "lookup")).unwrap().unwrap();
    let (declaration, occurrence) = source.expressions().iter().find_map(|expr| match &expr.form {
        LocalSourceForm::Operation { resolution: SourceOperationResolution::Resolved(declaration) } => Some((declaration, &expr.occurrence)),
        _ => None,
    }).unwrap();
    let mut family_seen = false;
    let mut explicit_seen = false;
    for error in candidate.candidate_conflicts() {
        let Ok(conflict) = candidate.effect_conflict(error.kind()) else { continue; };
        let CandidateEffectOperand::OperationInterfaceMember { declaration: actual, owner, occurrence: origin, member, effect, .. } = conflict.operand else {
            panic!("operation support must retain its actual interface owner")
        };
        assert_eq!(actual.id, declaration.id);
        assert_eq!(owner, root(&hir, "lookup"));
        assert_eq!(origin, occurrence);
        assert_eq!(conflict.annotation.unwrap().owner, root(&hir, "rejected"));
        if effect == &declaration.id.family { assert_eq!(member, 0); family_seen = true; }
        if effect == &hir.source_effect_declarations()[0].id { assert_eq!(member, 1); explicit_seen = true; }
        assert!(foreign.effect_conflict(error.kind()).is_err());
    }
    assert!(family_seen && explicit_seen, "outer family and original signature member both survive alias transport");
}

#[test]
fn owning_family_is_prepended_without_removing_original_interface_members() {
    let hir = module("act E\nact F\nact tick:\n    our next: () -> [tick, tick, E] int\n\nmy lookup = tick::next; my rejected: () -> [F] int = lookup");
    let source = hir.local_source(root(&hir, "lookup")).unwrap().unwrap();
    let (declaration, occurrence) = source.expressions().iter().find_map(|expr| match &expr.form {
        LocalSourceForm::Operation { resolution: SourceOperationResolution::Resolved(declaration) } => Some((declaration, &expr.occurrence)),
        _ => None,
    }).unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    let mut seen = [false; 4];
    for error in candidate.candidate_conflicts() {
        let Ok(conflict) = candidate.effect_conflict(error.kind()) else { continue; };
        let CandidateEffectOperand::OperationInterfaceMember { declaration: actual, owner, occurrence: origin, member, effect, .. } = conflict.operand else {
            panic!("operation support must retain its actual interface owner")
        };
        assert_eq!(actual.id, declaration.id);
        assert_eq!(owner, root(&hir, "lookup"));
        assert_eq!(origin, occurrence);
        assert_eq!(conflict.annotation.unwrap().owner, root(&hir, "rejected"));
        assert!(member < seen.len() as u32);
        let expected = if member < 3 { &declaration.id.family } else { &hir.source_effect_declarations()[0].id };
        assert_eq!(effect, expected);
        seen[member as usize] = true;
    }
    assert!(seen.into_iter().all(|member| member), "prepended family, both original family members and original E ordinal must survive");
}
