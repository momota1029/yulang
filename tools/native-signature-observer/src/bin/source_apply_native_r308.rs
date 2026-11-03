//! Finite source Apply to CandidateInference evidence for R308.
//!
//! This is an observer of one retained HIR execution and its candidate graph.
//! It does not establish whole-source coverage, original Call admission, or a
//! semantic theorem.

use std::{collections::HashMap, fs, ops::Range, sync::Arc};

use yu_hir::shadow::{LocalSource, LocalSourceExpr, LocalSourceForm, ShadowArtifact, lower_module_with_local_source};
use yu_hir::{DefinitionRootId, FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateInference, CandidateSourceCall};
use yu_syntax::{ParsedFile, SourceNodeKey, SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

const FACT_LIMIT: usize = 256;

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceKeyEvidence {
    id: usize,
    position_ordinal: usize,
    range: Range<usize>,
    kind: SyntaxKind,
}

struct SourceKeys<'a> {
    parsed: &'a ParsedFile,
    artifact: &'a ShadowArtifact,
    ids: HashMap<SourceNodeKey, usize>,
    records: Vec<SourceKeyEvidence>,
}

impl<'a> SourceKeys<'a> {
    fn new(parsed: &'a ParsedFile, artifact: &'a ShadowArtifact) -> Self {
        Self { parsed, artifact, ids: HashMap::new(), records: Vec::new() }
    }

    fn intern(
        &mut self,
        hir: &HirModule,
        expr: &LocalSourceExpr,
        selected_key: &SourceNodeKey,
    ) -> Result<usize, String> {
        if !hir.owns_occurrence(&expr.occurrence) {
            return Err("LocalSource occurrence is not owned by selected HIR".into());
        }
        let hir_key = hir.occurrence_source_key(&expr.occurrence)
            .map_err(|error| format!("HIR occurrence source lookup failed: {error:?}"))?
            .ok_or("LocalSource occurrence has no HIR source key")?;
        if hir_key != &expr.source || selected_key != &expr.source {
            return Err("swapped or foreign occurrence/source key".into());
        }
        if !self.parsed.owns_source_key(selected_key) || !self.artifact.parsed().owns_source_key(selected_key) {
            return Err("foreign parse key rejected".into());
        }
        let position = self.artifact.source_position(selected_key)
            .map_err(|error| format!("source key lacks a unique artifact position: {error:?}"))?;
        let value = self.artifact.position(&position)
            .map_err(|error| format!("source position belongs to another artifact: {error:?}"))?;
        if value.range() != &expr.range {
            return Err("LocalSource range differs from selected artifact source-position range".into());
        }
        if !local_form_matches_position(&expr.form, value.kind()) {
            return Err(format!("LocalSource form {:?} disagrees with source-position kind {:?}", expr.form, value.kind()));
        }
        let position_ordinal = self.artifact.positions().iter()
            .position(|candidate| std::ptr::eq(candidate, value))
            .ok_or("source position is not retained by selected artifact")?;
        if let Some(id) = self.ids.get(selected_key) {
            let prior = &self.records[*id];
            if prior.position_ordinal != position_ordinal || prior.range != *value.range() || prior.kind != value.kind() {
                return Err("repeated source key maps to inconsistent artifact evidence".into());
            }
            return Ok(*id);
        }
        let id = self.records.len();
        self.ids.insert(selected_key.clone(), id);
        self.records.push(SourceKeyEvidence { id, position_ordinal, range: value.range().clone(), kind: value.kind() });
        Ok(id)
    }

    fn record(&self, id: usize) -> &SourceKeyEvidence { &self.records[id] }
}

fn local_form_matches_position(form: &LocalSourceForm, kind: SyntaxKind) -> bool {
    match form {
        LocalSourceForm::Apply { source_form, .. } => *source_form == kind,
        LocalSourceForm::Group { .. } => kind == SyntaxKind::ParenthesizedExpression,
        LocalSourceForm::Lambda { .. } => kind == SyntaxKind::LambdaExpression,
        LocalSourceForm::Name { .. } => kind == SyntaxKind::IdentifierExpression,
        LocalSourceForm::Integer(_) => kind == SyntaxKind::IntegerLiteral,
        // An empty-call Unit intentionally shares its key, position, and range
        // with the Apply CallTail while retaining its own LocalSource index.
        LocalSourceForm::Unit => matches!(kind, SyntaxKind::CallTail | SyntaxKind::ParenthesizedExpression | SyntaxKind::MlArgument),
        // Do not authenticate forms whose CST kind relation this observer has
        // not frozen. The caller can add an explicit owner rule under review.
        _ => false,
    }
}

fn slot0_authenticates(fact: (yu_solver::Term, yu_solver::Term), native: (yu_solver::Term, yu_solver::Term)) -> bool {
    fact == native
}

fn parse(text: &str) -> ParsedFile {
    let text: Arc<SourceText> = Arc::from(text);
    parse_file(
        text.clone(),
        Arc::new(scan_header(text)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn lower(parsed: &ParsedFile, file: &str) -> Arc<HirModule> {
    Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r308", file))),
            parsed,
            SemanticImports::empty(),
        )
        .expect("fixture lowers to HIR"),
    )
}

fn binding<'a>(hir: &'a HirModule, name: &str) -> &'a yu_hir::HirBinding {
    hir.items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding),
            _ => None,
        })
        .expect("fixture binding")
}

fn source_group_path<'a>(source: &'a LocalSource, start: &'a LocalSourceExpr) -> Vec<&'a LocalSourceExpr> {
    let mut path = Vec::new();
    let mut current = start;
    while let LocalSourceForm::Group { inner } = &current.form {
        let next = source.expression(inner).expect("Group child belongs to same source owner");
        path.push(current);
        current = next;
    }
    path
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct GroupEdge {
    parent: yu_hir::shadow::LocalSourceIndex,
    inner: yu_hir::shadow::LocalSourceIndex,
}

fn source_group_edges(source: &LocalSource, start: &yu_hir::shadow::LocalSourceIndex) -> Vec<GroupEdge> {
    let mut edges = Vec::new();
    let mut current = start.clone();
    while let Some(expr) = source.expression(&current) {
        let LocalSourceForm::Group { inner } = &expr.form else { break };
        edges.push(GroupEdge { parent: current, inner: inner.clone() });
        current = inner.clone();
    }
    edges
}

fn authentic_group_projection(
    source: &LocalSource,
    start: &yu_hir::shadow::LocalSourceIndex,
    projection: &[GroupEdge],
) -> bool {
    let actual = source_group_edges(source, start);
    actual == projection && projection.iter().all(|edge| {
        source.expression(&edge.parent).is_some_and(|expr|
            matches!(&expr.form, LocalSourceForm::Group { inner } if inner == &edge.inner))
            && source.expression(&edge.inner).is_some()
    })
}

fn ungroup<'a>(source: &'a LocalSource, mut expr: &'a LocalSourceExpr) -> &'a LocalSourceExpr {
    while let LocalSourceForm::Group { inner } = &expr.form {
        expr = source.expression(inner).expect("Group child belongs to same LocalSource");
    }
    expr
}

fn candidate_for_apply<'a>(candidate: &'a CandidateInference, occurrence: &yu_hir::HirOccurrenceId) -> CandidateSourceCall<'a> {
    let found: Vec<_> = (0..candidate.source_call_count())
        .filter_map(|index| candidate.source_call(index).ok())
        .filter(|call| call.checking_occurrence().occurrence() == occurrence)
        .collect();
    assert_eq!(found.len(), 1, "one generated CandidateInference call per retained Apply occurrence");
    found.into_iter().next().unwrap()
}

/// Checks the finite same-execution joins. The returned lines are deliberately
/// proof-readable observations, not assertions of generalized source laws.
fn observe(text: &str, owner_name: &str, expected_applies: usize) -> Vec<String> {
    let parsed = parse(text);
    assert!(parsed.structural_recoveries().is_empty(), "fixtures have no parser recovery");
    let hir = lower(&parsed, owner_name);
    let owner = binding(&hir, owner_name);
    let root: &DefinitionRootId = owner.definition_root();
    let source = hir.local_source(root).expect("same HIR owner").expect("retained LocalSource");
    assert_eq!(source.definition_root(), Some(root));
    let artifact = ShadowArtifact::from_parsed(parsed.clone()).expect("artifact from selected parse");
    let mut source_keys = SourceKeys::new(&parsed, &artifact);
    let candidate = CandidateInference::solve(hir.clone()).expect("CandidateInference constructed");
    assert!(candidate.observes_hir(&hir), "candidate is tied to exact Arc<HirModule>");

    let mut out = vec![format!(
        "execution owner={owner_name:?} source_root={:?} exact_hir=true candidate_conflicts={} source_calls={} unresolved={:?}",
        source.source_root(),
        candidate.candidate_conflicts().len(),
        candidate.source_call_count(),
        candidate.unresolved(),
    )];
    let applies: Vec<_> = source.expressions().iter().filter(|expr| matches!(expr.form, LocalSourceForm::Apply { .. })).collect();
    assert_eq!(applies.len(), expected_applies, "fixture's retained LocalSource Apply census");
    let mut slot0_pairs = Vec::new();
    let mut native_pairs = Vec::new();
    for apply in applies {
        let apply_key = source_keys.intern(&hir, apply, &apply.source).expect("Apply occurrence/key/position/range/form authentication");
        let LocalSourceForm::Apply { callee, argument, source_form: local_form } = &apply.form else { unreachable!() };
        let source_callee = source.expression(callee).expect("callee index has same LocalSource owner");
        let source_argument = source.expression(argument).expect("argument index has same LocalSource owner");
        let callee_key = source_keys.intern(&hir, source_callee, &source_callee.source).expect("callee occurrence/key/position/range/form authentication");
        let argument_key = source_keys.intern(&hir, source_argument, &source_argument.source).expect("argument occurrence/key/position/range/form authentication");
        if apply.source == source_argument.source {
            assert_ne!(apply.occurrence, source_argument.occurrence, "one source key can retain distinct Apply and empty-argument occurrences");
        }

        let candidate_call = candidate_for_apply(&candidate, &apply.occurrence);
        assert_eq!(candidate_call.owner().definition_root(), Some(root), "candidate call owner is exact binding root");
        assert_eq!(candidate_call.source().occurrence, apply.occurrence, "candidate source occurrence is exact Apply");
        assert_eq!(candidate_call.callee_source().occurrence, source_callee.occurrence, "candidate callee child remains raw");
        assert_eq!(candidate_call.argument_source().occurrence, source_argument.occurrence, "candidate argument child remains raw");
        assert_eq!(candidate_call.checking_occurrence().occurrence(), &apply.occurrence, "checking provenance belongs to this Apply");
        assert_eq!(candidate_call.checking_cause().occurrence(), candidate_call.checking_occurrence(), "cause and checking occurrence agree");

        // CandidateInference retains the generated source fact for this exact
        // checking cause. Slot zero is the native callee-to-demand relation.
        let evidence = candidate.source_occurrence_observation(&apply.occurrence, FACT_LIMIT);
        let (slot0_fact, fact_rows, facts_complete, origins_complete, evidence_available) = match evidence {
            Ok(observation) => {
                let matching: Vec<_> = observation.facts().filter(|fact| fact.cause == candidate_call.checking_cause().occurrence()).collect();
                let slot0: Vec<_> = matching.iter().copied().filter(|fact| fact.cause.local_slot() == 0).collect();
                assert_eq!(slot0.len(), 1, "exact slot-0 fact for Apply checking cause");
                assert!(slot0_authenticates(
                    (slot0[0].fact.lower(), slot0[0].fact.upper()),
                    (candidate_call.native_callee(), candidate_call.native_demand()),
                ), "slot-0 fact authenticates the exact native callee/demand bundle");
                slot0_pairs.push((slot0[0].fact.lower(), slot0[0].fact.upper()));
                native_pairs.push((candidate_call.native_callee(), candidate_call.native_demand()));
                let fact_rows: Vec<_> = observation.facts().map(|fact| format!(
                    "(slot={},fact={},lower={:?},upper={:?})",
                    fact.cause.local_slot(), fact.fact.id().index(), fact.fact.lower(), fact.fact.upper(),
                )).collect();
                (slot0[0].fact.id().index().to_string(), fact_rows, observation.facts_complete(), observation.origins_complete(), true)
            }
            Err(_) => {
                assert!(!candidate.candidate_conflicts().is_empty(), "missing source facts are not silently accepted on a conflict-free candidate");
                ("unavailable".to_owned(), vec![], false, false, false)
            }
        };

        let groups = source_group_path(source, source_callee);
        let group_occurrences: Vec<_> = groups.iter().map(|expr| expr.occurrence.ordinal()).collect();
        let group_keys: Vec<_> = groups.iter().map(|expr| source_keys.intern(&hir, expr, &expr.source).expect("Group occurrence/key/position/range/form authentication")).collect();
        let group_edges = source_group_edges(source, callee);
        assert!(authentic_group_projection(source, callee, &group_edges));
        let group_index_edges: Vec<_> = group_edges.iter().map(|edge| (edge.parent.ordinal(), edge.inner.ordinal())).collect();
        let key_position_rows: Vec<_> = [apply_key, callee_key, argument_key].into_iter().chain(group_keys.iter().copied()).map(|id| {
            let record = source_keys.record(id);
            format!("k{}:p{}:{:?}:{:?}", record.id, record.position_ordinal, record.range, record.kind)
        }).collect();
        for group in &groups {
            let LocalSourceForm::Group { inner: source_inner } = &group.form else { unreachable!() };
            source_keys.intern(&hir, group, &group.source).expect("Group occurrence/key/position/range/form authentication");
            let inner = source.expression(source_inner).unwrap();
            source_keys.intern(&hir, inner, &inner.source).expect("Group inner occurrence/key/position/range/form authentication");
        }
        out.push(format!(
            "apply occurrence={} source_form={local_form:?} source_keys=(apply:k{apply_key},callee:k{callee_key},argument:k{argument_key}) source_key_positions={key_position_rows:?} local_indices=(callee:{},argument:{}) raw_callee={} raw_argument={} callee_group_path=(occurrences:{group_occurrences:?},keys:{group_keys:?},inner_index_edges:{group_index_edges:?}) checking_occurrence={:?} cause={:?} slot0_fact_id={slot0_fact} native_callee={:?} native_demand={:?} native_argument={:?} callee_effect={:?} argument_effect={:?} result={:?} invocation_effect={:?} application_effect={:?} source_facts={fact_rows:?} source_fact_evidence_available={evidence_available} facts_complete={facts_complete} origins_complete={origins_complete} resolved_hir_tree_join=not_exposed result_propagation=not_exposed_by_public_join",
            apply.occurrence.ordinal(), callee.ordinal(), argument.ordinal(), source_callee.occurrence.ordinal(), source_argument.occurrence.ordinal(),
            candidate_call.checking_occurrence(), candidate_call.checking_cause(),
            candidate_call.native_callee(), candidate_call.native_demand(), candidate_call.native_argument(),
            candidate_call.native_callee_evaluation_effect(), candidate_call.native_argument_evaluation_effect(),
            candidate_call.native_result(), candidate_call.native_invocation_effect(), candidate_call.native_application_effect(),
        ));
        let nested = ungroup(source, source_argument);
        if matches!(nested.form, LocalSourceForm::Apply { .. }) {
            let nested_call = candidate_for_apply(&candidate, &nested.occurrence);
            let term_identity = nested_call.native_result() == candidate_call.native_argument();
            out.push(format!(
                "nested_result_flow outer_occurrence={} inner_occurrence={} exact_native_term_identity={term_identity} inner_result={:?} outer_argument={:?} result_propagation=not_established missing_evidence=consumer_relation_from_native_result_through_enclosing_argument_into_candidate_graph_or_execution causal_explanation=not_inferred",
                apply.occurrence.ordinal(), nested.occurrence.ordinal(), nested_call.native_result(), candidate_call.native_argument(),
            ));
        }
        if evidence_available && (!facts_complete || !origins_complete) {
            out.push(format!("truncation occurrence={} facts_complete={facts_complete} origins_complete={origins_complete} cap={FACT_LIMIT}", apply.occurrence.ordinal()));
        }
    }
    if slot0_pairs.len() > 1 && slot0_pairs.windows(2).any(|pair| pair[0] != pair[1]) {
        for index in 0..slot0_pairs.len() - 1 {
            if slot0_pairs[index] == slot0_pairs[index + 1] { continue; }
            assert!(!slot0_authenticates(slot0_pairs[index], native_pairs[index + 1]), "cross-call native callee/demand bundle swap is rejected by exact slot-0 fact identity");
            assert!(!slot0_authenticates(slot0_pairs[index + 1], native_pairs[index]), "reverse cross-call bundle swap is rejected by exact slot-0 fact identity");
        }
        out.push("cross_call_bundle_swap= rejected_by_cause_selected_fact_identity".to_owned());
    } else {
        out.push("cross_call_bundle_swap=not_discriminating_fixture".to_owned());
    }
    out.push("claim_class=finite_source_native_evidence semantic_proof=false original_call_admission=false finite_function_ports_not_EI_All=true".to_owned());
    out
}

fn main() {
    let mut args = std::env::args().skip(1);
    let (text, owner) = match args.next().as_deref() {
        Some("nested") => ("my id x = x; my answer = id (id 1)", "answer"),
        Some("group") => ("my id x = x; my answer = ((id)) (id 1)", "answer"),
        Some("empty") => ("my invoke f = f()", "invoke"),
        Some("conflict") => ("my id x = x; my wrong (x:()) = x; my answer = wrong 1", "answer"),
        Some("file") => {
            let path = args.next().expect("file mode requires a path");
            let source = fs::read_to_string(&path).expect("read fixture");
            let owner = args.next().expect("file mode requires owner binding");
            let parsed = parse(&source);
            let hir = lower(&parsed, &path);
            let applies = hir.local_source(binding(&hir, &owner).definition_root()).unwrap().unwrap().expressions().iter().filter(|expr| matches!(expr.form, LocalSourceForm::Apply { .. })).count();
            for line in observe(&source, &owner, applies) { println!("{line}"); }
            return;
        }
        _ => ("my id x = x; my answer = id (id 1)", "answer"),
    };
    let parsed = parse(text);
    let hir = lower(&parsed, owner);
    let count = hir.local_source(binding(&hir, owner).definition_root()).unwrap().unwrap().expressions().iter().filter(|expr| matches!(expr.form, LocalSourceForm::Apply { .. })).count();
    for line in observe(text, owner, count) { println!("{line}"); }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_and_grouped_apply_retain_source_children_and_native_slot0() {
        let nested = observe("my id x = x; my answer = id (id 1)", "answer", 2);
        assert!(nested.iter().any(|line| line.contains("slot0_fact_id=")));
        assert!(nested.iter().any(|line| line.contains("cross_call_bundle_swap= rejected")), "fixture distinguishes native bundles across calls");
        let group = observe("my id x = x; my answer = ((id)) (id 1)", "answer", 2);
        assert!(group.iter().any(|line| line.contains("callee_group_path=(occurrences:[") && !line.contains("callee_group_path=(occurrences:[],")));
        assert!(group.iter().any(|line| line.contains("inner_index_edges:[(")));
    }

    #[test]
    fn two_group_callee_edges_are_ordered_and_missing_or_duplicated_edges_fail() {
        let parsed = parse("my id x = x; my answer = ((id)) (id 1)");
        let hir = lower(&parsed, "two-groups");
        let source = hir.local_source(binding(&hir, "answer").definition_root()).unwrap().unwrap();
        let apply = source.expressions().iter()
            .find(|expr| matches!(expr.form, LocalSourceForm::Apply { .. }))
            .unwrap();
        let LocalSourceForm::Apply { callee, .. } = &apply.form else { unreachable!() };
        let edges = source_group_edges(source, callee);
        assert_eq!(edges.len(), 2, "both raw Group nodes must be retained");
        assert!(authentic_group_projection(source, callee, &edges));
        for edge in &edges {
            let parent = source.expression(&edge.parent).unwrap();
            assert!(matches!(&parent.form, LocalSourceForm::Group { inner } if inner == &edge.inner));
            assert!(source.expression(&edge.inner).is_some());
        }
        let mut missing = edges.clone();
        missing.pop();
        assert!(!authentic_group_projection(source, callee, &missing), "omitted inner Group edge is rejected");
        let mut duplicated = edges.clone();
        duplicated.insert(1, edges[0].clone());
        assert!(!authentic_group_projection(source, callee, &duplicated), "duplicated Group edge is rejected");
    }

    #[test]
    fn source_key_join_rejects_swapped_keys_and_wrong_syntax_forms() {
        let parsed = parse("my id x = x; my answer = ((id)) (id 1)");
        let hir = lower(&parsed, "key-auth");
        let artifact = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
        let source = hir.local_source(binding(&hir, "answer").definition_root()).unwrap().unwrap();
        let apply = source.expressions().iter().find(|expr| matches!(expr.form, LocalSourceForm::Apply { .. })).unwrap();
        let LocalSourceForm::Apply { callee, .. } = &apply.form else { unreachable!() };
        let group = source.expression(callee).unwrap();
        assert!(matches!(group.form, LocalSourceForm::Group { .. }));
        let inner_group = source_group_path(source, group)[1];
        let actual_position = artifact.source_position(&group.source).unwrap();
        let actual_kind = artifact.position(&actual_position).unwrap().kind();
        assert_eq!(actual_kind, SyntaxKind::ParenthesizedExpression);
        assert!(local_form_matches_position(&group.form, actual_kind));
        assert!(!local_form_matches_position(&group.form, SyntaxKind::IdentifierExpression), "a Group cannot authenticate an Identifier source node");

        let mut keys = SourceKeys::new(&parsed, &artifact);
        assert!(keys.intern(&hir, group, &apply.source).is_err(), "swapped Apply key cannot authenticate a Group occurrence");
        assert!(keys.intern(&hir, group, &group.source).is_ok());
        assert!(keys.intern(&hir, inner_group, &inner_group.source).is_ok());
    }

    #[test]
    fn empty_call_and_foreign_hir_are_distinguished_by_artifact_identity() {
        let empty = observe("my invoke f = f()", "invoke", 1);
        assert!(empty.iter().any(|line| line.contains("claim_class=finite_source_native_evidence")));
        let empty_row = empty.iter().find(|line| line.starts_with("apply occurrence=")).unwrap();
        let apply_key = empty_row.split("source_keys=(apply:k").nth(1).unwrap().split(',').next().unwrap();
        let argument_key = empty_row.split("argument:k").nth(1).unwrap().split(')').next().unwrap();
        assert_eq!(apply_key, argument_key, "empty-call Apply and Unit share source key identity");
        let text = "my f x = x; my answer = f 1";
        let first = lower(&parse(text), "foreign");
        let second = lower(&parse(text), "foreign");
        let candidate = CandidateInference::solve(first.clone()).unwrap();
        assert!(candidate.observes_hir(&first));
        assert!(!candidate.observes_hir(&second));
        let foreign_root = binding(&second, "answer").definition_root();
        assert!(candidate.export(foreign_root).is_err());
    }

    #[test]
    fn candidate_conflicts_are_reported_without_relabelling_solve_as_success() {
        let text = "my id x = x; my wrong (x:()) = x; my answer = wrong 1";
        let hir = lower(&parse(text), "conflict");
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(!candidate.candidate_conflicts().is_empty());
        assert!(candidate.observes_hir(&hir));
        let evidence = observe(text, "answer", 1);
        assert!(evidence.iter().any(|line| line.contains("candidate_conflicts=1")));
    }
}
