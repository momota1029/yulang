//! Research-only final retained graph observer; no constructor trace or source semantics theorem.
use std::{collections::HashMap, sync::Arc};
use yu_hir::shadow::{
    LocalSourceForm, ShadowArtifact, SourceAnnotationType, SourceAnnotationValue,
    SourceOperationDeclaration, SourceOperationResolution, lower_module_with_local_source,
};
use yu_hir::{
    DefinitionRootId, FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports,
};
use yu_solver::Polarity;
use yu_solver::shadow_apply::{
    CandidateGraphEffectOperand, CandidateGraphEffectViewOrigin, CandidateGraphExport,
    CandidateGraphNode, CandidateInference,
};
use yu_syntax::{
    ParsedFile, SourceNodeKey, SourceText, SyntaxEnvironment, parse_file, scan_header,
};
fn parse(text: &str) -> ParsedFile {
    let s: Arc<SourceText> = Arc::from(text);
    parse_file(
        s.clone(),
        Arc::new(scan_header(s)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}
fn lower(p: &ParsedFile, label: &str) -> Arc<HirModule> {
    Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "native-signature-observer",
                label,
            ))),
            p,
            SemanticImports::empty(),
        )
        .unwrap(),
    )
}
fn root<'a>(h: &'a HirModule, n: &str) -> &'a DefinitionRootId {
    h.items()
        .iter()
        .find_map(|i| match i {
            HirItem::Binding(b) if b.name().spelling() == n => Some(b.definition_root()),
            _ => None,
        })
        .unwrap()
}
struct Keys<'a> {
    parsed: &'a ParsedFile,
    artifact: &'a ShadowArtifact,
    ids: HashMap<SourceNodeKey, usize>,
}
impl Keys<'_> {
    fn key(&mut self, k: &SourceNodeKey) -> usize {
        assert!(self.parsed.owns_source_key(k));
        assert!(self.artifact.parsed().owns_source_key(k));
        let p = self.artifact.source_position(k).unwrap();
        let loc = self.artifact.position(&p).unwrap();
        if let Some(i) = self.ids.get(k) {
            return *i;
        }
        let i = self.ids.len();
        self.ids.insert(k.clone(), i);
        println!(
            "key k{i} range={:?} kind={:?} authenticated=selected_parse_and_artifact",
            loc.range(),
            loc.kind()
        );
        i
    }
}
fn id(g: &CandidateGraphExport<'_>, n: CandidateGraphNode<'_>) -> usize {
    g.nodes().position(|a| a.same_identity(n)).unwrap()
}
fn lower_closure<'a>(
    g: &CandidateGraphExport<'a>,
    start: CandidateGraphNode<'a>,
) -> Vec<CandidateGraphNode<'a>> {
    let mut pending = vec![start];
    let mut seen = vec![];
    while let Some(n) = pending.pop() {
        if seen.iter().any(|a: &CandidateGraphNode| a.same_identity(n)) {
            continue;
        }
        seen.push(n);
        if let Some(r) = n.row() {
            for (i, b) in g.bounds().enumerate() {
                if b.kind() == yu_types::ComponentKind::Value
                    && b.upper().row().is_some_and(|u| u.same_identity(r))
                {
                    println!(
                        "root_witness bound=b{i} lower=n{} upper=n{} matched_row_of=n{}",
                        id(g, b.lower()),
                        id(g, b.upper()),
                        id(g, n)
                    );
                    pending.push(b.lower())
                }
            }
        }
    }
    seen
}
fn op<'a>(
    h: &'a HirModule,
) -> (
    &'a Arc<SourceOperationDeclaration>,
    &'a yu_hir::HirOccurrenceId,
) {
    let s = h.local_source(root(h, "resolved")).unwrap().unwrap();
    let mut ops = s.expressions().iter().filter_map(|e| match &e.form {
        LocalSourceForm::Operation {
            resolution: SourceOperationResolution::Resolved(d),
        } => Some((d, &e.occurrence)),
        _ => None,
    });
    let out = ops.next().unwrap();
    assert!(ops.next().is_none());
    out
}
fn path<'a>(
    g: &CandidateGraphExport<'a>,
    t: &SourceAnnotationType,
    n: CandidateGraphNode<'a>,
    p: &str,
    positive: bool,
    k: &mut Keys<'_>,
    declaration: &SourceOperationDeclaration,
) {
    assert_eq!(
        n.polarity(),
        if positive {
            Polarity::Positive
        } else {
            Polarity::Negative
        }
    );
    println!(
        "path {p} value=n{} polarity={:?} source_kind={:?}",
        id(g, n),
        n.polarity(),
        std::mem::discriminant(&t.value)
    );
    if let SourceAnnotationValue::Function { argument, result } = &t.value {
        let c = n
            .children()
            .expect("source function requires exact captured Function");
        println!(
            "function {p} owner=n{} children=[A:n{},AE:n{},RE:n{},R:n{}]",
            id(g, n),
            id(g, c[0]),
            id(g, c[1]),
            id(g, c[2]),
            id(g, c[3])
        );
        for (suffix, ty, port) in [
            ("argument", argument.as_ref(), c[1]),
            ("result", result.as_ref(), c[2]),
        ] {
            let row = ty.effects.as_ref().map(|r| k.key(&r.position));
            println!(
                "effect_path {p}/{suffix} owner=n{} port=n{} source_row={row:?} symbolic_names={:?}",
                id(g, n),
                id(g, port),
                ty.effects.as_ref().map(|r| &r.variables)
            );
            let port_positive = if suffix == "argument" {
                !positive
            } else {
                positive
            };
            assert_eq!(
                port.polarity(),
                if port_positive {
                    Polarity::Positive
                } else {
                    Polarity::Negative
                }
            );
            if let Some(source_row) = &ty.effects {
                if port_positive {
                    let port_row = port
                        .row()
                        .expect("written positive effect has captured row");
                    let relevant: Vec<_> = g
                        .bounds()
                        .enumerate()
                        .filter(|(_, b)| {
                            b.is_effect()
                                && b.upper().row().is_some_and(|r| r.same_identity(port_row))
                        })
                        .collect();
                    assert_eq!(relevant.len(), 1, "unique direct support-to-port bound");
                    let (bound_id, bound) = &relevant[0];
                    let CandidateGraphEffectOperand::SupportView {
                        position,
                        permitted,
                        tail,
                        ..
                    } = bound.lower().effect_operand().expect("support operand")
                    else {
                        panic!("expected exact Support view")
                    };
                    assert_eq!(position, &source_row.position);
                    let mut expected = Vec::new();
                    if p == "root" && suffix == "result" {
                        expected.push(declaration.id.family.clone());
                    }
                    expected.extend(source_row.concrete.iter().cloned());
                    assert_eq!(
                        permitted,
                        expected.as_slice(),
                        "exact ordered full-Eq family identities, duplicates retained"
                    );
                    assert_eq!(tail.is_some(), !source_row.variables.is_empty());
                    let mut reordered = expected.clone();
                    reordered.reverse();
                    if reordered != expected {
                        assert_ne!(permitted, reordered.as_slice());
                    }
                    let mut deduplicated = expected.clone();
                    let mut seen = std::collections::HashSet::new();
                    deduplicated.retain(|e| seen.insert(e.clone()));
                    if deduplicated != expected {
                        assert_ne!(permitted, deduplicated.as_slice());
                    }
                    println!(
                        "effect_incidence {p}/{suffix} port=n{} upper=n{} same_row=true support=n{} bound=b{bound_id} exact_source_row=k{} ordered_members={} symbolic_tail_present={} name_to_row_join=not_certified",
                        id(g, port),
                        id(g, bound.upper()),
                        id(g, bound.lower()),
                        k.key(position),
                        expected.len(),
                        tail.is_some()
                    );
                } else {
                    assert!(source_row.concrete.is_empty());
                    assert_eq!(source_row.variables.len(), 1);
                    assert!(port.row().is_some_and(|r| r.is_effect()));
                    println!(
                        "effect_incidence {p}/{suffix} negative_symbolic_bare_row=n{} name_to_row_join=not_certified support_or_permission_not_asserted=true",
                        id(g, port)
                    );
                }
            }
        }
        path(
            g,
            argument,
            c[0],
            &format!("{p}/argument"),
            !positive,
            k,
            declaration,
        );
        path(
            g,
            result,
            c[3],
            &format!("{p}/result"),
            positive,
            k,
            declaration,
        );
    } else {
        assert!(n.children().is_none());
        use yu_solver::shadow_apply::CandidateGraphLeaf as L;
        match &t.value {
            SourceAnnotationValue::Unit => assert_eq!(
                n.leaf(),
                Some(if positive {
                    L::UnitPositive
                } else {
                    L::UnitNegative
                })
            ),
            SourceAnnotationValue::Int => assert_eq!(
                n.leaf(),
                Some(if positive {
                    L::IntPositive
                } else {
                    L::IntNegative
                })
            ),
            SourceAnnotationValue::Variable(_) => assert!(
                n.row()
                    .is_some_and(|r| r.kind() == yu_types::ComponentKind::Value)
            ),
            _ => panic!("outside bounded fixture source constructors"),
        }
    }
}
fn main() {
    let a: Vec<_> = std::env::args().collect();
    let label = a.get(1).expect("positive|negative");
    let file = a.get(2).expect("fixture");
    let text = std::fs::read_to_string(file).unwrap();
    let parsed = parse(&text);
    assert!(parsed.structural_recoveries().is_empty());
    let hir = lower(&parsed, file);
    let artifact = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    println!(
        "fixture label={label} path={file:?} structural_recoveries=0 hir_diagnostics={}",
        hir.diagnostics().len()
    );
    let mut keys = Keys {
        parsed: &parsed,
        artifact: &artifact,
        ids: HashMap::new(),
    };
    for family in hir.source_effect_declarations() {
        assert_eq!(family.id.module.as_ref(), hir.identity().module());
        println!(
            "family spelling={:?} exact_declaration_key=k{}",
            family.spelling,
            keys.key(&family.id.declaration)
        );
    }
    let (declaration, occurrence) = op(&hir);
    let matches: Vec<_> = hir
        .source_effect_declarations()
        .iter()
        .flat_map(|f| f.operations.iter())
        .filter(|d| Arc::ptr_eq(d, declaration))
        .collect();
    assert_eq!(matches.len(), 1);
    println!(
        "operation owner_arc=exact_unique_table_arc declaration_key=k{} signature_key=k{} occurrence={occurrence:?}",
        keys.key(&declaration.id.declaration),
        keys.key(&declaration.signature_position)
    );
    let source_key = hir.occurrence_source_key(occurrence).unwrap().unwrap();
    println!(
        "operation_use source_key=k{} source_root={:?}",
        keys.key(source_key),
        root(&hir, "resolved")
    );
    let foreign_parsed = parse(&text);
    assert!(!foreign_parsed.owns_source_key(source_key));
    let cloned = Arc::new(declaration.as_ref().clone());
    assert!(!Arc::ptr_eq(&cloned, declaration));
    assert_eq!(cloned.id, declaration.id);
    println!(
        "guard foreign_parse_same_text_key=rejected cloned_declaration_same_id_not_same_arc=rejected"
    );
    let solved = CandidateInference::solve(hir.clone());
    if label == "negative" {
        assert!(solved.is_err());
        println!(
            "negative_preflight result={:?} graph_export=unavailable no_native_mapping=true",
            solved.err().unwrap()
        );
        return;
    }
    let candidate = solved.expect("positive capture");
    assert!(candidate.observes_hir(&hir));
    assert!(candidate.candidate_conflicts().is_empty());
    println!(
        "candidate observes_exact_hir=true conflicts=0 source_call_count={} unresolved={:?}",
        candidate.source_call_count(),
        candidate.unresolved()
    );
    let foreign_hir = lower(&foreign_parsed, file);
    assert!(!candidate.observes_hir(&foreign_hir));
    assert!(candidate.export(root(&foreign_hir, "resolved")).is_err());
    println!("guard foreign_hir_same_text=rejected foreign_root_same_spelling=rejected");
    let g = candidate.export(root(&hir, "resolved")).unwrap();
    println!(
        "graph root=n{} nodes={} bounds={}",
        id(&g, g.root()),
        g.node_count(),
        g.bounds().count()
    );
    let mut support_count = 0;
    for n in g.nodes() {
        let i = id(&g, n);
        println!(
            "node n{i} polarity={:?} leaf={:?} row={:?} function_children={:?}",
            n.polarity(),
            n.leaf(),
            n.row().map(|r| (r.kind(), r.is_local())),
            n.children().map(|c| c.map(|v| id(&g, v)))
        );
        if let Some(operand) = n.effect_operand() {
            match operand {
                CandidateGraphEffectOperand::SupportView {
                    origin,
                    owner,
                    position,
                    permitted,
                    tail,
                } => {
                    let CandidateGraphEffectViewOrigin::OperationInterface {
                        declaration: actual,
                        occurrence: actual_occurrence,
                    } = origin
                    else {
                        panic!("unexpected support provenance")
                    };
                    assert!(std::ptr::eq(actual, declaration.as_ref()));
                    assert_eq!(actual_occurrence, occurrence);
                    assert_eq!(owner.definition_root(), Some(root(&hir, "resolved")));
                    println!(
                        "support n{i} exact_declaration_arc=true exact_occurrence=true exact_owner=true source_position=k{} permitted={permitted:?} tail={:?}",
                        keys.key(position),
                        tail.map(|t| id(&g, t))
                    );
                    let family_names: Vec<_> = permitted
                        .iter()
                        .map(|effect| {
                            let matches: Vec<_> = hir
                                .source_effect_declarations()
                                .iter()
                                .filter(|f| &f.id == effect)
                                .collect();
                            assert_eq!(matches.len(), 1);
                            keys.key(&effect.declaration);
                            matches[0].spelling.as_ref()
                        })
                        .collect();
                    println!("support_members n{i} exact_full_eq_family_order={family_names:?}");
                    support_count += 1
                }
                CandidateGraphEffectOperand::PermissionView { .. } => {
                    panic!("direct operation signature unexpectedly has permission view")
                }
                _ => println!("other_effect_operand n{i}"),
            }
        }
    }
    for (i, b) in g.bounds().enumerate() {
        println!(
            "bound b{i} kind={:?} lower=n{} upper=n{}",
            b.kind(),
            id(&g, b.lower()),
            id(&g, b.upper())
        );
    }
    let reachable = lower_closure(&g, g.root());
    let functions: Vec<_> = reachable
        .iter()
        .filter(|n| n.children().is_some())
        .copied()
        .collect();
    assert_eq!(
        functions.len(),
        1,
        "root bound closure must select exactly one Function; no arbitrary first"
    );
    let native = functions[0];
    path(
        &g,
        &declaration.signature,
        native,
        "root",
        true,
        &mut keys,
        declaration,
    );
    println!(
        "selection unique_function_via_root_value_bounds=n{} operation_supports={} constructor_trace=false semantics_proof=false",
        id(&g, native),
        support_count
    );
    assert_eq!(support_count, 2);
    assert!(
        candidate
            .source_occurrence_observation(op(&foreign_hir).1, 256)
            .is_err()
    );
    println!("guard foreign_occurrence_same_ordinal=rejected");
    let observation = candidate
        .source_occurrence_observation(occurrence, 256)
        .unwrap();
    println!(
        "source_facts count={} complete={} origins={} origins_complete={}",
        observation.facts().count(),
        observation.facts_complete(),
        observation.origins().count(),
        observation.origins_complete()
    );
    for f in observation.facts() {
        println!("source_fact {f:?}")
    }
    println!("PASS bounded retained graph observation");
}
