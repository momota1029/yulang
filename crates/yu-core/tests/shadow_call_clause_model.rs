#![cfg(feature = "shadow")]

//! Finite research instances of candidate §§3–6, not original O0 closure.
//! Old families and their legal substitutions are independent supplied inputs.
//! Retained syntax IDs locate inputs; they never establish semantic typing.

use std::sync::Arc;
use yu_core::shadow::{BinderId, ExprId, Form, ShadowArtifact, UseId};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

#[derive(Clone, Debug, PartialEq, Eq)]
struct Signature {
    binder_tree: u8,
    component: u8,
    xi: (u8, u8, u8),
    local_scope: u8,
    provider_scope: u8,
    provider: BinderId,
    root: u8,
    dependencies: Vec<u8>,
    descriptor: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Record {
    sig: Signature,
    call: ExprId,
    callee_use: UseId,
    argument_use: UseId,
    argument_binder: BinderId,
    checking_occurrence: u8,
    beta: (BinderId, u8),
    p0: (BinderId, u8, &'static str),
    p_out: (ExprId, &'static str),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Designation {
    CompleteInvocation,
    LatentResult,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Position {
    sig: Signature,
    old_id: u8,
    designation: Designation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Witness {
    record: Record,
    position: Position,
    old_id: u8,
    observation: u8,
}

#[derive(Clone)]
struct Old {
    // Complete finite OSig domain, including unused typed descriptors.
    signatures: Vec<Signature>,
    positions: Vec<Position>,
    // Independently supplied Gen-Call-0 inventory, never inferred from syntax.
    records: Vec<Record>,
    witnesses: Vec<Witness>,
}

#[derive(Clone)]
struct Sections {
    signature: Vec<(Signature, Position)>,
    occurrence: Vec<(Record, Witness)>,
}

// Explicit finite maps on whole indexed objects. Legality of this old action
// is a premise; no independent freshening or coordinate casts are performed.
struct Substitution {
    signatures: Vec<(Signature, Signature)>,
    positions: Vec<(Position, Position)>,
    records: Vec<(Record, Record)>,
    witnesses: Vec<(Witness, Witness)>,
}

fn lookup<'a, T: PartialEq, U>(pairs: &'a [(T, U)], key: &T) -> Option<&'a U> {
    let mut matches = pairs.iter().filter(|(input, _)| input == key);
    let output = &matches.next()?.1;
    matches.next().is_none().then_some(output)
}

fn validate(old: &Old, sections: &Sections, actions: &[Substitution]) -> bool {
    if sections.signature.len() != old.signatures.len()
        || sections.occurrence.len() != old.records.len()
    {
        return false;
    }
    for sig in &old.signatures {
        let Some(position) = lookup(&sections.signature, sig) else {
            return false;
        };
        if !old.positions.contains(position)
            || position.sig != *sig
            || position.designation != Designation::CompleteInvocation
        {
            return false;
        }
    }
    for record in &old.records {
        let Some(position) = lookup(&sections.signature, &record.sig) else {
            return false;
        };
        let Some(witness) = lookup(&sections.occurrence, record) else {
            return false;
        };
        if !old.witnesses.contains(witness)
            || witness.record != *record
            || witness.position != *position
        {
            return false;
        }
    }
    for action in actions {
        for sig in &old.signatures {
            let Some(target) = lookup(&action.signatures, sig) else {
                return false;
            };
            let Some(selected) = lookup(&sections.signature, sig) else {
                return false;
            };
            if lookup(&action.positions, selected) != lookup(&sections.signature, target) {
                return false;
            }
        }
        for record in &old.records {
            let Some(target) = lookup(&action.records, record) else {
                return false;
            };
            let Some(selected) = lookup(&sections.occurrence, record) else {
                return false;
            };
            if lookup(&action.witnesses, selected) != lookup(&sections.occurrence, target) {
                return false;
            }
        }
    }
    true
}

// Interpretation selects a fixed old witness. Erasure is literally that same
// witness; the old primitive still ranges over ALL independently supplied
// alternatives, including those outside the candidate image.
fn interpret<'a>(
    old: &Old,
    sections: &'a Sections,
    actions: &[Substitution],
    record: &Record,
) -> Option<&'a Witness> {
    validate(old, sections, actions)
        .then(|| lookup(&sections.occurrence, record))
        .flatten()
}

fn observations(old: &Old, record: &Record) -> Vec<u8> {
    old.witnesses
        .iter()
        .filter(|w| w.record == *record)
        .map(|w| w.observation)
        .collect()
}

fn fixture() -> (Old, Sections) {
    let source: Arc<SourceText> = Arc::from("my apply f = { my step x = f x; step }");
    let header = Arc::new(scan_header(source.clone()));
    let artifact = ShadowArtifact::from_parsed(parse_file(
        source,
        header,
        Arc::new(SyntaxEnvironment::empty()),
    ))
    .unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let input = skeleton.source_call_use_inputs().next().unwrap();
    let Form::Use { binder, occurrence } = skeleton.expression(input.argument()).unwrap().form()
    else {
        panic!("approved local x use");
    };
    let sig = Signature {
        binder_tree: 0,
        component: 0,
        xi: (1, 2, 3),
        local_scope: 2,
        provider_scope: 1,
        provider: input.binder().clone(),
        root: 4,
        dependencies: vec![1, 2],
        descriptor: 5,
    };
    let record = Record {
        sig: sig.clone(),
        call: input.application().expression().clone(),
        callee_use: input.occurrence().clone(),
        argument_use: occurrence.clone(),
        argument_binder: binder.clone(),
        checking_occurrence: 6,
        beta: (sig.provider.clone(), sig.root),
        p0: (sig.provider.clone(), sig.root, "call.effect"),
        p_out: (input.application().expression().clone(), "ElimOrigin"),
    };
    // Scope numbers and semantic descriptor/witness membership remain explicit
    // finite inputs: the structural facade supplies no original typing bridge.
    let position = Position {
        sig: sig.clone(),
        old_id: 7,
        designation: Designation::CompleteInvocation,
    };
    let witness = Witness {
        record: record.clone(),
        position: position.clone(),
        old_id: 8,
        observation: 9,
    };
    (
        Old {
            signatures: vec![sig.clone()],
            positions: vec![position.clone()],
            records: vec![record.clone()],
            witnesses: vec![witness.clone()],
        },
        Sections {
            signature: vec![(sig, position)],
            occurrence: vec![(record, witness)],
        },
    )
}

fn swap_action(old: &Old) -> Substitution {
    // Involution of old evidence alternatives, fixing the ENTIRE source tuple.
    Substitution {
        signatures: old
            .signatures
            .iter()
            .map(|s| (s.clone(), s.clone()))
            .collect(),
        positions: old
            .positions
            .iter()
            .map(|p| (p.clone(), p.clone()))
            .collect(),
        records: old.records.iter().map(|r| (r.clone(), r.clone())).collect(),
        witnesses: vec![
            (old.witnesses[0].clone(), old.witnesses[1].clone()),
            (old.witnesses[1].clone(), old.witnesses[0].clone()),
        ],
    }
}

#[test]
fn coherent_sections_select_existing_witnesses_in_a_finite_instance() {
    let (old, sections) = fixture();
    let identity = Substitution {
        signatures: old
            .signatures
            .iter()
            .map(|s| (s.clone(), s.clone()))
            .collect(),
        positions: old
            .positions
            .iter()
            .map(|p| (p.clone(), p.clone()))
            .collect(),
        records: old.records.iter().map(|r| (r.clone(), r.clone())).collect(),
        witnesses: old
            .witnesses
            .iter()
            .map(|w| (w.clone(), w.clone()))
            .collect(),
    };
    let actions = [identity];
    assert!(validate(&old, &sections, &actions));
    assert_eq!(
        interpret(&old, &sections, &actions, &old.records[0]),
        Some(&old.witnesses[0])
    );
}

#[test]
fn full_signature_domain_includes_unused_typed_descriptors() {
    let (mut old, mut sections) = fixture();
    let mut unused = old.signatures[0].clone();
    unused.descriptor = 99;
    old.signatures.push(unused.clone());
    assert!(!validate(&old, &sections, &[]));
    let missing = Position {
        sig: unused.clone(),
        old_id: 99,
        designation: Designation::CompleteInvocation,
    };
    sections.signature.push((unused, missing));
    assert!(!validate(&old, &sections, &[]));
}

#[test]
fn legal_old_involution_can_preclude_any_coherent_candidate_section() {
    let (mut old, sections) = fixture();
    let mut alternative = old.witnesses[0].clone();
    alternative.old_id = 10;
    old.witnesses.push(alternative);
    let action = swap_action(&old);
    for witness in &old.witnesses {
        let mapped = lookup(&action.witnesses, witness).unwrap();
        assert_eq!(mapped.record, witness.record);
        assert_eq!(mapped.position, witness.position);
        assert!(old.witnesses.contains(mapped));
        assert_eq!(lookup(&action.witnesses, mapped), Some(witness));
    }
    // Exhaust both possible sections: identity/composition of the base action
    // hold, but neither old alternative is fixed by this substitution.
    for witness in &old.witnesses {
        let mut choice = sections.clone();
        choice.occurrence[0].1 = witness.clone();
        assert!(validate(&old, &choice, &[]));
        let action = swap_action(&old);
        let actions = [action];
        assert!(!validate(&old, &choice, &actions));
        assert!(interpret(&old, &choice, &actions, &old.records[0]).is_none());
    }
}

#[test]
fn latent_result_position_cannot_type_immediate_invocation() {
    let (mut old, mut sections) = fixture();
    old.positions[0].designation = Designation::LatentResult;
    sections.signature[0].1 = old.positions[0].clone();
    old.witnesses[0].position = old.positions[0].clone();
    sections.occurrence[0].1 = old.witnesses[0].clone();
    assert!(!validate(&old, &sections, &[]));
}

#[test]
fn exact_joint_fiber_rejects_xi_scope_provider_and_separate_output_mismatch() {
    let (old, sections) = fixture();
    for mutation in 0..8 {
        let mut altered = old.clone();
        let mut wrong = altered.witnesses[0].clone();
        match mutation {
            0 => wrong.record.sig.xi.1 += 1,
            1 => wrong.record.sig.local_scope = wrong.record.sig.provider_scope,
            2 => wrong.record.sig.provider = wrong.record.argument_binder.clone(),
            3 => wrong.record.p_out.1 = "call.effect",
            4 => wrong.record.beta.1 += 1,
            5 => wrong.record.p0.2 = "latent.result",
            6 => wrong.record.checking_occurrence += 1,
            7 => wrong.record.callee_use = wrong.record.argument_use.clone(),
            _ => unreachable!(),
        }
        altered.witnesses[0] = wrong.clone();
        let mut selected = sections.clone();
        selected.occurrence[0].1 = wrong;
        assert!(!validate(&altered, &selected, &[]), "mutation {mutation}");
    }
}

#[test]
fn empty_incidence_rejects_extension_and_does_not_generate_free_evidence() {
    let (mut old, sections) = fixture();
    old.witnesses.clear();
    assert!(!validate(&old, &sections, &[]));
    assert!(interpret(&old, &sections, &[], &old.records[0]).is_none());
    assert!(observations(&old, &old.records[0]).is_empty());
    // Candidate §6 falsifier: changing the independent old fiber would change
    // this active existential primitive. Interpretation never performs this.
    let mut free_extension = old.clone();
    free_extension
        .witnesses
        .push(sections.occurrence[0].1.clone());
    assert_eq!(observations(&free_extension, &old.records[0]), vec![9]);
    assert!(old.witnesses.is_empty());
}

#[test]
fn erasure_keeps_old_alternatives_outside_candidate_image_and_observations() {
    let (mut old, sections) = fixture();
    let mut alternative = old.witnesses[0].clone();
    alternative.old_id = 10;
    alternative.observation = 11;
    old.witnesses.push(alternative.clone());
    let before = observations(&old, &old.records[0]);
    let erased = interpret(&old, &sections, &[], &old.records[0]).unwrap();
    assert_eq!(erased, &old.witnesses[0]);
    assert_ne!(erased, &alternative);
    assert!(old.witnesses.contains(&alternative));
    assert_eq!(observations(&old, &old.records[0]), before);
    assert_eq!(before, vec![9, 11]);
}

#[test]
fn retained_source_call_omitted_from_supplied_generated_inventory_stays_omitted() {
    let (mut old, mut sections) = fixture();
    let retained = old.records[0].clone();
    old.records.clear();
    sections.occurrence.clear();
    assert!(validate(&old, &sections, &[]));
    assert!(interpret(&old, &sections, &[], &retained).is_none());
    assert!(old.records.is_empty());
}

#[test]
fn section_existence_iff_old_rule_witnesses_for_sixteen_finite_instances() {
    // Bounded iff only: one typed descriptor, one supplied record, no
    // nonidentity substitutions. This is not the general section theorem.
    for mask in 0..16 {
        let (mut old, _) = fixture();
        if mask & 1 != 0 {
            old.positions.clear();
        }
        if mask & 2 != 0 {
            old.witnesses.clear();
        }
        if mask & 4 != 0 {
            for position in &mut old.positions {
                position.designation = Designation::LatentResult;
            }
        }
        if mask & 8 != 0 {
            for witness in &mut old.witnesses {
                witness.record.p_out.1 = "different origin leg";
            }
        }
        // Direct old-rule satisfiability, independent of section tables.
        let old_rule_instance = old.positions.iter().any(|position| {
            position.sig == old.signatures[0]
                && position.designation == Designation::CompleteInvocation
                && old.witnesses.iter().any(|witness| {
                    witness.record == old.records[0] && witness.position == *position
                })
        });
        // Exhaust the whole finite interpretation search space; never create
        // a missing old position or witness to satisfy the clauses.
        let section_exists = old.positions.iter().any(|position| {
            old.witnesses.iter().any(|witness| {
                let choice = Sections {
                    signature: vec![(old.signatures[0].clone(), position.clone())],
                    occurrence: vec![(old.records[0].clone(), witness.clone())],
                };
                validate(&old, &choice, &[])
            })
        });
        assert_eq!(section_exists, old_rule_instance, "finite mask {mask}");
    }
}
