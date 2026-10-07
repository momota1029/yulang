#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::ShadowArtifact;
use yu_core::shadow_call_formation::{Address, UnresolvedPremise, generate_captured_singleton};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn artifact(text: &str) -> ShadowArtifact {
    let source: Arc<SourceText> = Arc::from(text);
    let header = Arc::new(scan_header(source.clone()));
    ShadowArtifact::from_parsed(parse_file(
        source,
        header,
        Arc::new(SyntaxEnvironment::empty()),
    ))
    .unwrap()
}

#[test]
fn captured_singleton_retains_distinct_static_incidence_and_pending_bridges() {
    let source = artifact("my apply f = { my step x = f x; step }");
    let [record] = generate_captured_singleton(&source).unwrap();
    let skeleton = source.skeleton().unwrap();
    let input = skeleton.captured_call_input().unwrap();
    assert_eq!(
        record.demand().registration.declaration,
        input.outer_parameter()
    );
    assert_eq!(record.demand().registration.outer_scope, skeleton.body());
    assert_eq!(record.demand().local_scope, input.local_lambda());
    assert_eq!(record.callee_use(), Address::CalleeUse(input.callee_use()));
    assert_eq!(record.returned_use(), input.returned_use());
    let addresses = [
        record.callee_use(),
        record.upper_checking(),
        record.source_position(),
        record.invocation_output(),
    ];
    for (index, address) in addresses.iter().enumerate() {
        assert!(!addresses[index + 1..].contains(address));
    }
    let effect = record.call_effect();
    assert!(std::ptr::eq(effect.record(), &record));
    assert!(std::ptr::eq(effect.root().demand(), record.demand()));
    assert_eq!(record.unresolved_premises().len(), 7);
    assert!(
        record
            .unresolved_premises()
            .contains(&UnresolvedPremise::EmittedGenCall0Membership)
    );
    assert!(
        record
            .unresolved_premises()
            .contains(&UnresolvedPremise::CompleteInvocationInterpretation)
    );
    assert!(
        record
            .unresolved_premises()
            .contains(&UnresolvedPremise::LegalOldWholeTupleSubstitution)
    );
    // Formation does not discharge missing original assumptions.
    assert_eq!(
        effect.record().unresolved_premises(),
        record.unresolved_premises()
    );
}

#[test]
fn retained_topology_accepts_whitespace_and_ordinary_apply_is_not_promoted() {
    let spaced = artifact("my apply f = {  my step x = f x;  step }");
    assert!(generate_captured_singleton(&spaced).is_some());
    for source in [
        "my apply f x = f x",
        "my apply f = { my step x = f x; step 0 }",
    ] {
        assert!(generate_captured_singleton(&artifact(source)).is_none());
    }
}

#[test]
fn formation_has_no_string_or_solver_semantic_evidence() {
    let implementation = include_str!("../src/shadow_call_formation.rs");
    for shortcut in [
        "artifact.source(",
        "interpret_old(",
        "solver::",
        "my apply f =",
        "parse_file(",
    ] {
        assert!(
            !implementation.contains(shortcut),
            "unexpected semantic shortcut: {shortcut}"
        );
    }
}
