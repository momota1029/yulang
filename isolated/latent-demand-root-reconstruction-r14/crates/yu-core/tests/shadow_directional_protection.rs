#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::ShadowArtifact;
use yu_core::shadow_derivation::RawStructuralArena;
use yu_core::shadow_directional_protection::{
    AssumedDirectionalInput as Input, AssumedExposure, AssumedOriginalContext, AssumedUpperView,
    ConditionalStatus, DirectionalProtectionPremises,
};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

#[test]
fn conditional_rule_retains_assumptions_and_rejects_mixed_premises() {
    let source: Arc<SourceText> = Arc::from("my apply f x = f (f x)");
    let header = Arc::new(scan_header(source.clone()));
    let artifact = ShadowArtifact::from_parsed(parse_file(
        source,
        header,
        Arc::new(SyntaxEnvironment::empty()),
    ))
    .unwrap();
    let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
    let registrations = arena
        .nodes()
        .iter()
        .filter_map(|node| node.pending_source_call_registration())
        .collect::<Vec<_>>();
    assert_eq!(registrations.len(), 2);
    let registration = &registrations[0];
    let [beta, scope, xi, variable, seed, view, output, other] = [0_u8, 1, 2, 3, 4, 5, 6, 7];
    let context = AssumedOriginalContext {
        beta: &beta,
        scope: &scope,
        xi: &xi,
        shared_variable: &variable,
    };
    let upper_view = AssumedUpperView { witness: &view };
    let other_view = AssumedUpperView { witness: &view };
    let exposure = |source, binder, context| AssumedExposure {
        source,
        binder,
        context,
    };
    let source = registration.source;
    let binder = registration.source_use_input.binder();
    let inputs = |upper_source, upper_binder, upper_context, output_view| {
        (
            Input::ProtectedVariableAtExposure {
                exposure: exposure(source, binder, &context),
                seed: &seed,
            },
            Input::SourceUpperFunctionUse {
                exposure: exposure(upper_source, upper_binder, upper_context),
                upper_view: &upper_view,
            },
            Input::CovariantOutputOccurrence {
                exposure: exposure(source, binder, &context),
                upper_view: output_view,
                output: &output,
            },
        )
    };
    let (s, u, o) = inputs(source, binder, &context, &upper_view);
    let derivation = DirectionalProtectionPremises::from_assumed_inputs(registration, s, u, o)
        .unwrap()
        .derive_conditionally();
    assert_eq!(derivation.status, ConditionalStatus::Assumed);
    assert_eq!(derivation.source, source);
    assert_eq!(derivation.binder, binder);
    assert!(std::ptr::eq(derivation.context, &context));
    assert!(std::ptr::eq(derivation.seed, &seed));
    assert!(std::ptr::eq(derivation.upper_view, &upper_view));
    assert!(std::ptr::eq(derivation.covariant_output, &output));
    assert!(std::ptr::eq(
        registration.application_premises,
        arena
            .nodes()
            .iter()
            .find(|node| &node.source == source)
            .unwrap()
            .call
            .as_ref()
            .unwrap()
            .application_premises
            .as_slice()
    ));

    // Each changed family is a different assumption packet, even with equal values.
    let mixed_contexts = [
        AssumedOriginalContext {
            beta: &other,
            ..context
        },
        AssumedOriginalContext {
            scope: &other,
            ..context
        },
        AssumedOriginalContext {
            xi: &other,
            ..context
        },
        AssumedOriginalContext {
            shared_variable: &other,
            ..context
        },
        AssumedOriginalContext { ..context },
    ];
    for mixed in &mixed_contexts {
        let (s, u, o) = inputs(source, binder, mixed, &upper_view);
        assert!(
            DirectionalProtectionPremises::from_assumed_inputs(registration, s, u, o).is_none()
        );
    }
    let (s, u, o) = inputs(registrations[1].source, binder, &context, &upper_view);
    assert!(DirectionalProtectionPremises::from_assumed_inputs(registration, s, u, o).is_none());
    let (s, u, o) = inputs(source, binder, &context, &other_view);
    assert!(DirectionalProtectionPremises::from_assumed_inputs(registration, s, u, o).is_none());
    let (s, u, o) = inputs(source, binder, &context, &upper_view);
    assert!(DirectionalProtectionPremises::from_assumed_inputs(registration, u, s, o).is_none());
}
