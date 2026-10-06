#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Form, ShadowArtifact};
use yu_core::shadow_derivation::RawStructuralArena;
use yu_core::shadow_directional_protection::{
    AssumedDirectionalInput as Input, AssumedExposure, AssumedOriginalContext, AssumedUpperView,
    ConditionalStatus as DirectionalStatus, DirectionalProtectionPremises,
};
use yu_core::shadow_typed_evidence::*;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

#[test]
fn retained_source_registration_joins_only_supplied_conditional_incidence() {
    let source: Arc<SourceText> = Arc::from("my apply f = { my step x = f x; step }");
    let header = Arc::new(scan_header(source.clone()));
    let artifact = ShadowArtifact::from_parsed(parse_file(
        source,
        header,
        Arc::new(SyntaxEnvironment::empty()),
    ))
    .unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let captured = skeleton.captured_call_input().unwrap();
    let pending_before = skeleton
        .pending()
        .iter()
        .map(|premise| (premise.call().clone(), premise.premise()))
        .collect::<Vec<_>>();
    assert_eq!(pending_before.len(), 7);
    let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
    let registrations = arena
        .nodes()
        .iter()
        .filter_map(|node| node.pending_source_call_registration())
        .collect::<Vec<_>>();
    let [registration] = registrations.as_slice() else {
        panic!("one retained source application")
    };
    let declaration = registration.parameter_declaration.unwrap();
    let outer = skeleton.expression(skeleton.body()).unwrap();
    let local = skeleton.expression(captured.local_lambda()).unwrap();
    assert!(std::ptr::eq(declaration.lambda, outer));
    assert!(!std::ptr::eq(declaration.lambda, local));
    let Form::Lambda {
        parameter: local_parameter,
        ..
    } = local.form()
    else {
        panic!("local step parameter declaration")
    };
    assert_ne!(declaration.parameter, local_parameter);
    assert_eq!(declaration.parameter, captured.outer_parameter());
    assert_eq!(
        registration.source_use_input.binder(),
        declaration.parameter
    );
    assert_eq!(registration.application_premises.len(), 7);

    // Nonzero-sized caller-owned tokens supply semantic assumptions independently.
    // No source position, BinderId or declaration is cast into a semantic token.
    let tokens = [0_u8; 18];
    let context = AssumedOriginalContext {
        beta: &tokens[0],
        scope: &tokens[1],
        xi: &tokens[2],
        shared_variable: &tokens[3],
    };
    let upper_view = AssumedUpperView {
        witness: &tokens[4],
    };
    let exposure = || AssumedExposure {
        source: registration.source,
        binder: registration.source_use_input.binder(),
        context: &context,
    };
    let conclusion = DirectionalProtectionPremises::from_assumed_inputs(
        registration,
        Input::ProtectedVariableAtExposure {
            exposure: exposure(),
            seed: &tokens[5],
        },
        Input::SourceUpperFunctionUse {
            exposure: exposure(),
            upper_view: &upper_view,
        },
        Input::CovariantOutputOccurrence {
            exposure: exposure(),
            upper_view: &upper_view,
            output: &tokens[6],
        },
    )
    .unwrap()
    .derive_conditionally();
    assert_eq!(conclusion.status, DirectionalStatus::Assumed);
    assert!(std::ptr::eq(conclusion.context, &context));
    assert!(std::ptr::eq(conclusion.context.xi, context.xi));
    assert!(std::ptr::eq(conclusion.upper_view, &upper_view));
    assert!(std::ptr::eq(conclusion.covariant_output, &tokens[6]));

    // The returned witnesses wire the chain. Original boundary association,
    // profile realization, Flow/Observe/Receive and activation are still supplied.
    // The directional adapter has no lower input; these graph facts do not prove
    // source-wide no-backflow or original admission/association semantics.
    let nodes = [
        AssumedTypedPort {
            context: conclusion.context,
            view: conclusion.upper_view.witness,
            position: conclusion.covariant_output,
        },
        AssumedTypedPort {
            context: conclusion.context,
            view: &tokens[7],
            position: &tokens[8],
        },
        AssumedTypedPort {
            context: conclusion.context,
            view: &tokens[9],
            position: &tokens[10],
        },
    ];
    let upper_boundary = AssumedBoundary {
        context: conclusion.context,
        witness: &tokens[11],
        original_receiver: &tokens[12],
    };
    let provider_boundary = AssumedBoundary {
        context: conclusion.context,
        witness: &tokens[13],
        original_receiver: &tokens[14],
    };
    let profiles = [
        AssumedProfile {
            witness: conclusion.seed,
            boundary: &upper_boundary,
            port: 0,
        },
        // Independent pre-existing provider protection is retained, not erased.
        AssumedProfile {
            witness: &tokens[13],
            boundary: &provider_boundary,
            port: 2,
        },
    ];
    let flows = [AssumedFlow {
        context: conclusion.context,
        from: 0,
        to: 1,
    }];
    let upper_event = AssumedEvent {
        context: conclusion.context,
        witness: &tokens[15],
    };
    let provider_event = AssumedEvent {
        context: conclusion.context,
        witness: &tokens[16],
    };
    let observations = [
        AssumedObserve {
            event: &upper_event,
            port: 1,
        },
        AssumedObserve {
            event: &provider_event,
            port: 2,
        },
    ];
    let handler = AssumedHandler {
        context: conclusion.context,
        witness: &tokens[17],
        owner: &tokens[1],
    };
    // Each receipt is already expanded through its supplied corresponding path.
    let receipts = [
        AssumedReceive {
            context: conclusion.context,
            owner: handler.owner,
            port: 1,
        },
        AssumedReceive {
            context: conclusion.context,
            owner: handler.owner,
            port: 2,
        },
    ];
    let graph = AssumedTypedEvidence::new(
        conclusion.context,
        &nodes,
        &profiles,
        &flows,
        &observations,
        &receipts,
    )
    .unwrap();
    let active_handlers = [handler.witness];
    let active_owners = [
        handler.owner,
        upper_boundary.original_receiver,
        provider_boundary.original_receiver,
    ];
    let current = AssumedConfiguration {
        context: conclusion.context,
        active_handlers: &active_handlers,
        active_owners: &active_owners,
    };
    let upper = graph
        .query_conditionally(0, &upper_event, &handler, &current)
        .unwrap();
    assert_eq!(upper.status, ConditionalStatus::Assumed);
    assert!(upper.path && upper.inc_c);
    let unsupported_join = graph
        .query_conditionally(0, &provider_event, &handler, &current)
        .unwrap();
    assert!(!unsupported_join.path && !unsupported_join.inc_c);
    let provider = graph
        .query_conditionally(1, &provider_event, &handler, &current)
        .unwrap();
    assert!(provider.path && provider.inc_c);

    let remaining_owners = [handler.owner, provider_boundary.original_receiver];
    let expired = AssumedConfiguration {
        context: conclusion.context,
        active_handlers: &active_handlers,
        active_owners: &remaining_owners,
    };
    let upper_expired = graph
        .query_conditionally(0, &upper_event, &handler, &expired)
        .unwrap();
    assert!(upper_expired.path);
    assert!(!upper_expired.inc_c);
    assert!(
        graph
            .query_conditionally(1, &provider_event, &handler, &expired)
            .unwrap()
            .inc_c
    );

    // Structural declaration ownership and all seven unresolved semantic rows
    // survive the conditional chain; no source acceptance or scheme is obtained.
    let retained = arena
        .nodes()
        .iter()
        .find_map(|node| node.pending_source_call_registration())
        .unwrap();
    let retained_declaration = retained.parameter_declaration.unwrap();
    assert!(std::ptr::eq(
        retained_declaration.lambda,
        declaration.lambda
    ));
    assert!(std::ptr::eq(
        retained_declaration.parameter,
        declaration.parameter
    ));
    assert!(std::ptr::eq(
        retained.application_premises,
        registration.application_premises
    ));
    assert_eq!(retained.application_premises.len(), 7);
    assert_eq!(
        skeleton
            .pending()
            .iter()
            .map(|premise| (premise.call().clone(), premise.premise()))
            .collect::<Vec<_>>(),
        pending_before
    );
}
