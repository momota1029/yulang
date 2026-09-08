use crate::tests::support::*;

use crate::{
    ambient_claim::{AmbientClaimContext, AmbientClaimView, ProofSite},
    lexical::yumark::{FenceOpener, FencePrefixPolicy},
};

fn statement_with_ambient<'source, 'frame>(
    source: &'source str,
    ambient: impl Into<AmbientClaimContext<'frame>>,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    Vec<CommittedRecoveryRecord>,
    TailExit,
    &'source str,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = statement_normalized(
        In::new(&mut input, &mut recover, &mut output),
        0,
        0,
        0,
        LineEntry::InLine,
        fence,
        ambient.into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    );
    let mut exit = crate::handoff::ordinary_exit(exit);
    if let Err(Either::Right(end)) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, records, exit, input)
}

// The sentinel proves that the actual target owner ran the hook. A missing or
// dropped hook cannot pass merely because the inert parser output is unchanged.
#[derive(Debug)]
struct ProofReached;

fn prove_entrance(source: &str, ambient: AmbientClaimContext<'_>, fence: Option<&FenceBoundary>) {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        statement_with_ambient(source, ambient, fence)
    }));
    match result {
        Err(error) if error.is::<ProofReached>() => {}
        Err(error) => std::panic::resume_unwind(error),
        Ok(_) => panic!("proof target was not observed: {source:?}"),
    }
}

fn unavailable_pv(site: ProofSite, view: Option<AmbientClaimView<'_>>) {
    if site == ProofSite::PolymorphicVariant {
        assert!(view.is_none(), "virtual Type/PV must remain unavailable");
        std::panic::panic_any(ProofReached);
    }
}

#[test]
fn actual_virtual_type_pv_entrances_observe_unavailable_context() {
    let root = AmbientClaimView::root_statement(8);
    let frame = root.if_companion(2);
    let context = AmbientClaimContext::from(Some(root.with_if(&frame))).with_proof(unavailable_pv);
    for source in [
        "\"%{if x:\n  type T = :{A}\n}\"",
        "\"%{mod M { type T = :{A} }}\"",
        "\"\"\"%{if x:\n  type T = :{A}\n}\"\"\"",
        "\"\"\"%{mod M { type T = :{A} }}\"\"\"",
        "\"%{\"%{if x:\n  type T = :{A}\n}\"}\"",
        "\"%{\"%{mod M { type T = :{A} }}\"}\"",
    ] {
        prove_entrance(source, context, None);
    }
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::None,
        close_column: 0,
    };
    for source in [
        "\"%{\"%{if x:\n  type T = :{A}\n```\nouter",
        "\"%{\"%{mod M { type T = :{A}\n```\nouter",
    ] {
        prove_entrance(source, context, Some(&fence));
    }
}

fn ordinary_pv(site: ProofSite, view: Option<AmbientClaimView<'_>>) {
    if site == ProofSite::PolymorphicVariant {
        AmbientClaimContext::from(view).assert_shape(Some(0), &[9]);
        std::panic::panic_any(ProofReached);
    }
}

#[test]
fn actual_recursive_type_pv_entrances_preserve_the_ordinary_context() {
    let root = AmbientClaimView::root_statement(8);
    let frame = root.if_companion(9);
    let context = AmbientClaimContext::from(Some(root.with_if(&frame))).with_proof(ordinary_pv);
    for source in [
        "type T = :{A}",
        "type T = (:{A})",
        "type T = F(:{A})",
        "type T = {x: :{A}}",
        "type T = for 'a: :{A}",
        "type T = '[ :{A} ]",
    ] {
        prove_entrance(source, context, None);
    }
}

fn caller_else(site: ProofSite, view: Option<AmbientClaimView<'_>>) {
    if site == ProofSite::ElseBody {
        AmbientClaimContext::from(view).assert_shape(Some(0), &[9]);
        std::panic::panic_any(ProofReached);
    }
}

fn caller_tail(site: ProofSite, view: Option<AmbientClaimView<'_>>) {
    if site == ProofSite::IfOuterTail {
        AmbientClaimContext::from(view).assert_shape(Some(0), &[9]);
        std::panic::panic_any(ProofReached);
    }
}

fn root_else(site: ProofSite, view: Option<AmbientClaimView<'_>>) {
    if site == ProofSite::ElseBody {
        AmbientClaimContext::from(view).assert_shape(Some(0), &[]);
        std::panic::panic_any(ProofReached);
    }
}

fn root_tail(site: ProofSite, view: Option<AmbientClaimView<'_>>) {
    if site == ProofSite::IfOuterTail {
        AmbientClaimContext::from(view).assert_shape(Some(0), &[]);
        std::panic::panic_any(ProofReached);
    }
}

fn active_arm_pv(site: ProofSite, view: Option<AmbientClaimView<'_>>) {
    if site == ProofSite::PolymorphicVariant {
        AmbientClaimContext::from(view).assert_shape(Some(2), &[0, 9]);
        std::panic::panic_any(ProofReached);
    }
}

#[test]
fn actual_if_else_and_outer_tail_retire_only_the_own_companion() {
    let root = AmbientClaimView::root_statement(8);
    let frame = root.if_companion(9);
    let context = AmbientClaimContext::from(Some(root.with_if(&frame)));
    prove_entrance(
        "if x:\n  type T = :{A}",
        context.with_proof(active_arm_pv),
        None,
    );
    prove_entrance(
        "if x: value else: other",
        context.with_proof(caller_else),
        None,
    );
    let root_context = AmbientClaimContext::from(Some(root));
    prove_entrance(
        "if x: value else: other",
        root_context.with_proof(root_else),
        None,
    );
    for source in [
        "if x: value",
        "if x: value else: other",
        "if x: value elsif y: other",
        "if x: @ else: other",
        "if x:",
    ] {
        prove_entrance(source, context.with_proof(caller_tail), None);
        prove_entrance(source, root_context.with_proof(root_tail), None);
    }
}

#[test]
fn ambient_carrier_preserves_ordinary_outputs_through_if_exits_and_type_owners() {
    let root = AmbientClaimView::root_statement(8);
    let frame = root.if_companion(2);
    let caller = root.with_if(&frame);
    for source in [
        "if x: value",
        "if x: value elsif y: other else: end",
        "if x: if y: value else: other else: end",
        "if x: @ else: value",
        "if x:",
        "if x { type T = :{A} }(tail)",
        "if x:\n  type T = :{A}\nelse: value",
        "type T = (for 'a: A, '[E], :{Tag}, [R], {x: X})",
        "my value: :{Tag} = body",
        "cast(value): :{Tag};",
        "impl :{Tag};",
        "role :{Tag};",
        "act :{Tag};",
    ] {
        assert_eq!(
            statement_with_ambient(source, Some(caller), None),
            statement_with_ambient(source, None, None),
            "carrier-only gate changed output: {source:?}",
        );
    }
}

#[test]
fn unavailable_interpolation_reaches_indented_and_braced_type_pv_owners() {
    let root = AmbientClaimView::root_statement(8);
    let frame = root.if_companion(2);
    let caller = root.with_if(&frame);
    for source in [
        "\"%{type T = :{A}}\"",
        "\"\"\"%{type T = :{A}}\"\"\"",
        "\"%{if x:\n  type T = :{A}\n}\"",
        "\"%{mod M { type T = :{A} }}\"",
        "\"%{\"%{type T = :{A}}\"}\"",
        "if x: \"%{if y:\n  type T = :{A}\n}\" else: value",
    ] {
        let available = statement_with_ambient(source, Some(caller), None);
        let unavailable = statement_with_ambient(source, None, None);
        assert_eq!(available, unavailable, "{source:?}");
        let tree = SyntaxNode::new_root(unavailable.0);
        assert!(
            tree.descendants()
                .any(|node| node.kind() == SyntaxKind::PolymorphicVariantType),
            "control must reach a nested Type/PV: {source:?}",
        );
    }
}

#[test]
fn unavailable_fence_terminated_nested_interpolation_preserves_the_outer_result() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::None,
        close_column: 0,
    };
    let source = "if x: \"%{\"%{type T = :{A}\n```\nouter";
    let root = AmbientClaimView::root_statement(4);
    let frame = root.if_companion(0);
    let available = statement_with_ambient(source, Some(root.with_if(&frame)), Some(&fence));
    let unavailable = statement_with_ambient(source, None, Some(&fence));
    assert_eq!(available, unavailable);
    assert!(
        matches!(unavailable.2, Err(Either::Left(ref item)) if item.payload_view().is_boundary())
    );
}
