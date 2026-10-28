//! Current F5 versus frozen legacy displayed arrow/variable shape only.
//! This is not complete legacy constraint/scheme equivalence, successor-shadow
//! parity, denotational equivalence, soundness, principality, or Apply/call-view
//! behavior evidence.

use super::*;
use yu_types::{NegativeEffectView, PositiveEffectView};

// Exact 11-byte Oracle input recorded in the frozen-source probe note:
// notes/progress/2026-10-06-frozen-oracle-rebuild-and-source-probes.md.
// SHA-256: 6fdaa7a0ce83d2309290787aa7de9f1d9080bacf3f33726ac19974fc954a1273.
const IDENTITY_SOURCE: &str = "my f x = x\n";
// Recorded CLI output from frozen Yulang2 a58eefc31e22141574b6f20c6a5748151c6d79f1,
// not an expectation derived from current inference.
const FROZEN_LEGACY_OUTPUT: &str = "my d0:f: 'a -> 'a = e1:(fn p0:d1:x -> e0:r0:x->d1:x)\n";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DisplayedArrowVariableShape {
    DiagonalIdentity,
}

#[test]
fn current_f5_versus_frozen_legacy_identity_displayed_shape_differential() {
    assert_eq!(IDENTITY_SOURCE.as_bytes(), b"my f x = x\n");
    assert_eq!(IDENTITY_SOURCE.len(), 11);
    let legacy = normalize_legacy_displayed_shape(FROZEN_LEGACY_OUTPUT)
        .expect("frozen legacy output has the supported displayed arrow/variable shape");
    let current = current_identity_displayed_shape(IDENTITY_SOURCE);
    assert_eq!(
        current, legacy,
        "only displayed arrow/variable shape: not complete legacy constraint/scheme \
         equivalence, successor-shadow parity, denotational equivalence, soundness, \
         principality, or Apply/call-view behavior"
    );
}

fn normalize_legacy_displayed_shape(output: &str) -> Option<DisplayedArrowVariableShape> {
    let output = output.strip_suffix('\n').unwrap_or(output);
    if output.contains(['\n', '\r']) {
        return None;
    }
    let (scheme, body) = output.strip_prefix("my d0:f: ")?.split_once(" = ")?;
    if body.is_empty() {
        return None;
    }
    // Only the displayed scheme prefix is compared; the printed expression
    // contains its own arrows and is outside this normalization contract.
    let mut sides = scheme.split("->");
    let argument = sides.next()?.trim();
    let result = sides.next()?.trim();
    if sides.next().is_some() || argument != result {
        return None;
    }
    let variable = argument.strip_prefix('\'')?;
    if variable.is_empty() || !variable.bytes().all(|byte| byte.is_ascii_lowercase()) {
        return None;
    }
    Some(DisplayedArrowVariableShape::DiagonalIdentity)
}

fn current_identity_displayed_shape(source: &str) -> DisplayedArrowVariableShape {
    let hir = module(source, "frozen-legacy-identity.yu");
    assert!(hir.errors().is_empty(), "identity must have no HIR errors");
    assert!(
        hir.diagnostics().is_empty(),
        "identity must have no HIR diagnostics"
    );
    let [HirItem::Binding(binding)] = hir.items() else {
        panic!("exact identity source must register one binding");
    };
    let solved = SolvedModule::solve(collect(hir.clone())).expect("current F5 identity solves");
    assert!(
        solved.errors().is_empty(),
        "identity must have no solver errors"
    );
    let position = *solved
        .root_scheme_positions
        .get(binding.definition_root())
        .expect("identity binding's own root has a scheme position");
    let scheme = solved.schemes[position]
        .as_ref()
        .expect("identity binding's own scheme is finalized");
    let view = solved.closed_types.scheme_view(scheme).unwrap();
    assert_eq!(view.quantifier_count(), 1);
    assert!(view.recursive_bounds().is_empty());
    let PositiveValueView::Function {
        argument,
        argument_effect,
        result_effect,
        result,
    } = view.positive_value(view.predicate()).unwrap()
    else {
        panic!("identity finalized root must be a positive Function");
    };
    assert!(matches!(
        view.negative_effect(argument_effect),
        Ok(NegativeEffectView::Empty)
    ));
    assert!(matches!(
        view.positive_effect(result_effect),
        Ok(PositiveEffectView::Bottom)
    ));
    let NegativeValueView::Quantified(argument) = view.negative_value(argument).unwrap() else {
        panic!("identity argument must be quantified");
    };
    let PositiveValueView::Quantified(result) = view.positive_value(result).unwrap() else {
        panic!("identity result must be quantified");
    };
    assert_eq!(argument.ordinal(), result.ordinal());
    assert_eq!(argument.ordinal(), 0);
    DisplayedArrowVariableShape::DiagonalIdentity
}

#[test]
fn legacy_displayed_shape_normalizer_rejects_unsupported_fragments() {
    for scheme in [
        "'a -> 'b",
        "'a -> 'a -> 'a",
        "'a",
        "Int -> Int",
        "('a) -> ('a)",
        "'a ['e] -> 'a",
        "forall 'a. 'a -> 'a",
        "'a 'b -> 'a 'b",
        "'a#0 -> 'a#0",
        "' -> '",
    ] {
        let output = format!("my d0:f: {scheme} = expression\n");
        assert_eq!(normalize_legacy_displayed_shape(&output), None, "{scheme}");
    }
    for output in [
        "my d0:g: 'a -> 'a = expression\n",
        "my d0:f: 'a -> 'a = ",
        "my d0:f: 'a -> 'a = expression\nextra\n",
    ] {
        assert_eq!(normalize_legacy_displayed_shape(output), None, "{output}");
    }
    assert_eq!(
        normalize_legacy_displayed_shape("my d0:f: 'renamed -> 'renamed = expression\n"),
        Some(DisplayedArrowVariableShape::DiagonalIdentity)
    );
}
