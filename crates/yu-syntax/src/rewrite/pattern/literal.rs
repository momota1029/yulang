//! Isolated Pattern literal checkpoint before production primary dispatch.

use super::super::{
    RewriteIn,
    literal::{
        NonInterpolatingStringExit, PatternLiteralOpener, RuleLiteralExit,
        non_interpolating_string_literal_witness, rule_literal_witness,
        scan_pattern_literal_opener_witness,
    },
    yumark::FenceBoundary,
};

#[derive(Debug, Eq, PartialEq)]
pub(in crate::rewrite) enum PatternLiteralWitnessExit {
    Rule(RuleLiteralExit),
    String(NonInterpolatingStringExit),
}

/// Applies LC-5's one-quote/three-quote split without making it reachable
/// from the production Pattern primary path before the L7 barrier.
pub(in crate::rewrite) fn pattern_literal_witness(
    mut i: RewriteIn,
    origin: usize,
    fence: &FenceBoundary,
) -> Option<PatternLiteralWitnessExit> {
    let opener = i.token(scan_pattern_literal_opener_witness)?;
    match opener {
        PatternLiteralOpener::Rule(opener) => Some(PatternLiteralWitnessExit::Rule(
            rule_literal_witness(i, opener, origin + 1, fence),
        )),
        PatternLiteralOpener::String(opener, mode) => {
            let opener_length = opener
                .payload_view()
                .spelling()
                .expect("a Pattern string opener is one token")
                .len();
            Some(PatternLiteralWitnessExit::String(
                non_interpolating_string_literal_witness(
                    i,
                    opener,
                    mode,
                    origin + opener_length,
                    fence,
                ),
            ))
        }
    }
}
