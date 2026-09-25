use super::*;

#[test]
fn f5c_candidate_depth_256_finalizes_and_drops_on_small_stack() {
    const DEPTH: usize = 256;
    let stack_size = if cfg!(debug_assertions) {
        512 * 1024
    } else {
        64 * 1024
    };

    std::thread::Builder::new()
        .stack_size(stack_size)
        .spawn(|| {
            let mut positive = F5cPositive::Int;
            let mut negative = F5cNegative::Int;
            for _ in 0..DEPTH {
                positive = F5cPositive::Function {
                    argument: Box::new(F5cNegative::Top),
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: Box::new(positive),
                };
                negative = F5cNegative::Function {
                    argument: Box::new(F5cPositive::Bottom),
                    argument_effect: F5cPositiveEffect::Bottom,
                    result_effect: F5cNegativeEffect::Empty,
                    result: Box::new(negative),
                };
            }

            let draft = GeneralizationDraft {
                quantifier_count: 0,
                recursive_bounds: vec![F5cRecursiveBound {
                    ordinal: 0,
                    lower: positive,
                    upper: negative,
                }],
                predicate: F5cPositive::Int,
            };
            let mut finalization = ClosedTypeFinalizationSession::try_new().unwrap();
            let finalized = InferenceSession::finalize_generalization_draft_raw(
                &mut finalization,
                &draft,
                false,
            )
            .unwrap();

            drop(finalized);
            drop(draft);
            drop(finalization);
        })
        .unwrap()
        .join()
        .unwrap();
}
