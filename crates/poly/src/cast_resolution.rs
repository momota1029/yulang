//! Neutral cardinality classification for ordinary value-cast candidates.
//!
//! See `notes/design/2026-07-21-ordinary-cast-resolution-spec.md` for the project context.

/// The resolution of ordinary value-cast candidates already narrowed to one exact constructor pair.
///
/// Callers must supply only `CastRuleKind::Value` candidates whose source constructor path and
/// target constructor path exactly equal the requested paths. This type records only the resulting
/// candidate cardinality; it contains no registry-matching or generic-scheme viability policy.
///
/// `Ambiguous` has the invariant that its vector contains at least two entries. The public variant
/// remains directly constructible, while [`classify_ordinary_cast_candidates`] preserves the
/// invariant for every result it creates.
///
/// See `notes/design/2026-07-21-ordinary-cast-resolution-spec.md` for the ordinary-cast design.
pub enum OrdinaryCastResolution<R> {
    /// No declaration matches the exact constructor pair.
    Missing,
    /// Exactly one declaration matches the exact constructor pair.
    Unique(R),
    /// At least two declarations match the exact constructor pair.
    Ambiguous(Vec<R>),
}

/// Classifies the cardinality of already-pair-filtered ordinary value-cast candidates.
///
/// The input must already be restricted to `CastRuleKind::Value`, exact source constructor path
/// equality, and exact target constructor path equality. This function performs no path comparison,
/// cast-kind filtering, or generic-scheme viability filtering; it only counts declarations.
///
/// Payloads are preserved without cloning or alteration. An ambiguous payload preserves the input
/// iteration order: this classifier contains no sorting or other reordering logic. Stable-identity
/// sorting for diagnostics belongs to a later layer.
pub fn classify_ordinary_cast_candidates<R>(
    candidates_for_exact_pair: impl IntoIterator<Item = R>,
) -> OrdinaryCastResolution<R> {
    let mut candidates = candidates_for_exact_pair.into_iter();
    let Some(first) = candidates.next() else {
        return OrdinaryCastResolution::Missing;
    };
    let Some(second) = candidates.next() else {
        return OrdinaryCastResolution::Unique(first);
    };

    let mut ambiguous = vec![first, second];
    ambiguous.extend(candidates);
    OrdinaryCastResolution::Ambiguous(ambiguous)
}

#[cfg(test)]
mod tests {
    use super::{OrdinaryCastResolution, classify_ordinary_cast_candidates};

    #[derive(Debug, PartialEq, Eq)]
    struct InferCastRuleLike {
        scheme_name: String,
    }

    #[derive(Debug, PartialEq, Eq)]
    struct PolyCastRuleLike {
        def_id: u32,
        scheme_name: &'static str,
    }

    #[test]
    fn zero_candidates_are_missing() {
        let resolution = classify_ordinary_cast_candidates(std::iter::empty::<InferCastRuleLike>());

        assert!(matches!(resolution, OrdinaryCastResolution::Missing));
    }

    #[test]
    fn one_candidate_is_preserved_as_unique() {
        let candidate = InferCastRuleLike {
            scheme_name: String::from("infer-owned-scheme"),
        };

        let resolution = classify_ordinary_cast_candidates([candidate]);

        let OrdinaryCastResolution::Unique(candidate) = resolution else {
            panic!("one candidate must classify as unique");
        };
        assert_eq!(candidate.scheme_name, "infer-owned-scheme");
    }

    #[test]
    fn two_candidates_are_ambiguous_in_input_order() {
        let candidates = [
            PolyCastRuleLike {
                def_id: 20,
                scheme_name: "second-by-identity",
            },
            PolyCastRuleLike {
                def_id: 10,
                scheme_name: "first-by-identity",
            },
        ];

        let resolution = classify_ordinary_cast_candidates(candidates);

        let OrdinaryCastResolution::Ambiguous(candidates) = resolution else {
            panic!("two candidates must classify as ambiguous");
        };
        assert_eq!(
            candidates,
            vec![
                PolyCastRuleLike {
                    def_id: 20,
                    scheme_name: "second-by-identity",
                },
                PolyCastRuleLike {
                    def_id: 10,
                    scheme_name: "first-by-identity",
                },
            ]
        );
    }

    #[test]
    fn larger_ambiguous_borrowed_payload_is_stable_in_input_iteration_order() {
        let candidates = [
            PolyCastRuleLike {
                def_id: 40,
                scheme_name: "forty",
            },
            PolyCastRuleLike {
                def_id: 10,
                scheme_name: "ten",
            },
            PolyCastRuleLike {
                def_id: 50,
                scheme_name: "fifty",
            },
            PolyCastRuleLike {
                def_id: 20,
                scheme_name: "twenty",
            },
            PolyCastRuleLike {
                def_id: 30,
                scheme_name: "thirty",
            },
        ];

        let resolution = classify_ordinary_cast_candidates(candidates.iter());

        let OrdinaryCastResolution::Ambiguous(classified) = resolution else {
            panic!("five candidates must classify as ambiguous");
        };
        assert_eq!(classified.len(), candidates.len());
        assert!(
            classified
                .into_iter()
                .zip(candidates.iter())
                .all(|(actual, expected)| std::ptr::eq(actual, expected))
        );
    }
}
