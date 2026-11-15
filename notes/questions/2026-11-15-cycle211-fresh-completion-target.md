# Cycle 211: FreshCompletion is stronger than the final B4 obligation

## Recommendation first

Defer the `GeneralDictionaryDefaultProduction208.FreshCompletion` helper in its
present form: it is false. Keep the selected domain, Evidence, Models, Step and
final B4 Statement unchanged. First check whether selected dictionary children
can be shown generated directly from their own selection/registration, rather
than demanding an installation extension for every selected parent. This is a
proof-route change, not a proposed language-semantic change. If that route does
not close the final theorem, state the remaining exact obligation explicitly;
do not replace it silently with an inhabitance assumption.

## Closed counterexample

`GeneralDictionaryDefaultFreshProbe211Refutation.not_freshCompletion` proves
`¬ GeneralDictionaryDefaultProduction208.FreshCompletion roles` for a concrete
checked registry. Its parent has three where clauses. Two role-1 children have
no arguments and carry incompatible named outputs (Int and a tagged Int).
Their actual same-input merge makes the complete journal inconsistent. A third,
independent role-2/id-39 terminal child remains selected: it is not in the merged
alias class. Its implementation has not been recorded.

The six `GeneralDictionaryDefaultFreshProbe211*` modules construct an inhabited
initial state, actual installation and merge, then a terminal state using the
existing terminating executor. The final module proves `corrected_reachable`,
`corrected_stable`, `corrected_selected` and `not_recorded` for the repaired
I38 boundary, not just the historical V6 boundary. `FreshCompletion` would supply
an Extension and hence a model of this empty journal, a contradiction.

## What this does not refute

This is not a counterexample to `B4SkeletonV7.EvidenceNode`,
`B4SkeletonV7.GeneratedChildren` or the B4 Statement. The selected sibling is
terminal, so its child-generation obligation has no children. EvidenceAt is
model-relative and is vacuous when the journal has no model. Both facts are
proved separately by `evidence_vacuous` and `children_vacuous`.

The global EvidenceNode and the full B4 Statement are not proved by this probe.
No new model-inhabitance premise or selection guard has been added. The issue is
the stronger completion helper, not a finding that the specified language must
reject this independent sibling.

## Verification

Focused `lake build Yulang.GeneralDictionaryDefaultFreshProbe211Refutation
--wfail` passed. A separate Lean `--trust=0 -DwarningAsError=true` audit of the
refutation and its corrected-boundary/vacuity lemmas passed; dependencies were
only propext, Classical.choice and Quot.sound. No full umbrella build is claimed.
