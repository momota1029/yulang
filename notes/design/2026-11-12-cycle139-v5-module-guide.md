# I-25 V5 modules and exact remaining obligations

## Public target

`B4TargetV5.Statement` has the same five conclusions as V3, with Initial on
the input state only. Initial is not a successful result, a model witness, a
fuel bound, or an assumption of termination. The concrete boundary uses actual
`InitialSource` and an empty journal. `Reachable` is equivalent to the unchanged
full-feedback `SourceFormed`; arbitrary feedback refresh is not excluded.

`B4SkeletonV5.b4_of_bridges` composes fourteen local obligations. The fourteenth
is `initialReorders`, required to retain V3's single initial premise in order
independence. It is proved concretely using constructor/role equality from
registry reordering. This is not an extra user-language restriction.

## Six laws proved, eight OPEN

Concrete: closure, stepModels, frontierLocal, localIdentity, dictionaryRefl,
initialReorders. `GeneralDictionaryReachableObligations.Remaining` contains
exactly the other eight; `bridges_of_remaining` checks the named field types.
`b4_of_remaining` is CONDITIONAL, not an implemented B4 resolver.

Open: progress, execution, halted, whereAccessible, treeExecution,
canonicalLocalOrder, evidenceNode, generatedChildren. Old raw V4 evidenceNode
is refuted; this new V5 scoped obligation is OPEN, not refuted by that example.
Independent review identified and removed an unnecessary arbitrary-demand
proof burden: EvidenceNode only concerns the saturation root or its Generated
descendants, and whereAccessible only needs the saturation root. The root
accessibility proof supplies recursive child accessibility. The public
Statement is unchanged by this narrowing.

## Evidence work

`GeneralDictionaryReachableEvidenceInitial` proves initial survivor -> Joint,
then stable initial selected -> current Instance, children=[], terminal evidence.
This is ONLY the zero-step case. The older cycle initial-stability theorem can
be lifted to actual feedback stability; a model-bearing example demonstrates
that this stability premise is not empty. Its stronger feedback-selected
classification is not claimed.

`GeneralDictionaryReachableJointBridge` reduces general V5 evidence to
inhabited reachable selected Joint and generation to model-independent selected
Joint on generated nodes. Joint is the unchanged alias-key consistency plus
one simultaneous journal/branch model; it is not defined using Evidence.
Neither residual is proved universally. Arbitrary view/carrier-changing
refresh transport and shared alias-model compatibility remain real gaps.

## Regression

`GeneralDictionaryReachableRegressions.raw_not_reachable` excludes the prior
stale-key journal via the proved reachability/formation equivalence.
`positive_classified` preserves the genuine two-step installation plus
view-changing refresh, actual Stable, selected classification, nonempty model,
and all-model current Evidence. It is one example, not a universal executor.

## A tempting proof shortcut is false

`GeneralDictionaryReachableModelGap` supplies an actual reachable state and
a real journal model but refutes ContextComplete there. Raw-context Models
cannot be upgraded to journal Models using reachability alone. This example
is not asserted Stable and does not refute the V5 evidence bridge.
