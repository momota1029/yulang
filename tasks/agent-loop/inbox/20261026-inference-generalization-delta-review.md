# Independent delta review: canonical generalization transport

Review ID: INFERENCE-GENERALIZATION-DELTA-REVIEW-20261026/r1.
Reviewer: `/root/inference_frontier`, non-author. Producer/primary: `/root`.
This is the bounded M1 delta review requested on 2026-10-26, not a repeat of
the original broad review or an expansion of its accepted source domain.

## Disposition

**ACCEPT the repaired finite-store component. M1 is CLOSED. No new blocking,
major, or minor findings.** The first review remains byte-preserved. Acceptance
is for the exact constructive solution-transport, canonical minimum, and finite
allocation statements below. Actual native freshening/source correspondence,
the original inference-soundness/A/B roots, and production readiness remain
open as recorded in the initial review and producer handoff.

## Frozen review targets

Repository root: `/workspace/scratch/f98087c7ac1a/yulang`.
Isolated project: `/workspace/scratch/f98087c7ac1a/inference-generalization/`.

| Artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `tasks/agent-loop/inbox/20261026-inference-generalization.md` | `2d4641a6d0f2817720f0784a4b49439be31eb9b42170fc3a471aa2f2e09c134b` |
| Original `20261026-inference-generalization-review.md` | `3138339effb6e69f52529aaedd2b305dc495dd77f3522ff1f7fcdeb07df9f3e7` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |

The source and both dependency hashes match their isolated-project copies.
Both dependencies and the initial review remain unchanged from the first
review. The newly available producer handoff was read in full; its stated
hashes, theorem boundaries, and M1 account agree with the actual declarations.

## M1 closure: exact minima

All declarations below are in `YulangClosure.SimpleSub.Generalization`.

The arbitrary-map `quotientLevels` definition is unchanged and is now accurately
described as a **seeded lower envelope**. No canonicality has been silently
added to the broad forward pullback theorem.

The added definition is exactly:

```text
Canonical n q :=
  (forall k i, i < n -> q k i < n) and
  (forall k i, i < n -> q k (q k i) = q k i).
```

`FiberMinimum n before q k representative minimum` supplies both inequalities:
the candidate is below every finite fiber member's level, and every common
lower bound of those levels is below the candidate. This is an exact
greatest-lower-bound characterization, not merely the previously proved
nonincrease property.

`quotientLevels_is_minimum` explicitly requires `representative < n` and
`q k representative = representative`. Thus the initial fold seed is the
level of a genuine member of the nonempty finite fiber. Its first conjunct
uses `quotientLevels_le`; the second uses the newly proved fold lower-bound
invariant, with the representative itself establishing the initial bound.
Neither exact minimality nor a solution property is assumed.

`canonical_quotient_minimum` applies that theorem to every original bounded
row's image, using the two actual fields of `Canonical`. This excludes the
initial review's in-range-but-nonidempotent swap counterexample. The `n = 0`
case has no bounded rows and introduces no spurious nonempty fiber claim.

## M1 closure: post-quotient coordinates

`canonical_post_use_bounded` assumes `Canonical n q`, `use < count`, and
`i < n`. It proves

```text
freshen n boundary after use k (q k i) < n * (count + 1).
```

The low case uses the representative's actual range bound; the high case
applies the original copy-block arithmetic to that representative. Combined
with the unchanged `transport_future`, all these post-use coordinates are
disjoint from the fixed future-client region.

`canonical_post_uses_disjoint` assumes bounded original indices, distinct use
IDs, and post-quotient eligibility of both representatives. It proves their
fresh images unequal by applying `distinct_uses_disjoint` to the canonical
images. No inequality is claimed for deliberately shared low anchors. In-range
canonicality excludes both the previous cross-use collision and the previous
collision with a future-client coordinate. Post-quotient merged rows within
one use may still intentionally share their canonical image.

## Root statements and witness preservation

The old arbitrary-map minimum-named theorem is now
`lowered_quotient_uses_with_clients`. Its complete audited type and axiom block
are **identical to the original after replacing only the declaration name**.
The complete audited type/axiom blocks of `transport_freshen`,
`base_term_pullback`, `fresh_term_pullback`, `quotient_uses_sound`, and
`quotient_uses_with_clients` are byte-identical to their original audit blocks.
The broad forward result was therefore preserved rather than narrowed to fix
the interpretation problem.

The new `minimum_quotient_uses_with_clients` adds the meaningful
`Canonical n q` hypothesis. Its other inputs remain a bounded original store,
bounded requested use IDs, arbitrary finite client clauses, and one valuation
solving the post-quotient copied store together with clients renamed through
the same transport. It returns the conjunction of:

1. Satisfaction of the complete original store, all requested uses, and the
   original client clauses under the single valuation `rho o transport`.
2. `FiberMinimum` at every bounded original row's canonical image.
3. The allocation-region bound for every requested post-use coordinate.

These three conclusions follow from the broad lowered theorem and the newly
proved canonical results. No per-clause/per-use witness, commuting-square
assumption, exact-minimum assumption, or native-success premise was added.
The separate distinct-use theorem supplies the additional disjointness result;
the root's conjunction is accurately described in the handoff.

## Handoff and source-boundary repair

The source header and new handoff now explicitly distinguish the complete
supplied-store construction from actual reachable-high native publication.
They leave exact publication correspondence or an independently proved
solution-extension argument as an obligation. They do not infer that a native
solution satisfies every clause in the model's larger copied store.

The handoff also correctly preserves captured-local/non-generic/current-level
eligibility, retained-bound closure, canonical-row/allocation correspondence,
and source scope. It records that the original Scala path is absent and was not
freshly inspected, while identifying the actual Rust owners inspected in the
first review. It does not equate mutable type levels with immutable Value birth.

Full Call/effect meaning, native success and recursive solution construction,
source witness/environment realization, interleaved lets, principal coverage,
and termination remain open. The repair closes the earlier interpretation
finding; it does not close these original parent obligations.

## Verification inspected

The reviewer ran no Lean checker, compiler, tests, or Git command. No concrete
checker gap warranted a rerun. The producer's final build reports four jobs
successful with no warnings/errors, and the producer reports final audit exit 0.
The following exact evidence was read and hashed:

| Isolated-project evidence | SHA-256 |
| --- | --- |
| `check-07.log` | `d8e3d6c573b1528d66ccac5b9518e2998d60c7e49821e218eaba7195756d4991` |
| `audit-08.log` | `f9ca2f65d761a9352043c0ca5f73228448895d874a28939aa6b3187280e35a85` |
| Unchanged `GeneralizationAudit.lean` | `3b71221b4dd09d8fa360e0df953827ac0de9957d5c7636511b6f88cecf8929ff` |

The module-origin audit includes every theorem, including private/generated
declarations. Independently parsed **71 unique matching begin/end blocks**,
each with a complete type and exactly one axiom report. The new canonical,
minimum, and allocation theorem types agree with the source inspected above.
Actual axiom distribution: **35 empty**, **10 `propext`**, and **26 `propext,
Quot.sound`**. No error, warning, `sorryAx`, unchecked native evaluation, or
checker bypass appears. The new proofs contain no holes or project axioms.

The producer handoff preserves the failed elaboration checks preceding this
successful repair. This review does not replace those logs or imply that the
initial version already established the new canonical conclusions.

## Write cessation

The sole reviewer write is this delta receipt. The original review is unchanged.
No source, dependency, cache, scheduler record, expected output, or other artifact
was edited. No child or persistent process was launched.

**Delta review complete; writes stopped.** The primary owns integration and any
claim promotion, subject to the exact accepted scope above.
