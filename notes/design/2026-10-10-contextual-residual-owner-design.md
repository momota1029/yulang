# Contextual effect residual owner design

Status: Reviewed; not user-approved
Scope: Candidate representation and lifecycle for contextual effect-row residuals
Authority: None; annotation meaning remains governed by
[`annotation-effect-hygiene-integration.md`](2026-10-10-annotation-effect-hygiene-integration.md)
Baseline: `83b22c95369538a3f4c93810f9693500c12c9937`
Reviewed-by: independent residual semantic review and spec conformance review;
  both delta reviews closed all findings on the design body at SHA-256
  `c01281271a94cfcfed83b9aea215098d06ec990507c663f41dbfb9fa59da747b`
Supersedes: None

## 1. Existing decisions and target

The selected annotation policy is unchanged: contravariant concrete `[E]`
permits local subtraction at that annotation position; covariant `[E]` allows
that concrete effect. The returned callback scheme remains
`(int -> ['b, io] 'c) -> int -> ['b] 'c`. The whole example is an end-to-end
hygiene obligation: its construction and proof need annotation-local authority,
the `run_io` handler residual, preservation of independent effects, and the
returned Function use. These have distinct owners, but handler residual
behavior is not outside the hygiene case. Existing conditional results do not
prove the exact source/result pair.

The approved intrusion rule still equates an actual parent/copy row pair when
the pair is in one SCC. This draft asks how contextual residual owners follow
that equality. It does not weaken or replace intrusion.

## 2. Current implementation boundary

At this baseline, effect pair/task identities contain endpoint identities but
no attachment context (`crates/yu-solver/src/lib.rs:769–775`). `BoundKey`
likewise has only owner, side and endpoint
(`crates/yu-solver/src/candidate_effect.rs:34`). Replay and equal-endpoint
omission are endpoint-only (`candidate_extrusion.rs:595–631,675–677`).
Capture/freshening and SCC bound transfer retain endpoints and origins, with no
contextual residual record (`candidate_scheme.rs:79,416–506,710–864`;
`candidate_intrusion.rs:471–480,541–592`). The candidate formal constructor
still rejects concrete effect rows (`candidate_source.rs:77–81`;
`candidate_effect.rs:876–904`).

Oracle's residual table key is `(physical source TypeVar, retained families,
residual LEFT weight)`. Right debt and the original tail are absent from that
key, but remain on each emitted gamma-to-tail relation
(`crates/infer/src/constraints/row_effect.rs:180–232` at Oracle pin
`a58eefc31e22141574b6f20c6a5748151c6d79f1`). Filters are checked and registered
before the residual rule; same-source/tail omission additionally requires an
empty right weight (`row_effect.rs:120–149`).

## 3. Candidate carrier, not yet selected

The smallest candidate that retains the observed distinctions is:

```text
Attachment = (annotation owner, exact annotation occurrence, concrete-member
              ordinal, composed polarity, resolved effect operand)
EffectOperand = nominal effect identity + resolved type arguments
                + source symbolic-row coordinate

Context = exact left per-attachment (POP count, PUSH count, current family)
        + insertion filter
        + exact right per-attachment POP counts

ContextualBound = row owner + side + endpoint + context + origin dependencies

ResidualKey = (residual source lineage, retained concrete heads,
               residual LEFT weight)

ResidualRecipe = key + gamma row + source-to-Row(heads,gamma) relation
                + contextual gamma-to-tail relations + origins
```

The exact annotation occurrence and member ordinal distinguish two same-family
attachments in one binding. Nominal identity and resolved type arguments are
retained; spelling is not identity. The declared family and active residual
family are separate facts. Word cancellation changes only the active residual
payload; it does not delete an independent concrete contribution or transfer
another attachment's authority. Right debt and the original tail belong to each
outgoing relation, not the residual key. Distinct contexts on the same residual
gamma therefore retain distinct replay obligations.

An exact context language may be needed for a source class with unbounded
counts; a worklist entry cannot store one item per word in that class. A
symbolic language ID alone is insufficient: the language operations,
equivalence test, observer and termination argument must be exact.

## 4. Parent/copy equality and residual lineage

Two operations must remain distinct:

1. Apply approved SCC intrusion to every actual recorded parent/copy pair,
including a gamma pair when that pair's own provenance and SCC qualify.
Transfer both bound sides, origins and all contextual replay obligations.
2. Decide whether two separately created residual gammas become equal merely
because their source rows were identified and their residual keys now compare
equal.

Operation 1 is selected. Operation 2 is unresolved. The proposed
non-coalescing candidate keeps residual constructor lineage while canonical
source representatives are shared. Every source-row equality must replay its
new and future lowers into all retained residual recipes. Cache reindexing alone
must neither merge gammas nor discard recipes. This candidate still needs a
proof that retaining separate residuals preserves the required source behavior
and principality.

The equation

```text
gamma(c, H, L) = gamma(p, H, transport(L))
```

is not established by `c = p`, current intrusion, or the Oracle residual key.
An unrestricted conditional countermodel gives the two gammas separate owners,
registers `Empty` only on one, then inserts an independent concrete lower only
on the other. Distinct owners pass; coalescing fails. Source reachability of
that independent ingress was not derived, so this is not a source-program
counterexample.

A possible sufficient invariant is exact-image ownership: every gamma lower
comes only from its residual source decomposition; after source identification,
both decompositions receive complete current and future source histories; the
transport preserves attachment identity, operations, heads, filters and
outgoing right-context/tail edges. The source-to-`Row(heads,gamma)` relation
must also remain live so gamma upper constraints replay back into the source.
Capture/freshening must expose no independent gamma ingress or loss of reverse
feedback. This remains a proof obligation, not an input assumption for
implementation.

## 5. Source-reachability boundary

The following cases must not be conflated:

- The callback target's closed `[io]` annotation produces a paired
  `Stack(T, PUSH_i[{io}])` / `Filter(T,{io})` topology. The public closed Row
  view's residual tail is `Top`; this inspection found no two distinct
  live right-debt continuations there.
- A formal `[E; 't]` shares a named effect row but likewise produces a
  Stack/Filter pair. It does not itself construct a negative `Row({E},t)`.
- Oracle's generic negative Row consumer can create/reuse gamma for
  `Row({E},t)` and preserve distinct outgoing right debts. A source path that
  supplies both colliding demands and an independently admitted intact PUSH at
  gamma has not been found.

Therefore the shared-gamma collision remains a conditional generic Row-consumer
obligation, not a demonstrated callback-source failure. No global source
exclusion theorem was proved. Concrete formal-row implementation must not use
the conditional collision as a fabricated source restriction.

## 6. Required lifecycle if this carrier is selected

Before enabling explicit concrete formal rows, one reviewed implementation
contract must cover:

1. authentic annotation formation and attachment identity;
2. insertion/filter checks and future-lower registrations before self-omission;
3. contextual task, memo, bound, origin and replay identity;
4. Function argument `swap`, result preservation, and correlated `both` replay;
5. both residual directions: source-to-`Row(heads,gamma)` feedback and weighted
   gamma-to-tail projection with exact retained heads and outgoing contexts;
6. level-selected extrusion and operation-preserving view transport;
7. joint capture, freshening and independent use;
8. same-SCC parent/copy intrusion, including Cartesian replay of both sides;
9. atomic rollback of recipes, filters, bounds, watchers, origins and memo state;
10. an exact admission/observer argument for unbounded ordinary source classes.

Raw contextual-entry caps cannot be the whole admission design: the
independently source-reviewed [paired-ascription schemas](../progress/2026-10-10-recursive-push-source-invariant.md#independent-source-review)
admit unbounded one-ID left-PUSH contexts (see §1 and §§5–7, especially
§7's two corrected fixtures). The [exact symbolic observer](../progress/2026-10-10-recursive-push-observer-construction.md#1-result-and-exact-remaining-boundary)
is still an unreviewed mathematical reduction for that grammar interface; it
is not a reviewed general solution for mixed residual consumers. No numeric
cap, rejection behavior, or API error is selected here.

## 7. Open decision and review boundary

The next independent review must adjudicate whether to:

- retain separate residual lineages until an exact-image congruence is proved;
- canonicalize and merge equal-key residuals only with a source-ownership and
  complete-feedback theorem; or
- use another representation with the same exact future observations.

The result must state how it preserves every admitted source schema, soundness,
required principality, complete Call behavior and transaction rollback. Any
support-envelope change requires a separate explicit boundary and approval.
This draft introduces no implementation authority and closes no proof gate.

Evidence basis: bounded current-source reads and three unreviewed research
reports at this baseline. No source-level gamma collision was parsed or run;
no compiler code, tests, builds or measurements are claimed by this draft.
