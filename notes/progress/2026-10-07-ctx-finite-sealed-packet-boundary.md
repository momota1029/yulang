# CTX_FINITE: bounded open-endpoint restriction and sealed-packet boundary

Date: 2026-10-07
Baseline: `1356eccdf8654e500f772a881bdc5eec624dbe4e`
Status: conditional relational derivation and reviewed boundary characterization
Authority: none; CTX_FINITE remains OPEN-PROOF
Independent review: conditional pass; a global-ordering overclaim was corrected

## Result

For the finite acyclic, unsealed endpoint trace specified below, outward
permission restriction has a finite relational-algebra representation. This
does not establish that source generation uses this trace, preserve every
source rule, or close CTX_FINITE.

Let `Reach(u,y)` mean that endpoint `y` is reachable from outward endpoint `u`
through the fixed finite dependency graph, including reflexivity. Let
`Visible(d,k)` mean opening identity `k` is visible at destination `d`, using
the original destination ownership and opening-block identities. Then the
permission update is:

```text
Bad(y,k) = Reach(u,y) ∧ ¬Visible(d,k)
Allow'   = Allow \ Bad
```

On a fixed finite acyclic graph, `Reach` is a finite union of relational
compositions (with identity); joins, projection and difference construct
`Bad` and `Allow'` from the supplied static ports. Numeric lexical depth alone
does not encode `Visible` when sibling openings have distinct identities.

The preservation/termination implication is conditional on finite
preallocated endpoints and openings, ownership-preserving lookup/capture,
exhaustive restriction through existing bindings, immediate dependency checks,
finite decreasing permission/binding updates, and fair rechecking. The
operation-instance package §8 supplies these as premises for its restricted
unsealed fragment. Neither finite relational representation nor finite
carrier proves those premises for source generation.

## Sealed packet cut

In the chosen packet-bearing lifecycle trace, §8's unsealed restriction does
not cover transporting/opening a sealed existential packet whose payload
contains local dependent binders and witnesses. A candidate transport must
keep one capture-avoiding map for the whole interface and preserve each
original witness, provider, scope, `K,D` dependency and raw continuation.
Applying outward restriction as if a bound dependency were a free escaping
dependency would change the packet's meaning.

The operation-instance package §7 leaves the result/store lifecycle theorem
open. The minimum missing interface for this trace is:

```text
Input:
  original typed result/store root;
  complete incident binder, witness, provider, K,D and suffix graph;
  original source boundary, destination scope and shared xi.

Output obligation:
  source-justified scoped target interface and bound-capture map;
  pack / transport / read / open correspondence for that interface;
  preservation of every original witness and provider dependency;
  exact checking-assumption visibility and guard/invalidation dependencies.
```

This is an obligation signature, not an adopted semantic rule. It does not
derive Generalize eligibility. The certified-use joint-hiding theorem consumes
eligibility as an input.

The reviewer confirmed the finite relational representation conditionally and
corrected a potential overclaim: sealed transport is the next uncovered
operation in this selected trace, not a globally ordered or sole remaining
CTX_FINITE obligation. The canonical gate still separately requires an
inventory of actual child-context operations and identity observers, semantic
guard preservation, and monotone update/termination evidence. Other uncovered
operations include subtype/bound replay, fresh instance generation and
evidence preservation.

## Disposition

| Attack | Before | After | Result |
|---|---|---|---|
| Fixed finite unsealed restriction trace | OPEN-PROOF | OPEN-PROOF | Conditional representation derived and independently reviewed; source premises remain assumed. |
| Sealed result/store packet lifecycle | OPEN-PROOF | OPEN-PROOF | Exact trace-local missing interface identified; not a counterexample and no source rule adopted. |
| Whole CTX_FINITE | OPEN-PROOF | OPEN-PROOF | No node closure or status-count reduction. |

The minimum next attack is to derive the result-boundary capture/interface
from an actual source producer, then prove the pack/open relation preserves
the same original witnesses and invalidation obligations. Keep the other
CTX_FINITE inventory and termination leaves active; do not call this the
global first missing operation.

## Sources and checks

- `notes/design/2026-10-03-source-context-finite-closure.md` §§1–6.
- `notes/design/2026-10-02-operation-instance-binding-package.md` §§7–8,
  especially the explicit exclusions of sealed lifecycle transport.
- `notes/design/2026-10-04-certified-callback-and-constrained-use.md` §2.
- `notes/progress/2026-10-07-successor-effective-projection-round2.md` §1.
- Canonical DAG `CTX_FINITE` at the stated baseline.

The derivation and review were read-only; no tests, builds, executable probes,
Oracle calls or Git mutations were used. No seed search or performance
measurement was run. This note changes neither source semantics nor code.
