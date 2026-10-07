# Theorem C cannot introduce the original Call output map, round 6

Date: 2026-10-07
Baseline: `d8ddbb0a3a3ab80b7cca67de09a8310617ba1170`
Status: bounded specialization and last-rule inversion; no semantic or implementation authority
Gate: ORIGINAL_ASSOC O0

## Starting point

The canonical successor DAG at the latest remote HEAD contained 90 nodes and
196 edges: 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF,
19 OPEN-SEMANTIC, 1 IMPLEMENTATION-ONLY and 0 BLOCKED. The preceding O0 attack
isolated the original-sort `TypedOutputCorrespondence` for the captured Call
`f x` as the smallest missing constructor. This round asked whether Theorem C
and the source-indexed realization theorem can construct that correspondence
from their existing source inputs.

## Specialization and last-rule result

Specializing the reference Call constructor to the inner `f x` Call builds an
invocation relation at supplied typed coordinates. Realization then transports
finite derivations between the reference and generated semantics, preserving
the original source links, scopes and shared `xi`. This establishes endpoint
agreement inside the theorem's supplied decoration envelope.

The envelope is decisive. Source-indexed realization §2 requires independently
supplied typed paths and owner/view inputs. Source-generated callback theorems
§2.6 require the complete typed views and static path maps to already occur in
the source instruction schema. The Call constructor constructs invocation
behavior, while realization transports derivations over those inputs. Neither
introduces an original Function-signature interpretation or a typed map from
its immediate complete-invocation output to the original upper-use map.

The last-rule inversion has this form:

```text
Obar ∈ P_ref(e,h;xi)
  ⇒ exists w. Der_ref(e,h;xi,w) ∧ Obar = Pi_xi(Obs(w))

last constructor = Call
  ⇒ callee and inert whole argument,
     actual receiver/receipt, provider entry/body/consumer,
     invocation return and joint source links are retained
```

It recovers the same supplied Call witnesses; it does not produce a new
original-sort upper-output correspondence. If the required correspondence is
inside the typed decoration, extracting it assumes O0. If that correspondence
is withheld, reference/generated realization has no rule to introduce it.
Adding a fresh projection coordinate does not bridge the gap: projections
preserve a well-formed tuple's fixed endpoints, and certifying the new point as
the original `p0` still requires the missing original typing/commuting proof.

The exact unproved constructor remains:

```text
original Function-signature formation
+ resolved shared-root/capture/Call-elimination evidence
---------------------------------------------------------------- [missing]
TypedOutputCorrespondence_orig(
  U_c, outEff(U_c), p0; original scope,xi)
```

The smallest cut retains the resolved inner Call, both normalized Name
children, capture and signature data, and all other granted decorations, while
withholding only this original typed correspondence. This is a precise
limitation of the realization route, not a proof that no other source producer
exists.

## Status and decision discipline

No complete alternate Authority-consistent semantics with differing observable
or principal outcomes was constructed. No admitted-source counterexample or
new semantic clause was found. The user-decision criterion is not met. No DAG
node or edge is promoted; `ORIGINAL_ASSOC` remains OPEN-SEMANTIC and all
downstream statuses remain unchanged.

| Gate | Before | After | Result |
|---|---|---|---|
| ORIGINAL_ASSOC O0 | OPEN-SEMANTIC | OPEN-SEMANTIC | Theorem C preserves supplied typed maps but does not introduce one. |
| DAG counts | 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC, 1 IMPLEMENTATION-ONLY | unchanged | No closure or new edge. |

The next attack should inspect the owning original Function-signature
interpretation/elimination producer for a commuting map at this fixed Call.
Another reference-bound transport wrapper would leave the same premise open.

## Scope and checks

Two independent read-only research assignments specialized and inverted the
Theorem C route. They inspected source/design sections and the pinned baseline;
they ran no tests, builds, executable probes or Oracle code, and changed no
files. This note reports the bounded route only and claims no implementation,
performance, source-adequacy or production-conformance result.
