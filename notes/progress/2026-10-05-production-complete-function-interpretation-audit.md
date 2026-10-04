# Production complete-Function interpretation: direct main-gate audit

Date: 2026-10-05
Status: direct proof-gate audit; no theorem, semantic selection, carrier, or implementation authority
Scope: determine whether the current production endpoint and approved source contracts define the sets in the callback containment theorem
Branch: `research/simple-sub-intrusion`
Reviewed-by: compiler_referee and spec_auditor; bounded semantic and authority reviews closed with no remaining findings

## Target

The production callback theorem requires, at one fixed
`xi = (nu,K,D)`, an independently defined challenge domain and complete
observation relation for both bounds:

```text
D_C(xi) subseteq D_A(xi)
forall c in D_C(xi): P_A(c;xi) subseteq P_C(c;xi)
```

The production bound is allowed to contain endpoint-compatible observations
without source-constructor witnesses under approved Option 2. The option does
not make every port-compatible continuation or origin a member. This audit
attacks the main theorem's semantic domain directly; it does not add another
finite containment lemma.

## Source-to-production crosswalk

| Required interpretation | Governing evidence | What remains absent |
|---|---|---|
| Callback literal role and reference ordering | Authoritative callback-context design §§2–2.1: expected boundary selects Handler before body constraints; endpoints are synthesized independently; one `F_lit <: F_cb` closes the literal check. | `ResolvedExpr` has no function-application variant, and current resolved-HIR lowering has no inline-lambda-in-application path to generate that derivation. This contract fixes scheduling, not complete Function membership. |
| Source relation and reference callback bounds | Theorem C and the source-indexed realization define a finite source-generated relation, independent admission, and a checked lift preserving old tuples. | This is `P_ref`; it does not define current production `P_A` or permit treating source generation as exhaustive production membership. |
| Conservative production extras | Approved Option 2 allows extras. The conditional source-contract package §3.7 gives a sufficient grammar `H_G(R)` with whole-tuple `W`/`Z` abstractions, a complete guard `G`, paired transport, and independent admission. | `W`, `Z`, `G`, active descriptor membership, and the exact extra alternatives are explicitly unselected. The conditional theorem does not select them for F5. |
| Actual current Function owner | `LambdaRecipe` retains source positions; `admit_lambda_fact` emits a linked positive Function fact; `SemanticFact` retains lower/upper terms; provenance edges connect recorded causes to facts. | These records do not define `A_A(c)` or `M_A(c,O,w)` over complete typed observations, nor the independent `DescMem` judgment used by the conditional package. |
| Complete endpoint | `TermView` retains the four Function children; F5 generalization has a narrow pure-effect check over the existing polarized effect bounds. | Four endpoints and their constraints do not encode an exhaustive rule for histories, origins, continuation/future-use admission, or handler authority. No production source-to-complete-observation membership rule is present. |
| Challenge domain | The source packages describe punctured source contexts, requests/responses, resumptions, and future use; Theorem C keeps admission independent of inequality success. | Current `ResolvedExpr` has no function-application node and does not generate these complete application histories. Lower-level `HirExpr::Apply` represents dynamic operator association; it is not the missing resolved Function-application node. Retained source provenance does not independently define the complete production challenge domain. |

The F5 facts above are implementation characterization only. They neither
define successor Function-port subtyping nor imply that a new carrier is
needed. Frozen Oracle `StackWeight`, `SubtractId`, `AllExcept`, and left/right
routing likewise do not fill the gap: the SCC charter treats them as
characterization evidence, and they do not independently denote complete
source observations.

## Main-gate result

The containment statement cannot yet be evaluated for production because
`D_A`, `P_A`, and the corresponding checked membership predicates have no
exhaustive, query-independent production interpretation in the selected
contracts. The conditional package states exactly the needed interface:

```text
A_A(h;xi)                         challenge admission
M_A(h,O,w;xi) and DescMem(...)    complete observation membership
```

At fixed original scopes and the same full `(nu,K,D)` fiber, the interpretation
must account for the actual complete descriptor, every retained constraint,
authority and dependency, and every conservative extra. `DescMem` cannot be
defined as the source image because Option 2 allows non-source-witnessed
members; nor can it be reduced to four-port shape because that drops the
complete-observation and authority conditions. Admission cannot be inferred
from comparison success.

This is one missing premise: **an exhaustive, comparison-independent
interpretation of complete production Function membership and admission**.
It subsumes the exact `W`/`Z` grammar and active descriptor-membership rule if
the selected interpretation uses the conditional package's abstraction
presentation. Once that premise is supplied, source-generation conformance,
actual-to-checked containment, and the unrestricted principal-scheme gates
remain separate proof obligations.

No source counterexample to the intended schemes or accepted Option 2 policy
was found. No concrete fact proves existing `Rel_C`, `K,D`, paths,
occurrence/incidence, and subtraction evidence insufficient. Thus this audit
does not justify adding a carrier or selecting `W`/`Z`; it localizes the
unresolved production interpretation without promoting a conditional
candidate to semantics.

## Next decision boundary

The remaining design alternatives are not equivalent:

1. derive the complete production interpretation from existing source rules
   plus explicitly licensed local abstraction operations, with an exhaustive
   member/admission grammar; or
2. define a distinct conservative Function-bound abstraction over complete
   typed observations, including its lawful extra-membership rules and its
   relation to the existing evidence.

Both must preserve original role/entry, typed paths, source origins,
continuations, `nu,K,D`, binder scopes, and comparison-independent admission.
Neither is selected by this audit. A proposal that merely assumes the
membership contract or tests endpoint shape is circular with the theorem.
Production implementation remains gated.

## Verification scope

Primary reread of the bounded callback source contract, production endpoint
draft §4, the conditional source-contract package §§2.2, 3.7, 5.1–5.3, 7, and
10, plus the current HIR and solver owners. No tests, builds, measurements, or
production changes were made. Independent semantic and exact-authority review
closed after one minor HIR-owner wording correction; the repaired wording was
delta-reviewed.
