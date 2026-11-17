# Cycle 241: semantic quotient keys, read-only design review

## Scope and decision
Read I45–I47 in the current integration inbox, the source-initial predicate, allocation/capture/full-packet definitions, the 237 mass/readback results, 238 semantic congruence, and concrete regressions. No Lean implementation or existing-proof edit was made.

**Do not select (b) for immediate implementation on the evidence currently available.** Semantic identification can remove the specific 239/240 renaming loop, but neither a finite key universe nor a semantics-preserving allocator using it is established. It also does not resolve the independent compound-child endpoint obstruction. Prefer investigating (a)'s explicit source-projection/conservative-extension obligation first; this is not a claim that (a) is already correct. If that obligation fails too, report both gaps instead of choosing an unsupported implementation.

## 1. What “same meaning” must mean

Current `AggregateVersion231.version_eq_iff` identifies the *literal ordered list* of endpoint source pairs. A replacement cannot identify endpoints merely because one chosen model gives them the same type. For a fixed journal J, a minimally safe endpoint relation is:

- for every assignment satisfying full `Models J`, the two type components are mutually subtypes;
- row components are literally equal, as in `AssignmentCongruence238.Same` (a weaker row quotient would require additional proofs);
- preserve the distinction between input actual centers, lower/upper approximations, output binders, declaration, demand identity and allocation purpose.

For fixed declared consumers, lower/upper aggregate RHS expressions can be identified when their denotations are equivalent in **every** full model; an occurrencewise relation is stronger but easier to justify. Do not replace the whole key with just an aggregate type: registry/declaration/demand/purpose and actual-sharing provenance remain relevant. An unbounded list of equivalent repeated occurrences also needs either normalization or a proved arity bound; quotienting individual endpoint values alone does not make all lists finite.

The relation must be certified from pre-installation constraints. Deriving equality only after imposing the very alias/equation justified by that equality is circular. In an append-only journal, a proved universal equality persists along `step_models`, but equivalence classes can merge as models are removed. A stable representative scheme must preserve earlier certificates and earlier consumer references; recomputing a raw representative is not enough.

`SourceCongruence238.source_models_iff` is useful but insufficient: it transports assignments pointwise on the **same source-name domain and same fixed journal**, and requires source-reachable legacy emptiness. It is not a theorem identifying two names, changing allocation, rewriting a historical Plan, or preserving the existential projection to original source variables.

Required new contract: define a name map and assignment extension/restriction, prove forward and backward projected Models correspondence on original source/row identities, and commute all affected consumers (raw observations, capture merges, actual sharing, SchemaHolds, total emitted/default outputs, class effects and child requests). Fixed-plan congruence from 238 supplies ingredients, not the whole contract. An inconsistent journal must not become consistent by discarding its equations during canonicalization.

## 2. Finiteness does not follow from ground roots alone

`CenteredHeadMatStepBoundary.Initial` supplies ground root labels and coverage; it does not say every allocated or reserved endpoint has a fixed finite semantic value. In particular, privately named lower/upper approximations and emitted output expressions differ from actual ground centers.

`VersionedHeadMass237.schema_mass`, `WeightedHead237.head_weight`, `HeadReadback237` and `ChildLabels237` bound/read back **actual** head/capture/child meanings under their explicit Frame, packet Holds, coverage and input-label premises. They do not bound all lower/upper expressions, all rows, arbitrary cached approximations or the number of semantic equivalence classes of versions. Installation and refresh can expose inferred names not occurring literally in the original ground source.

A finite number of source names or constructors is not itself a finite semantic carrier: arbitrarily nested applications of a single variant constructor form an unbounded family of different finite type expressions. This is a counterexample to that *finiteness inference*, not a proved reachable execution of the current kernel. A root-label size bound could exclude such a family for actual children, but that exclusion must also be proved for every endpoint being used as a version key.

A possible sufficient theorem would provide a finite, source-dependent alphabet and depth/size bound for canonical endpoint expressions (including all generated output/row forms), or another explicit finite semantic abstract domain, and prove every reachable key lands in it. A mere abstract domain that collapses unequal types is not sufficient: either equality of abstract values must imply the full-model equivalence above, or the model/selection contract must be re-proved. No such theorem is currently available here. No semantic-normal-form decision procedure is supplied by the existing congruence lemmas.

## 3. What a valid termination measure would require

A plausible route is **finite obligation saturation**, not “number of current versions” alone:

1. Ground lineage and finite registry establish a finite universe of demand identities/actual shapes, including a bound on generated-child branching and depth.
2. A separate endpoint theorem establishes finitely many semantic keys per demand/declaration/purpose.
3. Construct a finite universe U of allowed allocation names, raw/center sites, edges, descriptor facts, equality facts, and semantically distinct installation obligations.
4. Show each allowed step adds a previously absent fact/obligation resolution in U, never losing previous progress. Then `|U minus recorded facts|` decreases, or use a lexicographic/multiset measure with a proved dependency rank.

Every item is essential. Existing `Committed` depends on full packet meaning and current class effects; treating it as a permanently monotone Boolean without a proof is unsafe. Plan records contain entire contexts, while allocation/reservation lists can carry duplicates: a finite key set does not directly imply finitely many literal Plan values. One must quotient irrelevant bookkeeping or prove repeated equivalent plans are already Committed. A finite number of observable quotient states also does not exclude an infinite execution consisting of zero-progress concrete steps; each allowed concrete step needs strict progress.

I45 should remain during this investigation. It already proves useful point-record persistence and restricts unnecessary retargeting. With a genuinely finite universe of relevant slots, each Reobserve's newly-point slot could contribute strict progress. Cycle240 demonstrates why that argument fails until the slot universe itself is bounded. Removing I45 is not needed to test (b) and would reopen 239's exact loop.

## 4. Regression expectations and obligations

| Regression | Required outcome under any replacement |
| --- | --- |
| 199 | Keep the real rejection/conflict; equal-name normalization must not erase the conflicting output constraints. Existing mixed/versioned regression remains the comparison baseline. |
| 202 | Keep default-derived dictionary evidence. Its empty capture bindings make aggregate-key changes largely irrelevant, but total default interpretation must remain. |
| 204 | Keep total join-expression evidence, not the old partial syntactic output test. The relevant terminal regression also has empty bindings. |
| 206 | Preserve the actual install/equate/refresh route, retained model, and removal of the bottom countermodel by the default output equation. Canonicalization must not weaken that equation. |
| 218 | Preserve actual sharing equations and the old generated child's rejection; preserve the finite-equality stable endpoint and EvidenceAt. Similar interval approximations are not permission to identify unequal actual arguments (Int versus Bool payloads). |
| 230 | Preserve the genuine V-to-W refinement and subsequent installation/evidence. These are not equivalent endpoint types and must stay distinguishable. Reusing one persistent aggregate equation without changing its ownership would restore the old collision. |
| 239 | Equivalent F-valued aliases should get the same semantic key. I45 already blocks its point-retarget step, but the allocator must not manufacture a fresh name for identical certified meaning. |
| 240 | Root remains structurally nonpoint while all successive lower aliases mean F. Quotienting those aliases should stop the exhibited fresh-name loop; this is only one regression, not the finite-universe theorem. |

Additional necessary regression: **Compound238/239/240**. It is still source-reachable under I45 and has nonempty Models plus no simultaneous current full packet model; EvidenceAt is true by the failed child premise. The old lower aggregate means V, the current one W, and these are genuinely different. A semantic quotient must not merge them. Their legacy compound child endpoints (purposes 3/4) nevertheless remain fixed and receive incompatible total output equations. Consequently semantic version normalization by itself does not fix this obstruction. It is not an EvidenceNode refutation, but any design claiming general current-packet completion must confront it explicitly rather than silently dropping outputs.

## 5. Concrete gates before choosing (b)

- Specify whether equivalence is model-independent expression equality or current-journal universal equivalence, and give a noncircular way to certify it.
- Prove original-source projected Models correspondence for aliasing/canonical naming, not just fixed-assignment congruence.
- Prove a finite endpoint-key universe covering inferred/generated lower, upper and output/row terms; distinguish this from actual child mass.
- Prove every concrete step makes strict progress in that finite universe, including reinstall, context bookkeeping and changing class effects.
- Retain all eight named regressions and the compound obstruction as explicit design tests.

Without these gates, a quotient key is a useful local optimization hypothesis, not a justified replacement boundary or stopping proof.
