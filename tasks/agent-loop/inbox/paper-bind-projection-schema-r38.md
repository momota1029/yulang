# R38 Luna candidate — let bind input projection schema

Sprint `PAPER-BIND-PROJECTION-SCHEMA-20261026/r38`, contract SHA-256
`69ae89735f471eb209058bff27fa77beb2e4011034e7f365c6cf8454919f9417`.
Baseline `8e255b775`; admission `e2e12255d`.
Outcome class: candidate source schema and falsifier; no theorem/source-native
closure or parent theorem is claimed.

## Candidate projection shape

For a full state whose active code label `ℓ` has ordinary bind form
`M bind x.N`, a projection to R36 would need to map the active child `M` to the
R36 head and the pending `N` body to the innermost let frame. Outer pending frames
then map in the same order to the rest of R36's stack. This is a candidate map,
not a defined manuscript transition. R36's actual `controlStep` focuses
`Computation.letE first body` as `head=first, stack=body::stack`; its `plug`
equality only establishes syntax erasure stutter.

The candidate full-state relation must carry the same typed derivation graph `G`,
the same joint assignment `η`, and the same port table `U` across this auxiliary
focus change. It must also map the parent active code label and current input
port to the newly focused child's code label and input port. Child membership
must be derived from existing full-state membership and a generated edge/transfer
closed under `F_G(U) ⊆ U`; membership cannot be included as a premise of the
projection relation.

## Source-grounded generated obligations

Manuscript `docs/yulang-operational-type-safety-ja.tex:1529` gives the bind-row
obligations: connect `M`'s result to `N`'s `x`; send requests from `M` and `N`
through the same outer request port in order; check `N` on every type-compatible
input diagram. The generation preface at `:1520–1523` says edges are finite
relation images and multiple input edges use all jointly consistent tuples.
The interface definition at `:1478–1485` gives each code node input, normal
result, outward event and latent ports; `η` is one joint assignment. The closure
at `:1544–1559` requires `F_G(U) ⊆ U` and every consistent joint `η`; it forbids
independent per-port assignments and arbitrary seed narrowing.

The bind row's explicit result-to-body input edge can support a later state when
`N` becomes active after `M` returns. It does not, in the inspected source, state
an edge or identity/restriction from the parent let-label's current input port to
`M`'s current input port. Nor does the full-state statement at `:1845–1858`
identify that label/port map: it requires current-interface membership and
active/saved frame derivations, but does not define the full state as a tuple or
spell out a let-focus transition. R36's `State` has no code label or port fields.

## Required derivation and finite discriminator

A complete projection schema would need an authorized generated relation
`R_bind-in : p_parent.in → p_M.in` (or an explicit identity/restriction rule
that makes these ports identical), with the actual transfer function on joint
diagrams. Then, from parent membership
`α_I(w, v, q) ∈ U(p_parent.in)`, the rule must produce the corresponding child
diagram and the Horn closure must place it in `U(p_M.in)` under the same `G,η,U`.
No such relation is stated in the inspected bind row or the full-state clauses.
I therefore do not assume it and do not claim child membership.

Falsifier for the candidate schema: take one parent input cell `p` and one child
input port `q`, set `U(p)={a}`, `U(q)=∅`, and let `G` contain no edge or Horn
rule from `p` to `q`. This can satisfy post-fixed closure for those ports, yet
parent membership does not imply child membership. Any schema that derives
`a∈U(q)` in this finite case without a generated connection has smuggled in the
missing premise. This is only a discriminator for the proposed schema, not a
counterexample to the manuscript theorem.

## First missing rule and owner

Luna's source/control lane owns the missing formalization: either cite an actual
source generation rule identifying the parent and active-child input interfaces,
including its joint-diagram transfer, or record that the manuscript has not
specified this mapping and obtain the decision from its authority owner. The
exact proposition cannot yet be sent to Lean without inventing that rule. The
next formal gate is: given the full-state relation, prove same `G`, same `η`,
same `U`, focus projection, and child membership from the named generated edge
plus Horn closure. Do not turn child membership into a relation field.

R36 `plug`/`erase` equality is insufficient for current-port inclusion. The
original one-step parent, other frames, full source/native, inference A/B and
production remain OPEN. No semantic choice, compiler edit, expected-output
change, test, fixture or diagnostic change is authorized. `NO_SAFE_CODE_SLICE`
after inspecting `PaperCoreControl.lean` and `PaperExecutionSyntax.lean`.

Frozen inputs rechecked:
- manuscript `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- R37 report `fed049b8a67f7c2a3919533ea4acf97ef3826d44715ccf2df5aaf3c6a1753b38`
- R36 source `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e`
- R36 contract `84c679419e1fd4cb75f4d16e2c2b9c537f0f10e5b29ac6d5fe885e697079bfe2`
- Paper syntax `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- R35 core step `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`

No checker/native commands, workers, descendants, tests, cache, or implementation
writes. R38 primary source construction finished within its 450-second share;
exact active seconds are not independently metered. The independent review share
remains capped at 150 seconds and must stop if its duration cannot be established.
