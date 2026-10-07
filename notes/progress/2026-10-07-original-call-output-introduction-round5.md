# Original Call output introduction, round 5

Date: 2026-10-07
Baseline: `cb789e453a080d751f9689918f94974283be7302`
Status: bounded constructive, adversarial and source-correspondence attack
Gate: ORIGINAL_ASSOC O0, ahead of O1
Semantic and implementation authority: none

## Starting point

The latest remote branch began with 90 DAG nodes / 196 edges: 7 CLOSED,
20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC,
1 IMPLEMENTATION-ONLY and 0 BLOCKED. The previous round's next proof cut was
an original-sort `TypedOutputCorrespondence` for the captured Call `f x`.
This pass attacked that cut directly without revisiting S1, K-Owner pair
models, or the immediate-versus-latent selector discriminator.

## Constructive cut

The Authoritative Function-view design requires typed paths to originate
from source resolution and typed elaboration, independent of pending
comparison `Q`, and explicitly leaves the exact construction open. For this
fixed source Call, the reviewed non-authoritative Gen-Call-0 construction
§4.2 and the canonical ORIGINAL_ASSOC node locate the candidate port at the
immediate complete-invocation output of the shared Function contract. Those
sources do not state the original-sort constructor that inhabits the
correspondence.

Use the following names only as a proposed notation for that missing clause:

```text
ResolvedOriginalCall(X,c,u_f,u_x,d_f; sigma_step)
SharedRootOriginal(X,d_f,R_f; sigma_apply)
CapturedRootTransportOriginal(d_f,R_f,sigma_apply,sigma_step; xi)
GeneratedUpperUse(c,u_f,R_f,U_c := F_c,beta,p0,ElimOrigin)
OriginalFunctionSignatureFormation(U_c; original scope,xi)
---------------------------------------------------------------- OC-Output-Intro [candidate]
exists kappa.
  kappa : TypedOutputCorrespondence(
    U_c,outEff(U_c),p0; original scope,xi)
```

For this call, the generated schema fixes `beta=(d_f,R_f)` and
`p0=(beta,call.effect)` and retains the map from that immediate signature port
to `p_out(c)`. Capture transport keeps `sigma_apply` and `sigma_step` distinct.
The conclusion is a static original typed map at the same `X,xi` and scopes;
it does not identify endpoint representations or assert runtime receipt,
source acceptance, `Own_orig`, a complete slot inventory, Call membership or
successful `Q`.

This is a candidate rule head, **not a proved theorem or adopted semantic
rule**. Its exact unproved point is whether independent original
Function-signature interpretation plus the generated source-elimination
schema suffices to construct the original-sort map. The present source-call
schema, conditional decorated observation-port result and typed-core
Call/Normalize skeleton do not instantiate that conclusion. Making
`TypedOutputCorrespondence` itself a premise would simply assume O0.

The proposed O0 head need not consume an execution world or the full Call
development: that would add the separately tracked CALL_TYPE/C0/C1/J0 proof
obligations to a static port map. Conversely, the bounded constructive report
also gave a sufficient route conditional on complete Call typing and all
joint local laws; it does not show those heavier premises are minimal.
Authority locators: [Function-view design §2](../design/2026-10-05-inferred-function-call-views.md);
[source-call construction §4.2](2026-10-06-source-call-generation-construction.md);
[canonical ORIGINAL_ASSOC](../theory/successor-proof-obligations.md#original-assoc).

## Adversarial result

At a fixed resolved Call, original scope, `xi`, upper interface and immediate
port, I examined whether multiple proof labels for the same checking
proposition yield a competing map. Under the inspected typed-core
construction, these labels leave the same structural Call skeleton. This
bounded observation does **not** prove equality of complete evidence,
residual behavior or principal solutions, so it is not an equivalence theorem
or countermodel. Varying satisfying endpoint values changes the fixed
assignment or demanded interface. Varying the actual provider changes the
admitted filling, not the meaning of that filling. Request origins, response
ports, current state, delimiters and pending continuations constrain attempts
to redirect the same execution to a different source phase; no complete
alternative preserving all supplied typed premises was constructed.

No complete pair of Authority-consistent output-map semantics with different
observable or principal outcomes was constructed. Thus the strict user-
decision criterion is not met. The absence of the original-sort introduction
rule does not by itself imply semantic nonuniqueness.

## Current compiler correspondence

The current default-off path retains the source Apply occurrence, HIR/Core
identity, pending structural addresses, direct Name operand joins and the
unresolved solve row. It does not allocate a typed Call Function demand,
`p0`, `p_out(c)`, or an original output map. The existing structural labels
already distinguish candidate Function return effect from whole-Apply effect;
adding another identity sidecar would duplicate current evidence rather than
advance O0. A real map requires the missing original typed Call-elaboration
producer, not additional current-solver bookkeeping.

The Frozen Oracle record remains historical mechanism evidence only. Its
header/formal/name/application/frame mechanisms do not interpret the current
original Function signature or supply this source rule; this pass did not
query or execute Oracle code.

## Before / after and remaining clauses

| Gate | Before | After | Result |
|---|---|---|---|
| CALL_TYPE | CONDITIONAL-CLOSED | CONDITIONAL-CLOSED | No existing joint constructor law was instantiated. |
| ORIGINAL_ASSOC | OPEN-SEMANTIC | OPEN-SEMANTIC | O0 still precedes O1; no source-owned original fiber was introduced. |
| DAG counts | 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC, 1 IMPLEMENTATION-ONLY | unchanged | No node or edge promotion. |

No new semantic clause is proven. The next smallest proof target is
`OC-Output-Intro`'s original-signature-to-output-map step at the fixed Call,
including a derivation that does not use the conclusion in its premises. If
that rule is introduced under the repository's approval process, O1 must
still separately produce `Slots_orig` / `Own_orig`; contribution typing,
uniform-family assembly, attachment/licensing, profile and independent
admission remain downstream.

Production cutover remains blocked by this original Call producer and the
other OPEN proof/semantic nodes, source adequacy and production conformance.
The default-off crosswalk remains structural only.

## Review and verification

Constructive derivation, same-port adversarial analysis, architectural rule
interface review and current compiler producer tracing were performed as
separate read-only assignments. The candidate rule signature is not
adopted. Independent compiler-referee and spec-auditor reviews passed after
minor repairs that bounded the proof-label observation and attributed the
candidate immediate port to the reviewed non-authoritative Gen-Call-0 source,
not the Authority that leaves exact construction open. No repository path
changed in the producer assignments; no tests, builds, probes, performance
measurements, Oracle execution or Git mutation occurred.

Next: independently review the exact `OC-Output-Intro` premise independence,
static scope and port conformance. Do not update DAG status unless its original
typed interpretation is actually derived.
