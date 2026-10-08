# Source-owned comparison action: candidate constructor

Date: 2026-10-08
Status: Draft; no implementation authority
Scope: same-value comparisons used to transport Function readouts during source closure introduction
Baseline: `916eb7eaaecbae6ca58544e4f803b2a67e6dad19`
Drafted-by: primary
Reviewed-by: compiler-referee and spec-auditor; draft-scope review only
Supersedes: none

## 1. Decision to resolve

The selected semantic meaning of ordinary `VIncl(A,B)` is pointwise inclusion
in the final interpretation `M = nu Phi`. It acts on an ordinary certificate
`M.V(A,v)` and yields `M.V(B,v)` for the same value and dependent tuple. It
does not, by itself, act on an arbitrary one-step constructor readout
`Phi(Z).V(A,v)` for another positive background `Z`.

That distinction blocks the outer `apply` constructor when an admitted carrier
returns a callable whose input and call-site descriptors differ. The selected
captured `step` proof obtains an ordinary `A_f` certificate, applies ordinary
VIncl, unfolds the result at `F_c`, and only then maps positive fields into a
relative background. A relative carrier Return yields only the relative
`A_f` field. A coincident `f = apply` value at `A_f = F_apply` cannot be
discharged by choosing the apply-hole branch as a non-hole `Phi` readout.

The candidate below targets the non-hole transport part of this proof
obligation by attaching construction evidence to a source-owned comparison.
It does not change
ordinary VIncl's final-model meaning, restrict the independently fixed
challenge domain, choose a provider from a printed type, or decide
generalization/export behavior. This is a proposed architecture decision;
implementation remains gated on review and explicit user approval.

## 2. Proposed comparison evidence

For a source-owned comparison from actual value endpoint `A` to checked
endpoint `B`, retain a finite, typed derivation `Cmp(A,B)` at the original
source occurrence, shared assignment, scope, and joint incidence. A final-
model VIncl result or successful query is not this derivation. Its
interpretation has two results:

1. The existing final-model proposition `M.V(A,v) -> M.V(B,v)` for the same
   actual value, provider decomposition, roots, and dependent evidence.
2. A one-step action for every relation-family tuple `Z` over the selected
   fixed sorts and independent index domains, with the non-hereditary
   parameters of `Phi` held fixed:

   ```text
   Phi(Z).V(A,v,r,e) -> Phi(Z).V(B,v,r,e)
   ```

   Here `Z` is arbitrary at hereditary fields; it need not be a fixed point
   or already satisfy VIncl. The action retains the complete independently
   fixed challenge domains, current event, whole carrier, guards, operation
   witnesses, response/raw handles, future-use restrictions, and original
   provider maps.

`Cmp` is proof evidence for an already generated source relation. It is not a
runtime object, a user annotation, a second type meaning, a successful-query
receipt, or a license to infer the comparison from the value's identity.
Evidence construction belongs to the phase that owns the comparison. Later
phases consume or transport that evidence; they do not reconstruct it from
endpoint syntax or solver success.

### 2.1 Callable constructor

For complete callable endpoints, a `Cmp(A,B)` constructor must retain at
least:

- actual role, entry, consumer, provider/capture and scope correspondence;
- a whole-challenge map from every independently admitted `B` challenge to
  the identical original `A` challenge, including the whole carrier and all
  correlated coordinates;
- a uniform observation/future map from every `P_A[Z]` field to its matching
  `P_B[Z]` field for arbitrary `Z`, with the same output-dependent provider;
- preservation or construction of every target immediate guard, profile,
  license, path, receipt, authority, and incidence condition;
- the actual same-value operand and complete whole-carrier checking evidence
  at their original source ports.

The callable action preserves the actual decomposition of the value. It may
not select a different provider after a result, drop an admitted challenge,
or project away a coordinate that the source contract keeps correlated.

### 2.2 Other constructors and alternatives

The evidence grammar must cover every constructor admitted by the selected
source descriptor grammar. For a union or other multi-alternative source
endpoint, it must account for every alternative that the original membership
clause requires. A convenient callable branch cannot stand in for the other
branches. `W`, `Z`, opaque, recursive, scoped, renamed, and imported clauses
keep their own original contracts and maps; no structural source execution or
new license is invented for them.

Recursive evidence may be represented as a finite DAG only when its
constructors establish the corresponding whole-interface action, including
every recursive endpoint transport used at a `Z`-indexed field. Cycles,
guards, and dependent maps stay explicit. Endpoint identity and successful
query results are not substitutes for a derivation.

### 2.3 Why final VIncl cannot construct `Cmp`

Let complete callable interfaces `A` and `B` have the same independent
challenge domains, actual provider, guards, worlds, and phases. Let their
result clauses be `PureReturn(C)` and `PureReturn(D)`, where the fixed final
interpretation gives the same returned values at `C` and `D`. The complete
final-model comparison can then hold. Choose a relation tuple `Z` whose value
field contains the returned tuple at `C` and omits it at `D`, leaving other
sorts and independent domains unchanged. The selected one-step PureReturn
clauses require `Z.V(C,v)` and `Z.V(D,v)` respectively. Thus an `A` readout
exists at this `Z`, while the corresponding `B` readout does not.

This is an abstract countermodel to deriving arbitrary-`Z` action from
ordinary final-model VIncl; it is not a source-admitted Yulang program or a
counterexample to the selected semantics. It shows that `Cmp` needs
additional constructor evidence for every endpoint-changing hereditary
field. No selected source rule currently supplies that evidence.

## 3. Constructor theorem and proof route

**Proposed theorem `Cmp-Action`.** For every finite `Cmp(A,B)` derivation,
the same actual value's one-step `A` readout maps to its one-step `B` readout
for every `Z` and every unchanged independent complete challenge. The
derivation also implies the existing final-model VIncl proposition.

For a callable comparison, unfold `Phi(Z).V(A,v)` at its actual provider.
Map each `B` challenge through the retained whole-domain action to the
identical `A` challenge. Use the `A` readout's actual-provider admission and
complete observation/future fields, then apply the retained whole-field maps
and target guard/incidence evidence. The resulting tuple is a `Phi(Z).V(B,v)`
readout. No membership premise is selected by successful query or by the
desired result. The final-model proposition follows by applying the same
constructor action at `Z=M`.

Applied to outer `apply`, a complete `Cmp(A_f,F_c)` action would let a
non-hole relative carrier Return at `A_f` supply the actual `F_c` readout. An
exact `apply` hole at a different `F_c` still requires a simultaneous
postfixed construction; the comparison action cannot convert a hole
assumption into a `Phi` readout. A coincident native apply call can use a
constructed apply front, but this alone does not close the universal outer
domain: every other admitted Return needs its own ordinary or certified input
path.

## 4. Ownership and lifecycle candidate

The source Call comparison owner forms `Cmp(A_f,F_c)` alongside the original
whole-comparison obligation, before closure introduction. The actual
same-value operand origin, complete carrier check, provider/entry relation,
scope, and original shared `nu,K,D` remain attached to that exact source
occurrence. The resolver validates the complete derivation and returns it as
an owned typed result; a boolean success flag is insufficient.

Closure introduction consumes the certificate for relative readouts. Module
generalization, SCC packing, and fresh use must transport the whole evidence
package with the same scope and covariance as the relation it proves. Every
member remains private until complete component validation; no partial
comparison or interface becomes public. This section identifies consumers,
not a selected export-root or publication policy.

The evidence is compile-time state. It does not alter runtime closure layout
or dispatch. Its resource costs still require accounting: DAG nodes and edge
incidences, binder/dependency payload, union width, recursive cycles,
per-use freshening, retained component bytes, and proof construction work.
No numeric cap, cache strategy, asymptotic claim, or supported-input boundary
is selected here.

## 5. Required evidence and falsifiers

Before this candidate can be selected or implemented, a proof and producer
must establish all of the following:

1. Every accepted source comparison in the approved envelope has an owning
   finite `Cmp` derivation, or a proved equivalent construction.
2. Every derivation constructor preserves the same complete challenge,
   actual provider, all live-event guards, every output/future coordinate,
   and every independently licensed alternative.
3. The action holds for arbitrary positive `Z`, including cyclic recursive
   descriptors, without assuming membership in the target endpoint.
4. Fresh use and SCC generalization preserve original scopes, fixed imports,
   jointly scoped evidence, and independent per-use identities.
5. Failed or incomplete construction remains private and cannot publish a
   partial callable interface.
6. Construction and transport costs are measured or structurally bounded
   under the selected performance gate; proof hits alone do not establish
   saved work or bounded output.

Reject the candidate if any proof requires narrowing the independent
compatible-context domain, dropping a `W`/`Z`/opaque alternative, identifying
values solely by endpoint spelling, assuming the target readout, or requiring
ordinary input membership that the challenge definition does not provide.
Also reject it if the existing source owner cannot construct the evidence
without a completeness loss for ordinary accepted programs.

The evidence does not itself prove source adequacy, resolver completeness,
principality, the selected Generalize/export root, complete production
membership, resource safety, or F5 replacement. Those remain their own gates.

## 6. Alternatives and decision requested

| Option | Consequence |
|---|---|
| **Select construction evidence (conditionally preferred)** | Keep VIncl's ordinary meaning and retain a canonical typed comparison proof at its source owner. The proof-economy rule prefers this only if the owner already knows the required endpoint actions and retention preserves approved behavior. Neither condition is established yet. Requires a new evidence output and lifecycle transport, with independent semantic, specification, and resource review before implementation. |
| **Keep only final-model VIncl** | Preserve the current source relation surface. Relative closure proofs must obtain ordinary hereditary input certificates independently or remain open; no target readout may be inferred from relative `A_f` membership. This does not complete the current outer `apply` proof. |

The first option is a construction/lifecycle choice, not approval to change
observable type behavior. It still requires proof that the evidence producer
is complete for approved ordinary programs. Approval of this candidate would
not approve implementation, a performance bound, a Generalize/export policy,
or production cutover; those gates remain separate.

## 7. Current evidence boundary

The existing [call input theorem](../theory/2026-10-08-call-semantic-input-realization.md)
§§3.2, 5, [captured closure theorem](../theory/2026-10-08-captured-call-closure-introduction.md)
§6, and [outer apply theorem](../theory/2026-10-08-outer-apply-closure-introduction.md)
§§3–6 supply the final-model inclusion, ordinary-input closure proof, and the
exact relative-transfer residual. Fresh read-only research at baseline
`916eb7eaa` confirms that selected source-owned VIncl and
WholeArgCompatible clauses do not supply an arbitrary-background action.
The exact apply/apply descriptor coincidence admits a staged intermediate
front, but it does not make the full universal outer domain postfixed while
other admitted carrier Returns remain open.

No selected rule currently supplies a complete `Cmp` grammar, arbitrary-Z
action, or source/solver completeness theorem. Current ordinary collection
classifies Apply/Group bodies as errors in `crates/yu-solver/src/lib.rs`
around `collect_mode`/`collect_expr`; the experimental Apply collector in
`crates/yu-solver/src/shadow_apply.rs` builds a polarized four-port demand but
leaves complete invocation, source typing, admission, and whole-tuple
semantics unresolved. Its typed pair memo retains diagnostic value children
and an effect marker, not the proposed complete action certificate. Thus
producer completeness is a concrete production gap, not an established
existing implementation feature.

The candidate is therefore a Draft decision packet only. No source behavior,
design authority, canonical DAG status, implementation, or cutover is
changed.

Review record: the spec-auditor found no authority or scope contradiction,
but blocked selection/implementation on the unproved complete producer and
action package. Its minor proof-economy wording finding was repaired. The
compiler-referee's initial major finding on arbitrary-background scope and
hole coverage was repaired and passed delta review. These reviews certify
neither producer completeness nor the proposed architecture; the selection
gate remains open.
