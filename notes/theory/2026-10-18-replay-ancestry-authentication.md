# Authentication of one source-to-Replay demand ancestry

Status: frozen conditional proof candidate; independent review NOT RUN.
Author `/root/replay_ancestry_proof`; descendants 0; requested Sol/high,
observed model/effort UNKNOWN/UNKNOWN. Assignment
`NPAIR-REPLAY-ANCESTRY-PROOF-20261018`, sprint
`npair-replay-ancestry-authentication-20261018` rev1, contract SHA-256
`23181fbb4511e1cc7c36fa3f28bfd6996027b04aa86bdd2f15bdda5758f7dae1`,
baseline supplied by Luna `f423047fa`. This document specifies a conservative
diagnostic verifier, not a new solver or semantic rule.

## Parent and advance

Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` retains its original
accepted source domain, same original contribution `c`, every context/future
quantifier, and independent F1/FK1. Reuse the independently reviewed CLEAN
constructor proof `2026-10-18-demand-root-transport-correspondence.md`, SHA-256
`426b1bf969eb9628b73f5bcddec38b2f169d41341479dda4019965b34fad1244`.
That result was conditional on exact captured-bound, owned-input,
postcanonical-root and ordered-Replay hypotheses. The present result turns
those local hypotheses into finite predicates over actual retained evidence.
It does not assert that the fixture satisfies them: runtime is NOT RUN here.

The prior implementation's tuple-first lookup is insufficient: another
captured relation can have the same demand tuple while the selected Replay
upper has no dependency path to its restored bound. The verifier must start
from a selected Replay dependency, carry all its coordinates, and authenticate
the path to its particular upper fiber. The previous closeout, SHA-256
`4a7cb704d807e020acb0edb10a50e19fe26846f7b7e6b041d7e93b3ceb52d66f`,
is evidence of that review obstruction, not runtime evidence.

## Finite evidence and identities

All IDs below are borrowed from one live inference State and one retained route;
cross-State IDs, rollback-retired IDs and out-of-range indices reject. Let
`pair(p)` and `flow(p)=(transformer,demand)` be actual retained relation values.
Write a demand `D=(k,u,t,s,i)` for call, use, root, scope and input. `bound_pair`
uses the *whole* BoundKey `(owner,side,item)` with its real polarity; it must not
be replaced by a polarity-free endpoint pair. Value and Effect kinds must be
checked before interpreting endpoints.

A certificate consists of selected dependency coordinates and a finite ordered
list of actual edges. It names source call/introduction `k,t0`, captured bound
index `b`, captured evidence reference and complete snapshot `S`, retained
LocalFreshRoute `r`, its use `u`, the actual FreshUse Transport edge, a spine to
the selected Replay upper, the exact Replay edge, a spine to a whole Function
comparison `C`, and four ordered FunctionPort edges. Indices serve only as
addresses: every addressed value is rechecked against the owning tables.
The certificate is never accepted because a tuple or term shape was found.

### Source and FreshUse anchor

1. Authenticate the accepted source call and its omitted-formal introduction
   using the existing source-call owner; its native demand is exactly `t0`.
   The captured source relation `p` must carry `original_call=k,root=t0`.
   This is the same-source captured relation hypothesis of the reused theorem,
   not a claim that every captured relation is the initial seed. If source
   ownership needs an earlier seed-to-capture path, retain and check that path;
   absent owner evidence fails closed.
2. In route `r`'s actual graph, `b.relation=Some(p)`,
   `S=graph.bound_evidence[b.evidence]`, `S.relation=Some(p)` and
   `S.source_bound=b.source_bound`. Compare the complete captured snapshot,
   including admission/emission heads and coverage, to its imported retained
   antecedent. Equal relation/bound labels alone do not establish snapshot
   identity. Snapshot identity does not establish complete admission coverage;
   preserved coverage gaps remain gaps.
3. Require `r.use_instance=r.retained.context_use=u!=0`. Reconstruct this
   bound using this route's retained terms/effect operands, original side and
   actual canonical destination `B`. Require actual edge
   `Transport{child:p1,parent:p,use_origin:u,witness:Some(from:b.source_bound,
   to:B,reason:FreshUse)}` and actual attachment of `p1` to `B`.
   Restored/imported evidence must select `S` and the same `p1`; a matching
   witness elsewhere is insufficient. Compare `pair(p1)=bound_pair(B)`.
4. Require `j=graph.negative_functions[t0]` and the actual negative Function
   node with ordered child indices `ja,jae,jre,jr`. All five retained term-map
   entries must exist. Set `t1=T[j]`; verify its four actual children equal
   `[T[ja],T[jae],T[jre],T[jr]]`. Check the actual retained mapped scoped flow
   for `p`, the scope/input maps and `flow(p1)`. The source input must be
   *owned* by this copied region, and `D1.use=u`. A borrowed input retaining
   an older use cannot instantiate the sibling-copy theorem.
5. Require `pair(p1).upper=NegativeFunction(D1.root)` and `D1.root=t1`.
   Canonicalizing `B` does not update the supplied mapped demand automatically;
   a failure here is the first missing normalization edge, not permission to
   substitute a nearby Function.

### Supported demand-preserving spine steps

For each step, require the exact selected dependency exists and connects the
stated parent and child. Both endpoints must have a demand; call/use/scope/input
must be identical. Require zero scoped transformer and a Value pair whose
negative Function upper equals its demand root at both ends. There are two
supported forms:

* `Derived{parent,child}`: check the actual parent/child Value pair and the
  equation `child.root=child.pair.upper.root`, with the parent root likewise
  checked. If the upper is unchanged, roots must be unchanged. This is the
  extensional demand-root equation enforced by
  `candidate_context_value_rewrite`; a generic Derived tag alone does not
  prove extrusion, qualifier or copy-map correctness. Reject any Derived
  without these equations. The result authenticated here is the diagnostic
  root transition along an actual edge, not ownership of a semantic rewrite.
* `Transport{parent,child,use_origin,witness:Some(w)}`: require full from/to
  BoundKeys match the actual parent/child fibers and their typed pairs, a
  recognized reason (`Extrusion`, `ParentCopy`, `EqualityCanonicalization`),
  and its retained constructor evidence. Apply `transported_scoped` literally:
  inspect owner endpoints then item endpoints; the first endpoint equal to
  `NegativeFunction(parent.root)` must map to a negative Function, giving the
  new root. If neither matches, the root is unchanged. Verify the computed
  flow equals the actual child flow. A second FreshUse cannot masquerade as
  this step: it needs a separately authenticated route/map anchor. A witness
  with no retained from/to fiber association, or `witness=None`, rejects.

An implementation may support a strict subset and return no certificate for
the rest. Missing constructor evidence must not be filled by endpoint equality.
Internal Function-port commutation under a *later* extrusion is a separate
property: a root equation alone does not prove its internal four children are
the original FreshUse-mapped children. This verifier authenticates original
mapped children at `p1` and actual current consumed children at `C`, recording
each intervening root equation. A stronger composed child-map claim needs its
own actual structural copy evidence.

### Selected Replay and current consumers

Select one actual `Replay{child:q,lower:l,upper:h,lower_input:L,upper_input:H}`
before selecting a route. Require actual membership of `l` in bound fiber `L`
and of `h` in fiber `H`, `pair(l)=bound_pair(L)` and
`pair(h)=bound_pair(H)`, the actual ordered Replay task pair, and the exact
retained Replay recipe. Equality of typed pairs does not replace membership
or the full keys. Require `flow(l).demand=None` and
`flow(q).demand=flow(h).demand`. Check actual transformer composition in lower,
then upper order; a whole Function consumer additionally requires its resulting
transformer zero. The first supported spine must end at this exact `h`.

Starting at `q`, a second supported spine may reach `C` (zero steps permitted).
Require `pair(C)=F+ <: G-`, its upper `G-` equals `C.demand.root`, and actual
Function children of both polarities. For each field require a real dependency
`FunctionPort{child:Cfield,parent:C,field,operation}` with the following typed
child pair and scoped-flow effect. Field identity, pair and operation are all
checked, not only an unordered set of children:

| Ordered field | Actual typed pair | Operation | Scoped demand/transformer |
| --- | --- | --- | --- |
| argument | `G.argument+ <: F.argument-` | Swap | none / identity |
| argument effect | `G.argumentEffect+ <: F.argumentEffect-` | Swap | none / `stamp_input(i)` |
| result effect | `F.resultEffect+ <: G.resultEffect-` | Preserve | none / `protect_body(s,i)` |
| result value | `F.result+ <: G.result-` | Preserve | none / identity |

The effect transformers are compared extensionally or through the canonical
interned transformer owner, not guessed from a nonzero ID. The edges prove
admission by the port constructor; a claim about later execution additionally
requires its actual consumer receipt. Every requested consumer receipt must
name this child/parent/field. The constructor may also emit a Derived edge for
the *same* port parent/child; this is auxiliary evidence of port admission and
cannot be used as a demand-bearing spine step (the demand has been consumed).

## Fail-closed selection and proof

No search may choose the first same-tuple candidate. Enumerate/check only the
bounded live dependency inventory. For each requested spine node require one
unambiguous supported incoming spine edge, ultimately the specified FreshUse
anchor; an additional unsupported or competing demand-bearing edge rejects.
Multiple routes, source bounds or captured snapshots satisfying a requested
anchor reject unless their exact owner coordinate was supplied and there is
no competing ancestry for the selected child. Duplicate tuples with different
IDs never merge. A tuple-only request with duplicate candidates rejects.
Exact duplicate dependency coordinates must not be counted as two independent
proofs; a conservative observer may reject duplicate records entirely. A
revisited relation/cycle, absent edge, exhausted bound, unknown reason/kind,
substituted BoundKey, sibling route or mismatched snapshot rejects. Self-loops
also reject. Resource exhaustion returns unauthenticated and changes no solver
result. This is deliberately incomplete for authentic paths with merged
derivations; it does not reject the user's program.

Conditional theorem: if all predicates above succeed, the selected Replay
upper is connected by those exact checked demand transitions to the specified
source-owned captured demand under its actual FreshUse route; the Replay child
inherits that upper's demand, and all four specified FunctionPort admissions
consume the resulting current root, scope and input in their stated positions.
Proof: the anchor is exactly the reviewed FreshUse constructor theorem with
snapshot, map, owned-input and normalized-upper hypotheses supplied. Induct
on the finite first spine using the explicit demand equations; Replay inherits
only its checked upper demand. Induct on the second spine. Substitute the
current checked root and tuple into the four port constructors. Uniqueness
and cycle rejection prevent substituting a different derivation during either
induction. This proves the conditional diagnostic statement; it supplies no
semantic correctness for an otherwise unproved rewrite.

For sibling uses of the same graph, require distinct `context_use` and route
identity, their own snapshots/imported antecedents/maps/witnesses and distinct
owned input/scope copies. Even if some nongeneric terms coincide, substituting
either use at a selected upper breaks the required ancestry/use equations.
Integer propagation to both source results is a separate runtime assertion,
not a consequence of this demand metadata theorem.

Port permutation tests require all four comparisons to hold before acceptance.
Swapping two pairwise-distinct expected entries makes exactly those two
positions false and leaves the untouched positions true; their conjunction
is false. For fields with coincident term values, term equality alone cannot
detect a permutation: retain/check distinct field/edge identities and typed
pairs. Do not claim `[false;4]` after a two-position swap.

## Application, remaining evidence and checks

For local P3, a successful certificate supplies a real source/use/Replay route
address for transporting an independently established `At(D,c,delta)`; it does
not establish that judgment or every reached/future lower. For local P4 it
instantiates only the demand-root and actual Function-field portion of the
reviewed constructor result. Complete provider/witness/residual presentation,
all extrusion/intrusion/generalization paths and dependent checks remain open.
Original conditions closed: **0**. Fixed-c formation, W/Z, accepted-domain
cases, F1/FK1, N-Transport, complete Call, soundness, principality, termination
and production gates retain their existing status.

Mutual TODO `NPAIR-REPLAY-ANCESTRY-RUNTIME-20261018`: the leased implementation
owner must emit/check the exact source snapshot, retained route and real
FreshUse witness, both bounded spines, Replay keys/relations and four actual
port admissions/consumer receipts on the accepted two-use fixture. First
missing/ambiguous edge is the falsifier. Negative cases substitute each of:
unrelated same-tuple relation, source snapshot, sibling use, root, BoundKey,
ancestry edge, unsupported edge, and each pairwise port permutation. Preserve
the raw `native_root_matches=false`; a transported correspondence does not
change raw equality. Luna owns independent review and one-shot runtime release.

Original TODO `NPAIR-P3P4-DEPENDENT-TRANSPORT` remains with Operation/Call and
capture/extrusion/intrusion consumer owners: supply the same original `c` and
complete `At(D,c,delta)` at the accepted incidence, then preserve it through
each real route and future lower. Diagnostic ancestry does not supply it.

Static constructor reads only; no compiler/test/probe/Git execution, code edit,
external contact or descendants. Governing dependency pins and authoritative
inference principles were read. No runtime or complete source admission
coverage is asserted. Source files are concurrently leased to the separate
implementation lane: the source equations here are those read from the frozen
contract baseline, and this candidate does not certify later implementation
bytes. Frozen proof/handoff hashes are supplied in the assignment handoff.
