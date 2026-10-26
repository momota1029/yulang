# Original identity Function membership: receipt realization and the exact open application

Date: 2026-10-26. Baseline: `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`.
Producer: `/root/source_membership_r4`, bounded supported `lean_prover` leaf.
Status: **original Function membership not proved or refuted**. The checked
receiving-component construction below is not a substitute definition of
`ValueMem`, `PhiW`, `P_F`, `SourceT`, or the original source judgment. Fresh
independent review remains required.

## 1. The unchanged target and the attempted application

The actual source still separates the retained relay from the returned identity:

```yulang
my relay (thunk:[] (int -> int)) = thunk
my main = relay (\x -> x)
```

`C` is the delayed argument computation. Executing `C` constructs and returns
the actual identity value `W`. The fixture contains no later invocation of
`W`. Universal invocation challenges are required by `W`'s Function membership;
they are not additional source occurrences invented for this fixture.

The selected [Function definition](../design/2026-10-08-contextual-function-membership-definition.md)
§2 requires the same actual provider at every independently admitted complete
challenge, actual acceptance of the same whole carrier, and every actual
complete, pending, administrative and zero-step observation and admitted
development in the **full** original observation contract. The
[selected closure construction](../design/2026-10-08-captured-closure-constructor-definition.md)
§2 gives the relevant complete interface:

```text
F† = Strict(I_x, x:A_x, PureReturn(A_x), IF_id).
```

This is a complete Value-entry contract: receipt, designated Force of the
arbitrary admitted carrier, actual Return/rebind, identity body and invocation
return. The inlet can admit effects and divergence. Neither identity syntax
nor a pure body makes its complete invocation pure.

The prior [lambda construction](2026-10-26-source-identity-lambda-construction.md)
already proves paper identity typing, actual paper context substitution, all
represented finite interactions and the symbolic same-interface inlet
calculation. The prior [world construction](2026-10-26-source-identity-world-construction.md)
constructs the actual rebind, Name receipt, owned return and all represented
suffix prefixes. This packet attempted to apply those results to the original
membership head, rather than proving another theorem called identity typing.

Take an **arbitrary original** `d ∈ D_F†(e)` and each actual retained
`Act(W,U_id,r)`. Inverting the stored unannotated parameter gives
`CarrierContract(U_id)=I_x`. The very carrier certificate and receipt/path/context
preconditions in `d` therefore construct `ActualAdm(W,U_id,d)` at `d`'s same
event, as established by the earlier inlet calculation. No membership of `W`,
body success, Return, final world or Q result is needed for this part.

The remaining part is not another inlet inclusion. It is the full observation
readout for this same `d`, including the original current-world and history
interpretation. The following investigation establishes why raw receipt growth
is not, by itself, a contradiction, and identifies the still missing application
at its actual source owners.

## 2. An administrative receipt abstraction that does not erase evidence

### 2.1 The actual source and native constructors

[Semantic input realization](2026-10-08-call-semantic-input-realization.md)
§4.2 reads a Name from its immutable binding and returns the same value/provider
at the current source world. Its pure Return does not create a receipt. The
typed-boundary receiving account, in contrast to a mere allocated identity,
introduces `Receive(u,slot,view,correspondence)` when an invocation obtains a
view in a typed binding. Its subsequent `Path` joins that receipt with the same
view's typed flow and observation; `Inc_C` separately checks current activity.
See [typed-boundary realization §6](../design/2026-10-02-typed-boundary-realization-draft.md#6-common-typed-view-transport).
That decorated receiving account is an input to the older source correspondence,
not a complete adopted descriptor model.

The native owner equations are more operational:

| Owner | Actual action relevant to identity |
| --- | --- |
| `program.rs`, parameter role and Name construction | The unannotated parameter has Value entry and its resolved Name has Observe consumption. |
| `machine.rs::Frame::ValueEntry`, `bind`, `extend` | The actual returned packet is bound as Value; the lexical parent dispatch is retained. An unannotated formal has no `CallbackResultSchema` action. |
| `machine.rs::Instruction::Name` and `dispatch_name` | Resolve the actual parameter cell; apply the current dictionary substitution to the returned packet's dispatch. |
| `machine.rs::consume` | Check that the registered view belongs to that value, append a genuine current-owner Name receipt, then return the packet for Observe. |
| `receiving.rs::receipt` | Append the complete `(owner,view,site,formal)` record and overwrite only its exact last-receipt index key. All earlier records and views persist. |
| `machine.rs::ReceiverReturn`, `leave_owner` | Deactivate exactly the invocation being completed and restore its actual previous owner. Historical receipts are not live-owner evidence. |

Thus the source binding receipt and its native materialization need not occur
at the same small-step boundary. Equating entire native worlds is too strong;
erasing all receipts is too weak. The native receiving consumers actually use
them: `callback_entry_for_apply` checks the current Name site's receipt, and
`local_grant` joins the exact candidate owner's receipt of the observed view.

### 2.2 Checked construction

[SourceFunctionMembership.lean](lean/YulangClosure/SourceFunctionMembership.lean)
uses the existing R3 `Receiving`, `Receipt`, `World`, `bindValue` and
`observeName`. It introduces no new semantic Function or world-validity
predicate.

`Recorded(r,receipt)` means an actually allocated native receipt with all four
fields intact. `ReceivedBy(r,u,v)` is its owner/view projection. The checked
append equation says:

```text
Recorded(record(r,u,v,site,None), receipt)
  iff Recorded(r,receipt) or receipt=(u,v,site,None).
```

The record index bounds are checked, so an arbitrary function value in an
unallocated `Store` cell cannot count as a receipt. The owner/view consequence
is equally exact: only the new `(u,v)` pair is added; all previous pairs remain.
This does not infer activity, protection, a grant or an observation from the
mere existence of a receipt.

The candidate interpretation has two explicit phases. A **binding** phase
stores the native receiving record and the actual pending owner/view/site.
An **executed** phase stores the actual receiving record after Name. Realizing
the binding phase applies the already fixed receipt constructor; realizing the
executed phase retains its record. Consequently:

```text
realize(binding(r,u,v,site))
  = realize(executed(record(r,u,v,site,None))).
```

This equality retains the **entire receiving component**, including every
receipt identity, source slot, optional formal, old log entry, last-receipt
index and view. Therefore every function of that complete component gives
the same result on both realizations. It is not only equality of receipt
counts or a projection that hides a changed guard.

`identity_name_materialization` applies this square after the actual parameter
binding. Its premises are only lookup of the selected lexical parent and the
actual incoming view/value match. It derives successful Name execution using
R3's constructed binding lookup. The output record retains the actual dispatch
result explicitly. No successful Name, membership, final-world validity or
body derivation is supplied as a premise.

The binding phase is **relation data**, not a claim that the native receipt
already executed. To use it for the original source semantics one must map the
source typed binding receipt, its slot and correspondence, to this phase data.
In particular, a formal's source binding slot is not identified with the body
Name's source site merely because both concern `x`; the native new record has
`formal=None`. Their actual source-reference edge must carry the correspondence.
The theorem supplies the materialization square once that original field map
is constructed. It does not supply the missing field map by a new definition
of the old judgment.

R3's finite-prefix classification makes the phase placement precise. Before
the arbitrary carrier actually returns there is no new parameter binding and
no pending Name receipt. After rebind, the binding-phase data can be formed
from the actual packet and current owner. Name materializes it. Owned return
retains the log but deactivates its owner. No receipt is created on a divergent
carrier prefix, replayed during an earlier pending resumption, or treated as a
grant after invocation exit.

### 2.3 A proved obstruction to the stronger, incorrect stuttering demand

`no_executed_receive_reflecting_stutter` names a precise failed alternative.
Suppose a first Name read has no executed receipt of this view by its current
owner. There cannot be one unchanged abstract state related to both sides if
its `Receive` predicate is required to reflect **executed native receipts**
at both sides. The append equation supplies Receive afterward and its absence
beforehand gives a contradiction through the two reflection equivalences.

This uses the real Receive premise of the Path join, not an invented rejecting
guard. It refutes that particular reflection/stuttering combination. It does
**not** refute identity membership, prove an admitted original challenge for a
counterexample, or rule out the phase-indexed binding realization above. No
source soundness counterexample is claimed.

## 3. The complete challenge calculation, with the first unavailable arrows

For the original coinductive application let `H_id` contain only the exact
identity value tuples at their original root, source incidences and lawful
event restrictions. The callable may occur inside an arbitrary carrier,
response, continuation or future client, even though its own captures are
empty. Those background objects are not deleted and are not declared holes.

Keep all four components of the selected declared-hole background `B_H`.
Extend it with the exact source/native identity tuples and every actual finite
invocation-prefix row at the one original `eta0`, `xi=(nu,K,D)` and witness.
This is the natural candidate `S`; merely putting an observation into `S.T`
does not establish its `PhiT` or `P_F[S]` obligation.

The arbitrary-exact-`H` [RP5 lift](2026-10-24-original-raw-observation-postfixedness.md)
§3 is already proved and applies without a finite-cardinality restriction. It
will carry the entire background once the actual added rows have their full
one-step readouts and the identity hole has been replaced. The attempted
application has the following exact phases:

| Original phase | Available construction | Still required for the full original conclusion |
| --- | --- | --- |
| Initial and receipt/entry | Actual stored Value-entry/provider; `ActualAdm` at this same complete challenge | Interpret the original challenge's full typed receipt/path/current-world fields and its genuine receipt transition. |
| Arbitrary pre-Return Force prefixes | The unchanged whole-carrier certificate; no body or result assumption | Its uniformly interpreted `B_H.Car`, pending world, response and continuation fields in the original context/history model. |
| Request and each raw Resume | Original raw handle, actual current resumed state, exactly the unfinished rebind/body/return suffix | The same full typed request/response/scope/authority map at each original admitted history, including repeated resumptions. |
| Actual argument Return/rebind | The same returned value/root/provider; R3 constructs all old/new bindings and control/registration fields | Interpret all remaining original current-world and dependent binding incidences at that tuple. |
| Identity body Name | Genuine lookup and view match; the receipt materialization square above; unchanged raw value/view | Source binding-slot/Name-site typed correspondence and dictionary denotation at the original assignment. |
| Invocation return | Exact invocation deactivation, previous-owner restoration and retained history | Original result/future port and full current-world interpretation across this actual return. |
| Later use | The argument result's hereditary contract; no extra Force or invented call of `W` | Its original lawful restriction at every admitted future event and the original descriptor's dependent future interpretation. |

This table preserves the entire challenge and finite-history domain. It does
not assume termination to reach the lower rows. Earlier rows are obligations
on their own, including zero steps and indefinitely many pending developments.

## 4. The precise definition/correspondence boundary

The remaining difficulty is not that receipt arrays have different lengths.
Nor is it an arbitrary extra predicate attached to an otherwise specified
identity descriptor. The selected sources retain the following *named old
objects* but do not provide their complete native/source interpretation:

1. **The original complete context/history proof-field telescope.** The
   selected Function definition §2 explicitly leaves the source context
   domain and complete admission/observation relations independent. The
   selected simultaneous introduction §3 defines their intended `B_H` meaning
   and requires uniform interpretation over the entire independent domain;
   it does not derive an interpretation of another already fixed context
   certificate from that definition. The missing map must preserve all
   original carriers, worlds, responses and continuations at once. Defining
   its domain to be the certificates already known to map would violate the
   fixed-domain condition.
2. **The original jointly indexed world/phase field types and their actual
   actions.** `PhiW` requires the jointly valid registry, scope, current
   authority and incidence tuple in addition to all binding certificates.
   `P_F[Z]` expressly retains its entire independently specified hard envelope.
   The new receiving square and R3's five world fields do not define that
   complete tuple. The needed Name map must compose the original binding
   slot, actual Name occurrence and typed correspondence while retaining
   every original provider and witness. The subsequent return map must keep
   the completed invocation inactive rather than recover activity from its
   new historical receipt.
3. **The dictionary interpretation of the same decorated binding.** In
   `dispatch.rs::name`, even when no new Name-instantiation step is selected,
   the result is `then(value.dispatch,current.substitution)`. `Then` is ordered
   substitution composition, not an idempotent normalization. This code
   supplies the concrete action and its source sites, but no field map from
   that action to the old `nu,K,D`/descriptor interpretation. R3 keeps the
   output dispatch explicit and this packet preserves that boundary. Equating
   raw value handles cannot discharge this decorated-value requirement.
4. **The actual descriptor and annotation identification.** `F†` is constructed
   at the source-owned `I_x,IF_id`. The written `int -> int` is another actual
   source boundary whose complete domain, observation, profile and future
   meaning must be identified or compared by its original local law. A paper
   `callable int int` derivation is a value-type projection and does not supply
   that full correspondence. The selected Generalize definition §3 expressly
   retains genuine L1–L5 world, checking, annotation and lifetime laws.

This was checked against the later candidate owners as well as the October 8
sources. [Source-context guard interpretation](../design/2026-10-18-source-context-guard-interpretation.md)
is explicitly Draft and records that the original `j0/a0` telescope,
projections and old-global-predicate actions are not supplied. Its named
residuals are not evidence. [MI Return incidence](../design/2026-10-18-mi-return-incidence-telescope-proposal.md)
explicitly defines a different candidate port and does not identify it with
the old Return/`DeclContribution` telescope. The more recent
[original Call evidence candidate](2026-10-26-original-call-evidence-construction.md)
similarly distinguishes its explicit proposed declaration from the undeclared
historical predicate. None of those documents is promoted here.

The operational/source safety manuscripts define a useful syntax-directed
decorated machine, but disclose their source-correspondence and original
descriptor limits. Replacing the original independently admitted contexts by
that paper syntax would omit the required whole original interpretation.
Likewise, defining membership to mean execution safety, assuming the missing
`P_F` readout, or adding the desired body theorem to a `LocalLaws` parameter
would not finish this application.

The next original proof step is therefore a fieldwise interpretation at these
named owners, with its exact quantifiers and one joint witness. This packet
provides a checked way for one subtle phase seam to commute; it does not claim
that a complete faithful model is impossible. No new observable semantic
choice, smaller source language, narrowed challenge domain or changed profile
policy has been adopted.

## 5. Verification and outcome

The pinned Lean 4.35.0 checker accepted the module and all six authored roots.
A separate originating-module census includes generated/private theorem
constants and prints every full type and transitive axiom dependency. The
complete receipts, exact counts, preserved failed source snapshots, root
manifest and frozen input/output hashes are in the
[handoff](../../tasks/agent-loop/inbox/20261026-source-function-membership-r4.md).
No root import, shared cache, compiler, tests, expected output, configuration,
shared status or Git state was written by this leaf.

The original `ValueMem_F†(W,r,e)`, the complete annotation bridge and `SourceT`
remain **OPEN**. This is neither a positive membership theorem nor a
source-qualified counterexample to it. The source meaning must still be
connected to the concrete phase construction above before RP5 can complete
the unchanged original Function introduction.
