# Identity Lambda: actual rebind, Name receipt, and current return world

Date: 2026-10-26. Input baseline: `60e8684224a8a911a5627b845312750a192be777`.
Producer: `/root/source_world_r3`, supported generic `lean_prover` leaf.
Status: bounded construction; independent review pending. Original contextual
Function introduction and full `SourceProblem.InferenceSoundness` remain **OPEN**.

## 1. Result and the original obligation

The new [SourceIdentityWorld.lean](lean/YulangClosure/SourceIdentityWorld.lean)
constructs the current-world actions of the identity's actual **post-Force
suffix**. It supplies more than an equation on the returned value:

1. Actual parameter binding appends the received record and the lexical
   environment node, using the selected parent's dispatch data.
2. All earlier installed binding certificates can be retained at one common
   current event. Earlier aliases and captures keep their original addresses
   and complete received records, including when their environment is not the
   most recently allocated environment.
3. The body Name obtains that same binding, records its actual read receipt,
   and preserves the full view registry. Its dictionary field is the actual
   Name-dispatch result, not an assumed identity action.
4. Invocation return deactivates exactly its own invocation and restores the
   original previous execution owner. Earlier receipts retain their original
   owner identity; their existence does not reactivate that owner.
5. Every finite prefix of the represented three-action suffix is classified,
   including its zero-step prefix. No successful final run is a premise.

These are checked constructions of the binding, registration, and control
fields that the original world and observation clauses require. They are not
the full original `PhiW`, `P_F`, or declared-hole interpretation. In particular,
the definition `World` below is an explicitly described native **projection**;
it is not substituted for the original jointly indexed world.

The original target is unchanged. For
`F† = Strict(I_x,x:A_x,PureReturn(A_x),IF_id)`, every independently admitted
challenge must be interpreted under only the exact identity-value declaration,
and every actual entry/body/return observation must satisfy the original full
envelope at its actual joint tuple. No world, carrier, continuation, current
authority, or guard is admitted as a declared hole. The same provider, original
`eta0`, `xi`, scopes, and hard dependencies must survive the application.

The [accepted identity construction](2026-10-26-source-identity-lambda-construction.md)
already constructs paper identity typing and capture-avoiding callable-hole
substitution. Its arbitrary represented interaction theorem remains unchanged.
Its original inlet equality already gives `ActualAdm` at `F†`; this note does
not repackage that calculation. The arbitrary-exact-H relative lift in
[original raw postfixedness](2026-10-24-original-raw-observation-postfixedness.md)
§3 and the existing full native profile catalogue are also retained as available.

## 2. Original source cases and the live native distinction

The selected [contextual membership definition](../design/2026-10-08-contextual-function-membership-definition.md)
§3 and [semantic input realization](2026-10-08-call-semantic-input-realization.md)
§4 require every immutable binding to be interpreted at the actual compatible
event. Pure Return retains the returned value/provider and result incidences;
binding extension uses the genuine carrier-result certificate. The selected
[complete closure constructor](../design/2026-10-08-captured-closure-constructor-definition.md)
§2 keeps actual Return/rebind before the body and original invocation return
after it. The full positive clause is the original one in
[simultaneous immutable introduction](2026-10-08-simultaneous-immutable-root-introduction.md)
§3, including its independent guards.

The native owner inspection exposes an important distinction within this
application. `machine.rs::consume` calls `receiving.receipt` **before** its
`NameConsumption::Observe` branch returns the received value. The receipt
operation appends a full `(owner,view,site,formal)` record and updates the
corresponding index. It does not rewrite the view. Thus value/view identity
does not imply equality of the native worlds before and after the Name read.

`name_world_changes` checks that distinction directly: the receipt count grows
by one, so the resulting projected world cannot equal the input world. This
is an operational separation witness against an unchanged-native-world bridge.
It is not a refutation of original Function membership, the source manuscript,
or the inference theorem. A source/native interpretation may relate these
different worlds, but that relation has to account for the actual read receipt.
No source guard is erased merely because the surface body is pure.

A second distinction is `dispatch_name`. It can change the returned record's
dictionary substitution and mutate its separate dictionary-machine store.
`suffix_result_fields` therefore preserves value and view exactly and exposes
the actual resulting dispatch field. `suffix_result_identity` proves complete
record equality only when the incoming interface is already Value and the
Name's dispatch result is the original dispatch. Dictionary computation and
its semantic action are not silently treated as identities.

### Source-to-construction map

Native paths in this table are under `tools/inference-playground/src/runtime/`.
They are static owner correspondences; no native execution or whole-machine
simulation was run or proved by this packet.

| Original/native owner | Checked construction | Exact preserved or changed fields |
| --- | --- | --- |
| `machine.rs::bind`, `extend`; semantic input §4.1 ValueBind | `bindValue`, `bind_valid`, `bind_read` | New cell is the actual received packet with Value interface; new environment uses the actual lexical parent's dispatch. |
| Immutable old bindings, imports, aliases, capture references | `bind_old_read`, `bind_all_installed`, `identity_bindings_at_event` | Every old installed cell is covered; old addresses and received records are unchanged. Independent hereditary restriction acts at one shared event. |
| `machine.rs::consume` Observe; `receiving.rs::receipt` | `observeName`, `name_success`, `receipt_new`, `receipt_old`, `receipt_index`, `receipt_other_index` | Exact new Name site and current owner; all prior receipt entries; other receipt-index keys; all view data. |
| `machine.rs::dispatch_name`; `dispatch.rs::Machine::name` | `Received.atName`, `suffix_result_fields` | The actual output dispatch is explicit. Its calculation and dictionary-store mutation are not represented. |
| `machine.rs::leave_owner` on owned ReceiverReturn | `Control.leave`, `leave_success`, `deactivate_current`, `deactivate_other` | Original current/top/registered/active checks; one deactivation; original previous owner; all unrelated invocation entries. |
| Historical receipts and live current ownership | `deactivate_registered`, `identity_world_fields` | Historical registration persists; active authority uses the current invocation registry; no receipt-based revival. |
| Original identity Name/Result/return suffix | `identity_suffix`, `identity_suffix_prefixes` | Constructed successes and all finite projected suffix prefixes; actual view and returned-value fields; final owner inactive. |

The identity has an unannotated Value-entry formal and an Observe body Name.
The separate relay has explicit outer effect syntax, Computation entry, and
an Execute body Name. The source remains:

```yulang
my relay (thunk:[] (int -> int)) = thunk
my main = relay (\x -> x)
```

`C` remains the delayed argument computation whose execution constructs and
returns `W`. This fixture contains no later Call of `W`. The identity-suffix
theorem is for the arbitrary invocation challenges required by its Function
membership obligation; it adds no such invocation to the fixture. Relay's
actual `RootCompReturn` behavior remains the earlier retained-result result.

## 3. What is constructed, and which premises are real inputs

### 3.1 Actual operation construction

`identity_suffix` is uniform over the raw received value payload, complete
view metadata, source site, lexical identities, parent environment, and the
current world projection. Its independent premises are precisely:

- lookup of the selected lexical parent node succeeds;
- the argument's actual view is registered for its actual value;
- the current execution owner is the actual identity invocation;
- that invocation is the top owned frame;
- its stored invocation record exists and is active.

These are raw input/frame guards. The proof does not receive a successful
Name or invocation return, an identity-membership certificate, a body-typing
premise, or a final world. It computes parameter binding, proves the exact
Name lookup, derives successful view matching and receipt insertion, and
discharges the owned-return checks from those original fields.

The native active vector is represented in reverse order, with its innermost
element first. `Control.leave` models the successful owned case. The native
failure paths, including mutations made before a failure, are not modeled by
this successful suffix relation. They are not declared unreachable for the
full source language.

`identity_suffix_prefixes` uses the existing length-indexed `Prefix` from
`Contracts.lean`. It derives that any finite represented suffix prefix is at
one of these actual states:

| Phase | Binding and live-world facts |
| --- | --- |
| Actual carrier Return, before rebind | Original current world and raw packet; no new cell yet. |
| Bound body Name | Exactly one new parameter cell/environment; no new Name receipt yet. |
| Name has returned | Same value/view; one actual Name receipt; invocation still current. |
| Invocation has returned | Same result view; own invocation inactive; previous owner restored; historical receipt retained. |

The theorem neither demands nor constructs termination of the arbitrary
carrier. Requests, divergence, receipt/Force prefixes before its actual Return,
resumption of the carrier, and future use of a latent result retain their
original separate obligations. This is a suffix theorem, not a smaller
replacement domain for complete Function challenges.

### 3.2 World fields rather than assumed final-world validity

`identity_world_fields` constructs five concrete conjuncts for the resulting
projected world: valid environment-parent structure, every installed binding's
predicate `P`, every installed binding's view/value match, the entire receipt
registration history, and valid current control. Its inputs are the corresponding
old-world fields, the actual new result's certificate, and the saved previous
owner being module scope or a remaining active frame. The new invocation record
is tied to its actual original record by `identity_suffix`'s registration premise
when the two results are applied together.

`P` is an arbitrary per-cell predicate over the **whole received record**.
It can express the original candidate-relative value or designated-carrier
certificate of each particular binding. The theorem does not create those
semantic meanings. It constructs their all-binding conjunction after appending
the genuine returned packet. No predicate of the final world is supplied as an
input. `identity_bindings_at_event` separately applies the original independent
hereditary actions to every old binding at the same actual compatible event
before appending the result certificate there. Compatibility is an input of
the independent history domain, not manufactured from immutability.

The complete original joint guard additionally contains source/profile/license,
scope, typed-path, correlated witness, and descriptor-specific conditions.
The five checked conjuncts do not replace that conjunction. The `Rest` field
can retain additional fields untouched by the represented primitives; it is
not an assertion that the entire native machine, dictionary store, or all
original joint evidence is unchanged.

## 4. Application to the original parent and the first remaining owner

Before this packet, the local world step was described as typed rebind followed
by a same-value Name/Return in the current world. There was no checked action
for the entire old cell set, the real read receipt, and invocation deactivation
together. That part is now an explicit construction and finite-prefix result.
In particular, a future proof may not make the omitted Name receipt disappear
or reuse its historical owner as live authority.

For an arbitrary unchanged original `d ∈ D_F†`, first use its whole-carrier
contract at its **actual** Return event. Once the original field interpretation
provides the old binding certificates, returned-value certificate, view identity,
and current frame fields at that same event, the new theorems construct the
post-Return binding and control/receipt fields. They require no Function
membership of `W`. In the simultaneous proof the binding predicate can use
`S.V` and `S.Car`; no candidate is eliminated as a completed greatest-fixed-point
member. The already available RP5 lift is unchanged.

The first unresolved owner is the **original context/history/descriptor
interpretation**. It must identify each original challenge's complete dependent
fields with the actual source/native world events and establish the remaining
full guard actions, particularly the executed Name receipt and actual dictionary
action. A bare typed paper context or final `P_F` premise cannot replace that
construction. The precise next evidence is a source-defined field map at the
actual Name/Return occurrence that preserves its provider, view, dictionary,
current authority, and joint witness and derives the remaining original
`PureReturn(A_x)`/Strict hard-envelope conjuncts.

After that map, pre-Return phases and all original pending/future/alternative
contracts still require their own full readouts. Descriptor identification with
the independently fixed `int -> int` annotation and the original source
derivation `T` also remain open. This packet does not identify `F†` with that
annotation, construct original `ValueMem_F(W,r,e)`, or prove the all-language
inference theorem. It changes no supported source form, inference behavior,
declared challenge, semantic policy, or production gate.

## 5. Verification and evidence

The isolated project uses the unchanged Lean 4.35.0 pin and official local
distribution, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Lake reports
`5.0.0-src+eb6cafb (Lean version 4.35.0)`. Sandbox installation detection failed;
the authorized normal-process version check succeeded. No installation,
network call, dependency change, shared cache write, compiler edit, native test,
Git operation, or root import edit occurred.

The exact final check counts, complete printed types/axioms (including generated
and private originating declarations), resource receipts, material failed
source snapshots/logs, and frozen hashes are retained in the
[assignment handoff](../../tasks/agent-loop/inbox/20261026-source-identity-world-r3.md).
Checker acceptance does not supply independent review or the missing original
source interpretation.

The final focused build and all 26 authored theorem audits passed. The complete
originating-module census passed for **91 theorem constants**, including all
private/generated helpers and those 26 required roots. Of those 91, 53 use no
axioms, 35 use only `propext`, and 3 use `propext` and `Quot.sound`; none uses
`Classical.choice`. No final lint warnings were emitted. Eight focused checker
calls, including the census, used a total of 17.26 measured seconds; material
failures are retained. Each used one CPU, `LEAN_NUM_THREADS=1`, and `-M1024`,
with an outer 119-second bound and monitored aggregate 1-GiB RSS ceiling. The
largest observed aggregate RSS was 920,035,328 bytes.

Frozen Lean SHA-256:
`6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168`.
