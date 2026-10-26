# Actual Value Return: the decoded world at the consuming source event

Date: 2026-10-27. Branch: `yulang3`. Producer: primary `/root`.
Implementation: `lean/YulangClosure/OriginalReturnWorld.lean`.

Status: **constructed and kernel checked; independent review pending**.
The original whole-language soundness, Effect hygiene, principality and
inference termination goals remain open. This module supplies a concrete
Return/readout/source-consumer join, without changing the original source
rules or native allocator.

## 1. Original obligation and the missing event equality

Source Generalize's original Value entry orders invocation, actual receiving,
Force/Return, native binding, installed Shared and the body. See
`2026-10-08-source-generalize-definition-and-proof.md` §3.3 and the actual
`OriginalFormalShared.enteredBody`/`entry_actual_return_consumer` definitions.
The full source pattern and body remain the original parameters; no identity
or record-only source fragment is substituted.

`OriginalParameterWorld.delivered_native_bind_readout` already computes the
complete allocated registry. `OriginalForcedParameter` already derives old
world and returned-value membership from a genuine observation of the same
whole carrier. The remaining join is the event: the decoded source Return
must contain that actual native bind, and the final installed registry must
be interpreted at that event rather than the earlier receipt event.

The post-Force world need not equal the receipt world. Treating it as equal
would lose new cells, provider/alias data, residual state, receiving state or
control changes performed by Force. This module retains the complete raw
post-Force snapshot and computes only the actual native binding update.

## 2. Constructed readout and exact retained data

`Packet` contains independent raw operands: a complete native snapshot,
received value, saved parent environment and its real node lookup, history,
observation, endpoints and pre-existing binding list. It has no membership,
postcondition, installed-registry equality or desired world invariant field.

`Packet.outcome` calls the existing `SourceIdentityWorld.bindValue` on
those operands. The allocated address is the old cell-vector length; the
binding record appends the original formal name and that address. The
returned value/root are interpreted by the independent `ViewAssignment`.

`valueReadout` interprets this same Return at the original `returnBinder`.
It installs the already selected descriptor only at the newly bound cell.
The inherited scoped witness strategy remains the same, while the independent
base readout supplies the actual current event fields. Other runtime kinds
and binders keep the base readout. The receipt field is not rewritten.

`computed_return_event` calculates the complete resulting Event, not just its
cell projection. It is exactly the existing `bindEvent` applied to
`beforeBind`, reconstructed from this actual packet and the same Return's
independent fields. `return_current_native_fields` explicitly preserves
residual, providers, aliases, receiving, control and rest. The static fiber,
entry assignment and shared strategy are inherited through the same event
construction.

This is a constructed local readout. It does not prove that an arbitrary
previous opaque `RuntimeReadout` already performs this interpretation.
Identifying a separately fixed original/native presentation with it remains
a correspondence obligation.

## 3. Actual decoding and own-event registry

`decoded_return_event` computes the real source `returnState` after the
original `scopeCandidate` and binder extension. `delivered_event` then
computes the subsequent original `deliverFrame`; installing Shared does not
replace this event with an earlier one. The private `objects_keep_installed`
induction covers every decoded endpoint object before the native binding is
installed.

`delivered_registry_at_own_event` proves:

```lean
post.installed = OriginalParameterSemantics.installed post.assignment.event
```

Here `post` is the actual constructed Return/Shared decoded state. The old
installed-map representation remains a premise at the **actual post-Force,
pre-bind world**. It is not silently inferred from the earlier receipt.
Deriving that representation through all actual Force effects remains a
separate whole-execution invariant. The finite vector-store representation
and real parent lookup are likewise explicit operational inputs.

## 4. Source-consumer application

The original `OriginalRecursivePair.Returned` carries a raw world and value.
`PairData` supplies its other native observation fields independently.
Its `packet` always uses the returned packet's actual world, and
`presentation` computes the same native bind on a successful parent lookup.
It remains total when no parent exists; the application theorem requires
the real successful lookup and makes no success claim for the absent case.

`pair_outcome` and `pair_evidence` identify that original pair readout with
the raw packet construction. They retain the same source-selected descriptor
and Shared witness.

`actual_entry_return_world` applies the existing original entry consumer to
a genuine `execution.Returns raw`. From the source judgment at the original
Value entry, it derives a witness and Shared occurrence together with:

1. Successful decoding of the actual Return/Shared source environment.
2. The original `checkedBody parameter` judgment in that same environment.
3. The complete installed-map equality at that decoded state's own Event.

The existential witness is obtained from the actual source admission and
used in that same extended environment. No body derivation or desired
post-registry equation is added as an admission field. This theorem retains
the original arbitrary pattern/body, invocation, actual Return, owner and
selected contract. Its local kernel and operational premises remain explicit.

## 5. Meaning and the recursive hole-relative variant

`delivered_phiW_at_own_event` transports the general one-step world invariant
to the same decoded Event. Its candidate restriction, return membership and
world guards remain exactly the existing `bind_phiW` obligations.

The stronger `delivered_meaning_from_actual_force` uses the accepted
`bind_after_force_return_meaning` theorem. From the same complete carrier,
an actual demanded Force observation and its original `traceForm` Return,
it derives completed world Meaning at the delivered state's own Event.
Old-world membership and returned-value membership are conclusions of that
whole-carrier observation, not extra premises of this theorem.

`delivered_background_from_actual_force` does the same in the original
hole-relative Background semantics. It uses Background's own carrier,
trace and hereditary clauses and an explicit hole-future condition. It does
not convert completed Meaning or a finite Checking result into arbitrary
recursive-candidate membership.

Both theorems retain actual Force incidence, original Return readout,
saved-provider/alias bounds, compatibility, event coherence and independent
world guards. The module does not derive all of these from arbitrary source
syntax, nor identify arbitrary `PairData` with executor events.

## 6. Verification and remaining parent obligations

Pinned Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Lake
5.0.0-src+eb6cafb were used. The final direct checks and the 37-job focused
integration build passed at `-j1 -M1024` with no diagnostics.

`AuditOriginalClosureProgress.lean` prints complete types and transitive
axioms for all **38 originating theorem constants** in this module,
including private/generated declarations, and all **323 theorem constants**
in the six-module integration surface. Its exit was 0. The only admitted
axioms are the actual subsets of `propext`, `Classical.choice` and `Quot.sound`;
no project axiom, `sorryAx`, native evaluation trust or checker bypass occurs.

The combined audit initially exceeded its 1 GiB memory cap. Splitting command
scopes alone did not eliminate that combined import/census cost. Only this
audit was rerun with `-M2048`; all proof modules and the project configuration
retain `-M1024`. An earlier audit-script type-inference error was repaired by
making its counter type explicit. These were checker infrastructure failures,
not mathematical counterexamples or accepted unfinished proofs.

Material elaboration repairs are retained in
`/tmp/yulang-return-world-01.log` through `-08.log`: implicit sort/type
parameters, record-update layout, preserving the `packet_address` rewrite,
dependent parent-lookup case splitting and an unnecessary `dsimp`.
The final successful standalone log is `-08.log`; the successful complete
audit is `/tmp/yulang-original-progress-audit-04.log`.

For the original whole-language theorem the first remaining obligations are
the genuine catalogue/readout interpretation, full native Force registry
preservation, original recursive callable realization (L4), primitive and
future-event interpretation, the complete source/native success bridge and
the concrete original `SourceProblem`. Principality's whole scoped order and
the complete native inference transition relation are independent open goals.
None is replaced by the new local constructions.
