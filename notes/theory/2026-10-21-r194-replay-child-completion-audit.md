# R194 — Replay child completion and Capture coverage audit

Status: source-qualified evidence audit; theorem preservation remains open.

## Exact R187 local Apply readback

The offline readback traversed 18 source occurrences for the `outer` definition.
All 18 had complete source facts, with no incomplete occurrence. It found one
completed source-drain receipt carrying a Replay acknowledgement:

```text
source="finish", occurrence=22, slot=0, relation=2,
incoming_relation=Some(2), replay_ack=Some((61, 0)),
created_seed=2, selected_relation=2
```

That receipt belongs to relation 2. It does not name either local Apply Replay
child relation 59 or 96, and its operation/index acknowledgement `(61, 0)` is
not bound by the retained readback to either target child.

For bridge Apply occurrence 13, the retained local source origins are slots
0/1/2 at relations 58/65/67. For relay Apply occurrence 18, they are slots
0/1/2/50/51 at relations 95/110/112/138/142. These are direct source drains:
their `incoming_relation` and `replay_ack` are `None`. The readback reports no
Replay-child completed drain receipt and no parent-delivery receipt for either
Apply view. The source occurrence set contains zero origins whose incoming
relation is target child 59 or 96.

The earlier R191 join identifies the target links:

| Local Apply | source relation | Replay child | parents | ordered Replay input |
| --- | ---: | ---: | --- | --- |
| bridge, Apply 13 | 58 | 59 | 55, 58 | lower `ValueRow(13) + <= PositiveFunction(Term 296)`; upper `ValueRow(13) - <= NegativeFunction(Term 306)` |
| relay, Apply 18 | 95 | 96 | 92, 95 | lower `ValueRow(18) + <= PositiveFunction(Term 324)`; upper `ValueRow(18) - <= NegativeFunction(Term 338)` |

## What the two completion owners establish

`start_typed_drain` stores a `SourceDrainReceipt` on the drain frame and, when
the origin matches, on that source origin. The receipt records the incoming
relation, optional Replay acknowledgement, selected relation, seed, task,
cause, and origin index. At terminal drain completion, the solver copies that
receipt into `source_drain_completions` with `completed=true`. The retained
completion list therefore attests to completion of that exact typed drain when
the exact receipt matches.

Replay parent delivery has a separate owner. `ReplayOperation` retains its
child relations and a `waiting_child` state. The Replay child step checks the
typed-drain frame against the operation/index acknowledgement, waits for the
terminal owner to publish `Ready`, verifies the queued/consumed counts, and
then returns `Delivered` while setting the wait state to `Idle`. The driver
reports `Complete` only after retirement and an idle child state. The bound
restoration consumer checks this outcome (or the returned state) before
advancing restoration.

Those runtime checks show how delivery is authorized during execution; they do
not turn a child completion receipt into a durable receipt of parent delivery
or retirement. Retired and idle Replay operations can be removed. The
`ReplayDrainObservation` carrying a `DriveReturn` is test-only. Thus the
observed relation-2 receipt proves one unrelated child drain completed, while
the exact R187 source readback does not provide a source-qualified completion
receipt for children 59/96 or a durable parent-delivery receipt for either
target. This is a limitation of the retained target view, not a proof that no
such event occurred anywhere in execution.

## Capture coverage gaps

Coverage bit positions come from `CoverageGap` declaration order:

| Bit | Gap |
| ---: | --- |
| 1 | `MissingBoundRelation` |
| 2 | `MissingBoundGroup` |
| 4 | `MissingPhysicalEmission` |
| 8 | `MissingAntecedent` |
| 16 | `ProcessingAntecedentsUnavailable` |
| 32 | `OrdinarySeedAuthenticationUnavailable` |
| 64 | `ReplayUseAntecedentsNotRetained` |
| 128 | `MissingOriginAssociation` |

Every reported snapshot for bridge relations 45 and 19 and relay relations 74,
60, 72, 73, 56, 57, and 62 has mask 56, which is bits 8+16+32. Relay relation
53 has mask 120, which is bits 8+16+32+64. Therefore the nonzero bits observed
in these snapshots name missing antecedent, unavailable processing
antecedents, unavailable ordinary-seed authentication, and (for relation 53)
unretained Replay-use antecedents. No other coverage bit is set in these
snapshot rows. The admission constructor assigns the first three gaps to
`OwnerEmission`/`ExtrusionLink`; `FreshUse` propagates antecedent coverage and
adds `ReplayUseAntecedentsNotRetained`.

These are explicit evidence-coverage gaps. They block deriving a full Capture
fiber from these snapshots; by themselves they do not establish a fiber
mismatch or refute the preservation theorem.

## Exact remaining premise

The R187 bridge/relay readback establishes direct source origins and ordered
Replay inputs but does not join the local Apply source facts to a completed
typed drain for Replay children 59/96, then to parent acknowledgement and
retirement. The one retained Replay-acknowledged receipt is for relation 2 and
cannot fill that premise. Capture snapshots also omit the derivation lineage
needed for a full-fiber claim. A source-qualified child completion joined to
the corresponding parent operation's delivery/retirement, plus complete
Capture antecedent and authentication evidence, remains the precise missing
evidence. The parent theorem, original A/B claims, source/native
correspondence, and production gate remain OPEN.

## Reproducibility

Probe source SHA-256:
`fd890235db96578ff07b76f8a4dacee63d9bc2e1a9e189244047de9703ba4884`.
Probe output SHA-256:
`ea653cfb227fba0d96d20c571e8e669623439ca96b18213ceee69b37c9fe277b`.
The temporary package and output were confined to `target/r194-readback/` and
are removed at sprint closeout.
