# R173 source-drain attribution and consumer join

Status: **implementation candidate; not compiled, executed or independently
reviewed as final code**. The R173 goal is active. All parent theorem and
production gates remain OPEN.

## Identity and scope

Proof baseline: commit `7ec64a3788175913a2be46331cf0f64c6bd5b407` and its four
original owner hashes in sprint contract revision 2. Activation metadata:
`9547edfc7`. R173 proof rev1 is baseline-only and does not apply to later code.
The implementation candidate has its own source manifest in the implementation
handoff. Do not treat that manifest as a theorem proof or production authority.

The unchanged input remains `tools/inference-playground/examples/r171-formal-name-forwarding.yu`.
This implementation adds only passive evidence to the candidate inference
observer. The source solver does not consult the evidence to choose constraints,
admission, propagation, recovery, diagnostics or publication.

## Retained drain receipt

`TypedDrainFrame` now has an optional `SourceDrainReceipt` containing the
incoming relation, Replay acknowledgement, newly created seed, selected
relation and Origin index. Its frame already owns the initial task, occurrence
and CauseId. `start_typed_drain` assigns the receipt only after
`enqueue_item` returns successfully. It copies that receipt, task and cause to
the newly created Origin, which survives normal frame removal. The Origin copy
starts incomplete; terminal drain completion marks it complete. A seed failure
or enqueue failure therefore leaves the receipt unavailable, and a failed
in-flight drain is not reported as completed. The frame's transactional undo
copy includes its receipt; route rollback truncates the newly-created Origin
with the rest of the transaction state.

Attribution matches the Origin's exact ordinal, occurrence, cause, task and
created relation. A direct source drain has no incoming relation or Replay ack
and selects its seed. A Replay child carries both an incoming relation and
Replay ack and selects the incoming relation. Unexpected combinations remain
unavailable. Relation interning does not merge invocation records because the
Origin ordinal identifies the retained invocation even after its drain frame
has been removed.

## Query joins

The source-keyed query now:

1. Selects source facts by the requested HIR occurrence/slot and retains their
   exact cause and fact.
2. Labels an Origin only when its retained drain receipt validates against the
   same exact source cause. It follows dependencies only from direct-source
   selected seeds; Replay rows are exposed as Replay and are not substituted.
3. Restricts provider routes to the same candidate graph as those direct seeds
   and to the forwarding Apply's exact callee occurrence.
4. Returns typed Capture graph summaries, relevant bound rows, snapshot source
   bound keys and coverage bits, plus every typed entry (including empty-map
   markers) from the provider route's own FreshUse maps and context-use identity.
5. Identifies a consumer relation only from a unique direct drain with the
   forwarding Apply's exact CauseId, when its selected relation is reachable
   from a direct source seed and is present in the same provider route's
   captured bounds. Multiple or missing joins remain incomplete.

Completeness flags fail closed on row truncation, missing attribution, missing
provider routes, incomplete maps or a non-unique consumer relation. The
presentation cap is applied while collecting the selected source evidence.
Hash-map iteration order in map entries is unspecified; completeness means all
entries were returned, not a stable order.

This is construction evidence for one finite fixture. It does not prove the
universal forwarding theorem, arbitrary chains or prefixes, same-assignment
preservation, Replay correspondence, or final source-to-native correctness.
The proof rev1 establishes only a baseline obstruction. A candidate-specific
proof and independent review of final source hashes are still required.

## Verification state

No Yulang2 or evaluator execution, compiler build, test, or inference probe has
run for this candidate. The R173 conditional probe remains NOT_RUN until a
fresh exact-hash review establishes that every required source-to-consumer
component is complete. The R171 source membership and candidate inference
success are reused only as the previously recorded fixture evidence.
