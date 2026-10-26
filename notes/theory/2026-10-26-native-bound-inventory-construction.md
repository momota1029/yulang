# Native physical-bound inventory and execution provenance

Date: 2026-10-26
Status: executable adapter verified; paper correspondence argument constructed; independent review pending
Parent: original source inference A/B, not a replacement source language
Baseline supplied by primary: `bf81a1bd444b3bcbecca6b754ea6fb603262f368`, branch `yulang3`
Author: `/root/native_inventory_construction`; no descendants

## 1. Outcome and exact scope

The test-only `candidate_native_inventory_tests.rs` constructs an inventory from
an actual borrowed `InferenceSession`. Its domain is every physical value/effect
bound vector, including vectors on nonrepresentative rows. Each entry keeps the
raw owner, eight-way lane, physical index, raw endpoint, exact emission IDs,
current canonical owner/endpoint, and oriented comparison. It does not identify
duplicate physical slots merely because their canonical comparisons agree.

The adapter also exposes the actual retained admission, emission, snapshot,
transport, replay-recipe and dependency records, live replay/restoration
operations, original extrusion pairs, groups and all later reuse records. It
reads structural terms through `TermView`, including all four Function ports,
record labels/optional bits, variant alternatives/payload order and tuple order.
Effect endpoints retain their actual contribution/view/member IDs and their
owning operand records. This is an extraction of finite native data, not an
interpretation of rows as semantic graph nodes.

The original claim remains the one in
`2026-10-13-intrusion-source-preservation-proof.md` §1, with qualification
corrected by `../design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. It ranges
over every supported original source program and lawful finite construction
history, preserving original source scopes, one shared witness, complete Call,
effects, soundness, required coverage and normal inference behavior. Nothing
in this inventory changes that domain or establishes native-success soundness.

## 2. Concrete finite address space

For a fixed native session S, let `Addr(S)` consist of triples `(owner,lane,i)`.
An owner is a value-row or effect-row ordinal within the corresponding physical
row vector. A lane is one of the following eight cases, and i is in range for
that exact owner's exact vector. The owner kind must match the lane kind.

| Lane | Actual vector | Side | Stored entry | Normalized inequality |
| --- | --- | --- | --- | --- |
| ValueLowerRow | `bounds[r].direct_lower_rows` | positive | value row | entry ≤ r |
| ValueUpperRow | `bounds[r].direct_upper_rows` | negative | value row | r ≤ entry |
| ValueLowerAtom | `bounds[r].exact_non_variable_lowers` | positive | value endpoint | entry ≤ r |
| ValueUpperAtom | `bounds[r].exact_non_variable_uppers` | negative | value endpoint | r ≤ entry |
| EffectLowerRow | `effect_bounds[r].direct_lower_rows` | positive | effect row | entry ≤ r |
| EffectUpperRow | `effect_bounds[r].direct_upper_rows` | negative | effect row | r ≤ entry |
| EffectLowerAtom | `effect_bounds[r].exact_non_variable_lowers` | positive | effect endpoint | entry ≤ r |
| EffectUpperAtom | `effect_bounds[r].exact_non_variable_uppers` | negative | effect endpoint | r ≤ entry |

Here “Atom” is the native lane name, not a mathematical assertion that its
endpoint is primitive. A Function, record, variant, tuple or contextual effect
operand is retained in that lane. The native vector type itself permits a row
endpoint there; the extractor preserves such an entry instead of silently
filtering or reclassifying it.

**Finite inventory proposition.** For every finite well-formed native session,
`inventory(S).physical` has exactly one entry for each address in `Addr(S)`;
its raw key equals the addressed native readback, and its normalized comparison
has exactly the orientation in the table. Representative collapse changes
neither the address nor multiplicity.

**Proof from the actual adapter loops.** The two outer loops are Rust
`iter().enumerate()` over `bounds` and `effect_bounds`. Thus each raw physical
owner occurs once, without an `is_representative` filter. For each owner the
four explicit append calls select the four actual vectors and distinct lane
constructors. Each append uses that vector's `into_iter().enumerate()`; it
emits precisely indices `0..len`, and inserts exactly the iterated endpoint.
Two outputs with equal slots must have equal kind, owner, lane and local index,
so they come from the same loop iteration. Conversely every valid address
selects one outer loop, one append call and one inner iteration. Its readback
is therefore present exactly once. Normalization applies the native
`canonical_extrusion` only to a second copy of owner and endpoint and then
orients according to side; the raw key and physical slot remain unchanged.
The actual row allocators enforce the `u32` ordinal bound used by the adapter.

The validator independently sums the eight actual vector lengths, requires
this cardinality, rejects duplicate addresses, and checks each address against
a separate eight-case raw lookup. Validity, injectivity and equal finite
cardinality imply coverage. This is why deleting one slot fails even when
another slot has an identical bound value. This argument concerns data
extraction; no satisfiability or typing predicate occurs in it.

**Termination and cost.** This is a total finite mathematical enumeration on well-formed representable
stores. The allocating test adapter additionally requires available resources;
it is not a claim of infallible allocation at arbitrary input size. The loops
are finite. Physical-vector enumeration and emission indexing alone take
expected O(B+E+R) work for B physical entries, E retained emissions and R rows,
excluding representative traversal. The whole extractor additionally visits
structural endpoints from every retained relation, including repeated handles:
the number of distinct reachable terms does not bound those root occurrences.
It traverses reachable child arrays, copies retained dependencies, enumerates
parents/groups/reuses/source sets, computes source-event qualification, and
traverses and sorts the live replay/restoration maps. Canonicalization incurs
the actual representative-forest traversal cost. These additional costs are not
included in the physical-enumeration bound. The adapter allocates a read-only
research snapshot; it is not installed in production inference. The adversarial
validator deliberately performs a slower per-slot emission join and is not a
production complexity proposal.

## 3. Constructor correspondence and retained evidence

The eight cases exactly match
`candidate_extrusion.rs::candidate_insert_bound_with_evidence` and
`candidate_physical_slot_bound`. The constructor first canonicalizes owner and
bound, chooses the lane by kind, polarity and direct-row versus other endpoint,
then records the old selected-vector length as the physical index immediately
before the push. Its subsequent native readback must equal the expected key
or it returns `ReceiptMismatch`. `evidence_emit` records that slot and the
`ConstructorAfterAppend` readback with the actual admission identity.

Thus a completed successful invocation supplies a concrete address/readback
witness for its own new slot. The adapter's emission join is by exact slot,
not by canonical endpoint equality or relation equality. It borrows the whole
emission vector as well, so an emission without a current matching slot is not
erased from the evidence surface. Missing relations and every
`EvidenceCoverage` gap are preserved. In particular `FreshUse` explicitly
retains `ReplayUseAntecedentsNotRetained`; inventory does not convert that bit
into a semantic proof. Source-drain completion records are also preserved as
actually retained; `record_source_drain_completion` can omit an observation if
its reservation fails. The adapter does not infer a missing completion record
from a successful return.

This local constructor statement does not assert an unconditionally global
bijection from every physical slot to every admission. Admissions and physical
emissions are different stages; direct copied-fiber admissions can exist
without a new physical slot, and failed/provisional states need their actual
transaction disposition. `apply_value_task` and `apply_effect_task` dispatch to
the candidate owners when the candidate graph exists; their separate legacy
physical writers must not be mistaken for this candidate constructor.

`merge_candidate_rows` reads both source sides using the actual opposite-side
enumerator, inserts each copied bound at the destination and retains
`ParentCopy { parent_index }` transport. It deliberately leaves source vectors
intact, then changes the representative and canonicalizes bound provenance.
Consequently a representative-only physical snapshot is incomplete. The
adapter retains source and destination addresses, each actual parent index,
and the separate current representative map.

## 4. Ordered replay and the trace distinction

`candidate_opposite_count(owner,p)` selects upper vectors for positive p and
lower vectors for negative p. `candidate_opposite_bound` reads the direct-row
vector first and then the structural vector at offset `direct.len()`. It
canonicalizes the result. The same total count does not identify the same
physical slot after a direct-vector append or representative change.

`candidate_replay_bound` snapshots the total count and emits a comparison at
each loop index. Both it and bound restoration construct ordered
`(lower_input,upper_input)` keys independently of insertion direction. In
`candidate_context_begin_replay`, new lower fibers meet all upper fibers;
old lower fibers meet only newly admitted uppers. Each generated dependency
retains child relation, lower relation, upper relation and both ordered bound
keys. The operation separately retains task, frozen heads/prior heads,
incoming-use flag, ordered child vector and queue/consumption/wait frontiers.

The extraction borrows all retained dependency/recipe records and all *live*
operation records. It does not claim a final snapshot contains all completed
operation identities. `acknowledge_replay`, `advance_restoration`,
`retire_restoration` and route commit can reclaim finished records. Rollback
can restore the allocation counter and discard provisional records.

This erasure is not itself a soundness obstruction. A proof of an actual finite
run may carry a ghost trace indexed by the concrete transition occurrence and
route checkpoint, recording each operation at creation, each physical read,
child transfer, child acknowledgment, parent advance, commit or rollback. At
an append/replay step extend the ghost list with the actual arguments and
returned identities. At reclamation keep the ghost event while projecting away
the runtime record. At rollback cancel the speculative segment or retain its
explicit abort marker; a retry gets a new ghost transition identity even when
its runtime ordinal is reused. This is an event-by-event construction, not a
new runtime log or a proposed hot-path data structure.

A finite sequence of actual transitions therefore has a finite faithful event
list even with runtime erasure. What remains unproved is that its comparisons,
child completions and retained equalities satisfy the semantic history needed
by `SimpleSubLatticeGrowingInference`. In particular saved-count/live-index
restoration is not promoted to a theorem that every *original* opposite slot
was consumed. A child may append a direct entry before an old structural one;
the exact correspondence must follow the actual reads and apply the appropriate
compensating-propagation result. The independently reviewed
`../progress/2026-10-13-restoration-live-index-pair-audit.md` already derives this
selected behavior; it is not a newly discovered compiler failure. The reviewed
`2026-10-13-restoration-temporal-coverage-proof.md` proves whole-block coverage
for its explicit all-local Value, equal-level, identity-context specialization.
Those premises are retained; the full shared/effect/contextual block remains a
separate owner. No duplicate shifted-index fixture was written or run here.
Empty worklists or a zero diagnostic count do not prove that fact.

## 5. All original and later qualification identities

`retain_extrusion_parent` appends actual copy, parent, polarity, target,
original source-set ID, processing comparison and occurrence. Original
qualification adds that exact parent-vector index to pending work.
`finish_candidate_extrusion` forms the actual half-open parent-index group and
records its occurrence/output association. Original parent source IDs are
immutable.

`recapture_candidate_extrusion` looks up only groups associated with the actual
reused output. For each previously unseen `(group,sources)` it allocates a new
occurrence and appends a `Reuse`. If that source set qualifies and the group
was not already active, it activates the group and queues precisely its
`start..end` parent indices. Therefore original `Parent.sources` alone is
insufficient. The adapter exports every parent and every group/reuse tuple,
all referenced source sets, and the actual current source qualification bits.
No group is filtered by final equality or by its original qualification.

For a completed uninterrupted group history with fixed source qualification,
its activating witness is constructionally either its original qualified
source set or the first qualifying recorded reuse of an initially unqualified
group. The loop's `!activated` guard makes the later activation unique. Rollback
truncates reuses/groups and reverses newly recorded activations, so the same
argument applies to the committed prefix. This does not infer source typing
from qualification: the original birth-level Value graph still owns that rule.

## 6. Capture, fresh use and structural interpretation

`Capture::expand_row` explicitly returns when the captured row is not local.
Those mutable bounds remain in the session; they are included by the physical
inventory but absent from that scheme graph. Scheme capture cannot serve as a
whole-store inventory.

`prepare_candidate_fresh_use` computes one canonical-row map. It iterates
captured rows, obtains their current representative, reuses the first stored
image when present, and otherwise applies the exact stored-local, level and
non-generic guard. The immutable `FreshUse.rows`, retained term/context/evidence
maps and actual context-use identity then feed `begin_candidate_fresh_bound`.
The latter maps both endpoints, preserves bound kind/side, constructs the
actual source-to-fresh transport and starts restoration with the imported
antecedent. A proof cannot replace this map by independently chosen per-bound
renamings. The adapter borrows every retained module, local, operator and member route,
including their actual row vectors and nested FreshUse maps. Future source
correspondence must consume these concrete routes; it must separately account
for any live partial continuation at the selected cut.

The Function extraction order is `(argument, argument_effect, result_effect,
result)`. Native extrusion flips polarity on the first two ports. Native
comparison uses upper-to-lower on those two ports and lower-to-upper on the
last two. Retained `FunctionPort` evidence labels the operations `Swap, Swap,
Preserve, Preserve`. Term readback retains these four distinct fields; it does
not reduce a Function to argument/result alone.

A semantic row assignment is still needed. Both upper and lower physical sides
must normalize into one directed inequality relation: a level-based native
row-row constraint can reside on either side. The model lane must not collect
only one row's lower vectors. Native endpoints do not contain explicit
union/intersection constructors; accumulation in the bound store is the
source of that lattice structure. Open rows, width/presence, contextual effect
operands, unguarded row cycles and all original Call/source witnesses remain
semantic correspondence obligations. A raw ordinal, extracted term handle or
borrowed native record is not by itself a `Regular.Node` interpretation.

## 7. Verification and parent application

The assignment handoff records actual toolchain commands, bounded test results,
all failures, exact frozen hashes and write cessation. No Lean module or theorem
is supplied by this packet; no Lean build, axiom audit or generic-list theorem
is claimed as native correctness. The finite address bijection above is a
paper argument tied to the eight concrete extraction loops. Its executable
falsifiers compare against actual producer data.

The final focused native test passed on the frozen 343-line adapter. Its
post-merge snapshot contained 18 physical slots, 18 emissions, 10 reachable
terms, 76 dependencies, 6 original parent/copy pairs, one group, zero reuses
and intrusion generation 6. All eight lanes were nonempty. The native
`candidate_opposite_count`/`candidate_opposite_bound` API agreed with the
extracted direct-before-exact order before and after aliasing. Removing a
physical entry, swapping the Function value ports, swapping its effect ports,
and removing a Replay dependency each caused the expected independent
readback/coverage failure. Real `ParentCopy` transport and raw/canonical
distinction were present.

This is one deterministic native-constructor fixture, not a complete original
source execution. Its source self-reference supplies a real qualification
event, while the test creates the typed rows and bound inputs through native
constructors. It does not call `finish_candidate` or claim native no-error
source acceptance. Zero reuses describes only this fixture; all reuse records
are exported without filtering, and no all-history theorem follows from that
zero. The evidence includes live queued replay operations; complete restoration
or all use families are not claimed to have been exercised.

Two earlier 120-second runs timed out during compilation. A separately
authorized final run used the identical source bytes, same private target,
locked/offline dependencies, debug info disabled, incremental compilation
disabled, one build job and test thread, a 4 GiB address-space bound and a
240-second process-group timeout outside the sandbox. It completed in
52.957 seconds (test body 0.01 seconds), exit 0. The compiler reported the
same 19 existing yu-solver warnings; none named this new module. Prior
timeouts are preserved and are not counted as acceptance.

This result removes the need to guess the native physical universe or recover
provenance by endpoint equality. It supplies a complete addressed store and
explicit retained evidence for the model/history construction. It does not
supply final decision acceptance, saturation across changing replay frontiers,
all-history source publication, full original Call, source principal coverage,
or progress/termination. Those original parent gates remain OPEN.
