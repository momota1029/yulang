# Physical scoped-flow and relation interning

Date: 2026-10-26. Producer packet: `RELATION-INTERNER-READBACK`, r4.
Baseline: `6b26127636b988614c676270c37a428464948f37`.
Status: constructed and checked with the pinned Lean kernel; fresh independent
review is required. The original complete native correspondence and
`SourceProblem.InferenceSoundness` remain OPEN at their other owners.

The proof is [NativeRelationInterner.lean](lean/YulangClosure/NativeRelationInterner.lean).
Its only direct project import is the accepted `NativeValuePorts`. The latter's
SHA-256 is `f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa`.
No downstream or concurrently changing proof module is imported. The final
producer manifest records the new source and all 25 fixed input hashes.

## 1. Original seam and resulting supplier

Section 7 of the accepted
[Value-port construction](2026-10-26-native-value-ports.md) leaves its Arena's
decoded complete relation keys to be connected to the native `ScopedFlowId`
and `RelationKey` interner. A chosen full-key reflection function would not
close that seam. Nor would assuming that a returned physical relation ID
happened to equal a selected Arena result.

This packet constructs the physical operations, including their materialized
maps, error effects and rollback, and derives that connection. Its principal
entry point, `YulangClosure.NativeRelationInterner.native_ok_refines_arena`,
starts with a constructed `NativeHistory n` and the actual condition
`(n.call resources key).2 = .ok id`. It names no matching output witness.
Writing `actual := (n.call resources key).1`, the conclusion is:

1. The complete input key satisfies the existing `NativeValuePorts.Allowed`
   guard and its Context passes the actual length assertion.
2. `actual.store.readback id = some key`, using the physical stored
   `RawKey` and the actual scoped-flow table.
3. `(n.store.arena contexts transformers).relation key` is exactly
   `(actual.store.arena contexts transformers, id)`.

Thus the source success supplies the same complete key, output Arena and raw
relation ID as the existing accepted Arena constructor. Map coherence and key
reflection are derived inside the construction, rather than supplied to this
entry point. The full theorem types and every originating axiom dependency
are retained in the census described below.

## 2. Exact native owners, read sets and mutations

The pinned native owners are
[candidate_context.rs](../../crates/yu-solver/src/candidate_context.rs) and
[candidate_source.rs](../../crates/yu-solver/src/candidate_source.rs).
All locations below refer to those retained source snapshots.

| Native owner | Reads and source order | Represented writes and proof owner |
|---|---|---|
| `ScopedDemand`, Context 267–273 | Original call, use instance, root Term, output scope and input route | The existing five-field `ScopedDemand` is retained intact inside `Flow`. |
| `ScopedFlow`, `ScopedFlowId`, `RelationKey`, 275–296 | Transformer, optional complete demand; physical key contains pair, Context, optional sources and flow ID | `Flow`, `RawKey`, `Entry.key`; no endpoint-only equality key. |
| `assert_context`, 2786–2791 | Identity or Context index at most current Context vector length | `Resources.contextCount`; `Failure.contextAssertion` denotes the native assertion/panic cut, not an `Err` returned by Rust. |
| `relation_with_scoped`, 3062–3071 | Context assertion; nonidentity Effect self-relation; Value transformer; Effect demand | `guards`, `guards_exact`, `Native.call`; failures precede any projected mutation. |
| Flow default and reuse, 3072–3073 | Default full flow first; then existing `scope_flow_keys` lookup | Default ID 0, existing nondefault ID unchanged. These paths bypass enabled, capacity, work and allocator checks. |
| Fresh flow, 3075–3080 | Enabled flag, 4096 records, inventory charge, vector reserve, map reserve, checked one-based ID | `Native.internFlow`, `Native.charge`, `Native.addFlow`; append full flow and insert its exact map entry. |
| `ScopeInventory::charge`, Source 216–221 | Checked addition, then 65,536 work limit | A successful charge updates `work_used` before later reservations. Failed charge leaves it unchanged. Other successful charge callers are represented by `NativeRun.inventory`. |
| Relation reuse, Context 3082–3085 | Complete physical key lookup after the flow phase | `Native.internRelation` returns the old ID before conversion or reservation. |
| Fresh relation, 3086–3093 | `u32` conversion of vector length; relation, key-map and pair-map reserves | Insert pair head and retain its previous value, append physical record, insert full key. `Native.addRelation` uses the actual materialized pair map. |
| `scoped_flow`, 2880–2882 | Relation lookup, zero/default branch, otherwise `scope_flows[id-1]` | `Store.flowAt`, `Store.decode`, `Store.readback`. Missing physical slots produce `none`. |
| Checkpoint, 2047–2077 | Relation-vector length, with other unrelated checkpoint fields | No flow-vector or flow-map frontier is captured. |
| Relation rollback, 2148–2155 | Drain relation suffix in reverse; remove each complete key; restore its saved pair head or remove it | `undoKeys`, `undoHeads`, `Native.rollback`, `native_cancel_maps_and_flows`. Flow vectors/maps and work remain at the attempted cut. |

`exhausted()` at Context 1319–1321 is `IdentityExhausted`. The proof's
`Failure.exhausted` denotes that outcome. `receiptMismatch` denotes the source
`ReceiptMismatch`. No exact diagnostic wording is introduced.

The mutation search found the production flow append in this constructor and
no production truncation, removal, clearing or popping of `scope_flows` or
`scope_flow_keys` in this rollback. Test-only corruption hooks at 1976–1988
are outside the production constructor history; they are not silently treated
as valid native constructors.

## 3. Complete physical data and finite-map semantics

`RawKey` has precisely the physical fields needed here: `pair`, `context`,
`sources` and `flowIndex`. `Pair` is the existing Value/Effect sum, so native
endpoint constructors, polarities, term identities, tuple arities and row
identities remain distinct. `sources : Option Nat` preserves both `none` and
`some 0`, as well as every other source-set ID.

A `Flow` retains its transformer and the entire optional demand. Default is
exactly transformer 0 with no demand. A nondefault record is stored at zero-based
vector position `i` and receives physical flow ID `i + 1`; zero always decodes
to the default flow. `decoded_demand_fields` explicitly exposes all five demand
fields from a successful physical decoder read.

The map model uses the ordinary mathematical semantics of a finite exact-key
map: empty lookup returns `none`; `put m k v` changes precisely key `k`;
`erase m k` removes precisely `k`; `restore` puts the saved previous value or
removes the key. Hash collisions do not identify different keys: native derived
`Eq`/`Hash` retains the whole key, and equality is the complete object equality.
This packet does not verify the Rust standard library's hashing or allocator
implementation. These are explicit standard container semantics, not an
arbitrary application-specific lookup or safety oracle.

There are two proof layers. `Store` reconstructs each finite interner cache
from its actual vector, proving `cache_append`, `cache_remove_fresh`,
`native_flow_map_insert` and `native_relation_map_insert`. `Native` additionally
stores the materialized `flowCache`, `relationCache` and `pairCache`.
`Native.internFlow`, `Native.internRelation` and `Native.call` read those
materialized maps. Their allocation constructors execute the corresponding
map updates, and their rollback executes the actual reverse removals/restores.

`Coherent` states agreement between the two representations, but the final
entry point does not assume it. `native_history_refinement` constructs it from
empty maps and the actual transitions, including cancellation. Consequently
`native_stored_complete_key` turns a successful materialized relation-map
lookup into the actual vector slot, physical key, complete decoded origin key
and full readback. The derived cache is not substituted for a stale native map
without this constructor proof.

## 4. Ghost provenance and allocation lifetimes

`Entry.origin` is an immutable ghost copy of the complete key passed to the
allocation constructor. `Entry.birth` is a monotonically increasing ghost
allocation number. Neither is consulted by the physical lookup, guards,
resource checks, map insertion, pair-head decision or rollback. Their values
are constructed from that same allocation input and clock; callers do not
provide a proof of desired completed behavior.

The separate decoder reads only the stored physical fields and flow vector.
`stored_key_decodes` proves that it recovers the ghost origin. This proof uses
the constructed flow interner and full physical key equality. It does not
define decoding as reading the ghost, nor assume origin equals a desired
output. `physical_complete_key` then proves the exact raw-key/origin equality
correspondence needed to compare cache indices with the accepted Arena.

Old successful flow meanings remain stable under append. Existing relation
readbacks remain stable throughout a forward `Run`, and
`same_id_across_forward_calls` derives full key equality when a later successful
call returns the same still-live raw ID. At one cut, `same_id_full_key` is the
corresponding decoder functionality result.

Cancellation changes the lifetime boundary. It removes the new relation
suffix while keeping the allocation clock, flow records, flow map and charged
work. A retry can allocate a new relation at the same raw vector position.
`retry_birth_newer` and the concrete retry witnesses record the new birth;
`raw_id_not_global_identity` computes different complete source-set keys at
raw ID 0 before and after cancellation. The theorem does not assert permanent
relation identity across such cuts.

Retained flows preserve their raw payloads. Semantic interpretation of the
transformer and the demand's source identities still belongs to their source
and transformer owners. This packet does not infer that every integer inside
a retained flow is a timeless semantic object merely because the flow vector
itself persists.

## 5. Exact success, rejection and partial-write paths

The executable `Native.call` represents every source branch of the assigned
interner. `guards_exact` proves that its successful guard result is precisely
the existing `NativeValuePorts.Allowed` condition. In particular, Value demand
is allowed here when the transformer is identity; the later Function-demand
root check is not incorrectly moved into relation interning. For an Effect
with both a nonidentity self-relation and a deferred demand, the first guard
returns exhaustion, matching the source order.

A nondefault existing flow is reused even when scoped mode is disabled,
4096 flow records already exist, work is exhausted, or the reservation results
would fail. Existing relation lookup likewise precedes `u32` conversion and
all three relation reservations. `default_bypasses_resources`,
`existing_flow_bypasses_resources` and `relation_reuse_before_reservation`
expose those actual ordering facts.

A fresh flow first charges one work unit. If the flow-vector reservation,
flow-map reservation, or checked one-based index subsequently fails, the work
charge remains and no flow record has been appended. After both reservations
and the checked index succeed, the flow and its map entry are appended before
the complete relation-key lookup. Any later relation ID conversion or
reservation failure leaves that flow and charge in place. No failure path
here publishes a relation record before all relation reservations succeed.

`Resources` records the actual `scoped_enabled`, current Context count,
platform `usize` maximum and the outcomes of the five distinct `try_reserve`
calls. Its default `usizeMax` is `2^64 - 1`, corresponding to the pinned
x86_64 target; the definition keeps the maximum explicit. These fields must
be instantiated with the native values/results at the corresponding source
cut. A boolean reservation result is not a promise that allocation succeeds.
Unused later results have no effect when an earlier guard returns.

The projection models the `work_used` counter, including successful external
`ScopeInventory::charge` interleavings, but not inventory region vectors,
heap capacities, retained byte counts, scratch peaks, allocator ownership or
exact allocation failures. Successful reserve calls may change capacities;
those changes are deliberately outside this projection and are not claimed
to roll back. Failed external inventory calls are projected stutters because
they change no represented field. No whole-inventory theorem is asserted.

`native_history_bounds` derives the native 4096 flow-record limit, the
`2^32` relation-vector length bound and the 65,536 work bound. The stronger
successful-ID conclusions are `native_success_u32` (`id < 2^32`) and
`native_nondefault_flow_range` (`0 < flow ID ≤ 4096`, with actual decoder
readback). These are consequences of existing native availability guards,
not new restrictions on the language or inference algorithm.

## 6. Rollback through the same history

`RelationTrace` retains the actual fresh-key condition and the previous pair
head at each appended record. Its induction proves the reverse key removals
and pair-head restorations for an entire appended suffix. Thus restoration
is derived from actual insertions and saved previous values; it is not
assumed as generic state equality.

`NativeRun` includes actual calls, including errors, and guarded inventory
charges. `NativeHistory` starts from the native default state and commits or
cancels those runs. `native_run_refinement` and `native_history_refinement`
connect the same materialized history to the vector construction. Cancellation
uses the saved relation frontier, not a saved flow frontier that the Rust
checkpoint never captured.

`native_cancel_maps_and_flows` proves all of the distinct conclusions at that
same cancellation cut:

- relation vector, full relation-key map and pair-head map equal their saved
  values;
- flow vector and flow map equal their current attempted values;
- charged work equals its current attempted value.

The current allocation clock is likewise retained. Old saved relation keys
still decode correctly because flow meanings are append-stable. Removing the
relation suffix therefore does not require restoring the entire state or
reusing canceled relation births.

## 7. Concrete witnesses and parent integration

The checked witnesses compute actual definitions with the ordinary Lean
kernel. They include a Value key carrying source-set ID 11 and demand
`(originalCall=5, useInstance=6, root=7, outputScope=8, inputRoute=9)`.
The first allocation yields flow ID 1 and relation ID 0. Cancellation leaves
the flow and charge, and a retry with scoped mode disabled and both flow
reservation flags false reuses that flow while allocating relation ID 0 with
birth 1. Separate witnesses cover a later relation-map failure, an earlier
flow-reservation failure after charging, every guard class, and a demand
whose changed original-call field requires a distinct full key.

`physical_maps_retry_exact` and `physical_partial_failure_exact` execute the
materialized-map implementation itself. Their histories are constructed by
`physical_first_history`, `physical_cancelled_history` and
`physical_retry_history`. The examples are falsifiable evaluations of the
source ordering, not premises of the general proofs.

For the parent, apply `native_ok_refines_arena` at the actual
`relation_with_scoped` call used by Value child admission. It supplies the
accepted Arena relation step and exact raw ID, retaining every pair, Context,
source, transformer and demand field. The primary's next integration owner
must align that call's inputs and intermediate Context/transformer arenas
with the complete `NativeValuePorts.admit` computation and the driver's
admission/enqueue history. That alignment is not performed by editing or
assuming a downstream module in this packet.

Other precise remaining owners are the concrete Rust event interpretation
for a whole execution; the actual Context vector/count and source/transformer
object meanings at each call; complete Value/Effect semantic dispatch and
diagnostic acceptance; and the original shared source witness. Optional
`source_drain_completions` storage is not used or assumed. No theorem here
claims source typing, terminal inference success, or closure of the original
whole-language soundness obligation.

## 8. Verification and frozen receipts

The producer used an isolated project/cache and the already installed native
Lean 4.35.0 toolchain at
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Lake reports `5.0.0-src+eb6cafb`; Lean reports 4.35.0, x86_64-unknown-linux-gnu,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
All calls used `LEAN_NUM_THREADS=1`, `-j1`, `-M1024`, a 120-second total check
bound, `PYTHONDONTWRITEBYTECODE=1`, and the owned `TMPDIR`.

Checks 07, 10 and 11 pass. Final check 11 builds the actual module and prints
the complete origin census, with zero warnings. There are **588 originating
declarations, 244 theorem constants, 109 named source theorem roots,
18 private declarations and 12 private theorem constants**. Every type is
printed without elision, and every originating constant has its actual axiom
list. Among theorems, 97 use no axioms, 65 use only `propext`, 35 use
`propext` and `Quot.sound`, 44 use those two plus `Classical.choice`, and
3 use only `Quot.sound`. No project axiom, proof hole or unchecked native
evaluation bypass occurs in the checked build.

The complete census is 397,560 bytes, SHA-256
`9b71e6d2aa0154f6949f71a50d56ed8d1c321576ad24908c309f95f50e4c55be`.
Final source SHA-256:
`1fd7ece6c6a7c6df7159efaebaec585b78a9e8513e9b10e6a3fb4d472b577d3a`.

Eleven of twenty focused check slots were used. Check 01 stopped before Lean
at an input-snapshot path selection error and has no measured duration; its
original zero-duration sentinel is explicitly excluded from timing totals.
The remaining checks total 91.676 measured seconds; the longest is 26.518
seconds. Final check 11 took 5.312 seconds with maximum child RSS 1,009,356 KiB.
Every failure, source snapshot and command receipt is retained. Earlier failed
elaborations concern namespace/reserved-name syntax, library lemma names,
indexed induction, equality normalization and the explicit local Result type;
they were repaired without weakening statements or suppressing linters.

All reproduction scripts, exact input snapshots, source versions, commands,
resource receipts, the 109-root list and complete origin inventory are under
`/workspace/scratch/f98087c7ac1a/relation-interner-r4/`. The
[producer handoff](../../tasks/agent-loop/inbox/20261026-native-relation-interner-r4.md)
and `freeze.json` identify the final hashes and writes-stopped cut. Independent
review and primary acceptance are required before integration or publication.
