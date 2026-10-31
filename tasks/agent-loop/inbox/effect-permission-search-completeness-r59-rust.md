# R59 Rust Support and ancestry correspondence

Session: `EFFECT-PERMISSION-REACHED-SLOT-COMPLETENESS/20261031-R59`
Requested lane: Luna/high. Observed model/effort: UNKNOWN.
Lease used: this handoff only. `candidate_receiver.rs` remains unchanged.

## Support decoding and scheduling in `certified_lower_paths`

The search state is `LowerPathSearch { endpoint, steps, seen, use_root }`; `pending` is a LIFO `Vec`. The seed is `(root, [], {root}, None)`. Each pop charges `steps.len + seen.len + 1` using checked `usize` additions before endpoint decoding; overflow or `> SCOPED_WORK_LIMIT` returns `SearchLimit`.

Target equality is checked before decoding Support or row endpoints. Before appending a reached target path, the machine fallibly reserves one result slot; failure returns `SearchLimit`. It then appends the path and returns `AmbiguousPath` if the result count exceeds one. Thus allocation failure at the second result can precede the ambiguity error. The machine drains remaining work after a first target, so a reached read, policy, or resource error on a later branch still rejects the query.

At `EffectEndpointKey::Support(view_index)`, the decoder reads precisely `views[view_index]`; a missing view is `BoundMismatch`. It rejects any `view.tail.is_some()` as `MissingCommonEndpoint` before enumerating members, including when the allowed vector is empty. It iterates `view.allowed` in ascending ordinal order. Each member consumes one work unit before its ordinal is converted to `u32`; checked-conversion overflow yields `SearchLimit`. The member endpoint is `AnnotationMember(view_index, ordinal)`. If that endpoint is in this branch's `seen`, the branch is skipped after the work charge. Otherwise the machine appends an ordered `SupportMember` step holding the exact support/member endpoints, indexes, borrowed view and family, and `closed_tail = true`; clones this branch's `seen`, inserts the member, and pushes the child. Ascending pushes make the LIFO visitation order descending by member ordinal.

The Support vertex was itself reached by a checked physical edge, which inserted that Support endpoint into the branch's `seen`. A member cycle check happens before cloning/queueing. `seen` is copied per child: there is no global suppression of convergent branches. Non-target `AnnotationMember` and other non-Support, non-row endpoints terminate their branch without further reads.

An `EffectRow(row)` reads that row's current `EffectBounds`. It schedules every `direct_lower_rows` slot in ascending index, then every `exact_non_variable_lowers` slot in ascending index. Each slot consumes one work unit before its current endpoint is read and before branch-local `seen` is tested. For a seen target it skips the physical owner reader; otherwise it calls `checked_physical_lower_edge` with the exact row, lane, index, and positive `EffectRow(row) -> targetEndpoint` bound. Children are pushed in row-lane then atom-lane order, so LIFO visitation is atom indexes descending, followed by row indexes descending. An invalid row/slot index is `BoundMismatch`; a checked-reader error propagates without being erased by a prior successful branch.

All per-branch `Vec` and `HashSet` growth and result/path retention uses `try_reserve`; allocation failure maps to `SearchLimit`. View/member index overflow and all checked-work overflow also map to `SearchLimit`. The limit is exactly 65,536. Charges occur for a full path/seen measure on every pop, each allowed Support member before cycle pruning, and each lower-row/atom slot before endpoint read/cycle pruning. Path copying, set copying, physical owner reads and support-tail validation do not add separate `certified_lower_paths` work units.

## Entry and Catch ancestry behavior

The caller invokes distinct searches: Catch root is the canonicalized `catch_fact.lower()` positive effect endpoint and passes `entry = None`; permission Entry root is `EffectRow(permission.entry_effect)` and passes `entry = Some(self)`. Both use the selected provider member as target. Keep `(root, target, mode)` as the query key; equal roots and targets do not justify merging Catch and Entry behavior.

Catch mode checks every unskipped physical edge with `checked_physical_lower_edge`, but keeps `use_root = None` and performs no relation-ancestry query. Entry starts at an effect row, so its first transition on any nonempty path is physical. After the physical slot reader succeeds, `current_internal_emission(edge.id)` re-reads the current exact slot, authenticates it to the unique Internal use and permission entry row, validates its admission/relation/source-drain root, and supplies `use_root`. The checked first emission must match the path edge's emission ID, admission ID, slot and bound. Later physical edges independently require `require_relation_ancestry(edge.relation, use_root)` before being queued. Support transitions carry the root unchanged. Any first-edge or later ancestry error rejects the entire query. After both selected paths return, `provider_entry_certificate` re-runs `current_internal_emission` for the first Entry edge and compares the four retained physical coordinates again.

`require_relation_ancestry` has a separate local `visits` counter for each invocation; these visits are not added to the path search's `work`. It first checks that both descendant and ancestor indexes exist, returning `InvalidRelationReference` otherwise. It then computes `limit = min(relations.len(), 65,536)` and returns `SearchLimit` immediately if `relations.len() > 65,536`, before allocating or traversing, even if descendant equals ancestor. It fallibly reserves the pending and seen sets for `limit`, seeds pending with descendant, and uses LIFO pops.

For each pop it checked-increments visits and rejects `>65,536`. It tests `child == ancestor` next and succeeds immediately, before inserting into seen, validating that child's record, or scanning dependencies. Otherwise a duplicate child is skipped. A nonduplicate child must index a relation row. The routine then scans every dependency in vector order, charging one visit for each scanned dependency, including nonmatching ones. Matching `Derived`, `FunctionPort`, `TuplePort`, `RecordPort`, `VariantPort`, and `Transport` edges contribute their one parent; matching `Replay` contributes lower then upper parents. Parent indexes are validated before the already-seen check, and each unseen parent is fallibly queued in array order, so a Replay's upper parent is visited first. Exhaustion without finding the ancestor returns `MissingUseAncestry`. Work overflow, failed reserve, oversized inventory, or over-limit visits returns `SearchLimit`.

The first Entry edge executes `current_internal_emission`, whose `checked_emission_for_internal_use` itself performs relation ancestry. Thus first-edge authentication includes the ancestry reader before the outer search retains the returned `use_root`; later edges call ancestry directly. The separate post-search first-edge re-read repeats that Internal check. The R58 Rust note did not state the early `relations.len() > limit` guard; this R59 handoff records it against the pinned source.

## Success/failure correspondence boundary

Success is exactly exhaustion of the LIFO stack with one reached target and no reached reader, ancestry, ambiguity, allocation, overflow, or work-limit failure. Zero targets returns `Ok([])` from the search; its caller maps that to `MissingCommonEndpoint`. A second target returns `AmbiguousPath` from the search immediately. Other returned errors propagate through `provider_entry_certificate` as unavailable; none become successful empty/singleton candidate lists.

The transition table can support the R59 Lean converse only relative to its encoded view/row/dependency readers and the R58 soundness/prefix theorems. The Rust search retains no trace, so this handoff does not claim a Rust small-step execution proof, completeness of a separate projection reader, or unconditional equivalence to an all-slot traversal. In particular, a malformed slot outside every reached branch is never read here, whereas an all-slot scan may reject it. Reached malformed alternatives, branch-local cycles, convergent paths, second targets, Support-tail errors, Entry's late ancestry errors, and distinct Catch/Entry policies must remain separate cases.

## Frozen inputs and scope

R59 contract: `tasks/agent-loop/sprints/effect-permission-reached-slot-completeness-20261031-r59.md`, SHA-256 `90278c103db56eaea91a65491241aec55e111db20bbfa2a71c85cc82b155e9b3`.
Receiver: `8d491e52ed9922e982c93a694e8c065bb065ca5f50bff76c255a5303eba1e016`
Read-only context: `8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89`
Read-only candidate source: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
R58 Lean model: `431d3b4cb031fd86ad4a0537c1c8a42adecb8433f3ef775b3371eb37611b3079`
R58 proof handoff: `0f21458b14cf34ca6712c85858cc02fac6f4733f14e14ffa174c43034495781f`
R58 Rust source map: `2a030a978dcf2b66a84b24013f04a0b7dc61556ac8ac9f7cdb8efd7b94cbda94`

No Rust code, tests, build, Cargo, formatter, type-check, environment, cache, scratch, target, or worktree changes were made. No runtime execution claim is made.
