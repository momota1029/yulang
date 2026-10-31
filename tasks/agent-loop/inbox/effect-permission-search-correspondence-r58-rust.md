# R58 Rust search correspondence handoff

Session: `EFFECT-PERMISSION-REACHED-SLOT-SEARCH/20261031-R58`
Requested lane: Luna/high. Observed model/effort: UNKNOWN.
Source baseline `candidate_receiver.rs`: `8d491e52ed9922e982c93a694e8c065bb065ca5f50bff76c255a5303eba1e016`.

## Concrete machine to model

The source machine is `certified_lower_paths` in `crates/yu-solver/src/candidate_receiver.rs:58-197`. Its complete call key is `(bounds, context, views, root, target, entryMode)`. A Lean state should retain, per pending branch, `(endpoint, orderedSteps, branchSeen, useRoot)` and a LIFO stack of such states, plus the ordered found-path list and `usize`-bounded work count. The initial branch has `endpoint = root`, empty steps, `seen = {root}`, and no use root.

Each `pending.pop()` charges, with checked `usize` arithmetic, `steps.len + seen.len + 1` before classifying the endpoint. Overflow or a total strictly greater than `candidate_source::SCOPED_WORK_LIMIT` (65,536) yields `CurrentEmissionGap::SearchLimit`. An endpoint equal to target appends its path; allocation failure is `SearchLimit`, and a second successful path immediately yields `AmbiguousPath`. A single found path does not end the search: the pending stack is drained, so later reached failures still invalidate the query.

Endpoint transitions follow this order:

1. **Target:** record the current ordered path and stop expanding that branch.
2. **Support:** index `views[view_index]`, else `BoundMismatch`. Any open tail gives `MissingCommonEndpoint`. For every allowed member in ascending source order, charge one work unit, convert its ordinal to `u32` (overflow gives `SearchLimit`), then check branch-local `seen`. A seen member is skipped; otherwise append one typed `SupportMember` step containing the exact support/member endpoints, view/member indexes, borrowed view/family, and closed-tail fact; clone the branch-local `seen`, add the member, and push the child. The stack therefore visits allowed members in reverse order. Any `try_reserve` failure gives `SearchLimit`.
3. **Effect row:** a missing row is `BoundMismatch`. Enumerate lower-row slots first, then lower-atom slots; within each lane use ascending indexes. Charge each slot before reading its current endpoint or checking `seen`. A seen endpoint is skipped before any physical-owner read. Otherwise construct the exact positive `EffectRow(row) -> endpoint` bound and physical slot, then call `State::checked_physical_lower_edge`. Children are pushed in row-lane then atom-lane order, so LIFO visitation is atom indexes descending followed by row indexes descending.
4. **Other endpoint:** no successors; that branch ends normally.

Every unskipped physical edge is checked against the exact current slot, unique emitted physical slot, retained emission/readback slot and bound, admission, positive effect-lower lane, and relation pair (`candidate_context.rs:3069-3102`). The checked edge retained in the path borrows the actual emission and admission. A malformed reached slot returns its reader error even if another path was already found. A malformed but unreachable slot is never read. Cycle pruning uses a copied `seen` set per path, not a global visited set; convergent branches remain separate candidates and can establish ambiguity.

## Entry and Catch policies

The caller `provider_entry_certificate` runs two separate searches (`candidate_receiver.rs:747-754`): Catch uses `root = effect_endpoint(catch_fact.lower(), Positive)` and `entryMode = None`; Internal permission entry uses `root = EffectRow(permission.entry_effect)` and `entryMode = Some(self)`. Both target the same uniquely selected operation annotation member. They are separate queries even if `(root,target)` happen to coincide; the mode is semantically relevant.

In Catch mode every checked physical edge sets `useRoot = None` and skips use-ancestry checks. In Entry mode the root is an EffectRow, so the first transition on a nonempty path is physical. Its exact lower slot is checked first; then `current_internal_emission(edge.id)` must match the same emission, admission, slot and bound. That reader ties the current slot to the unique Internal use, exact permission entry row, source occurrence/fact pair, admission/relation and completed source-drain root (`candidate_receiver.rs:618-679`; `candidate_context.rs:3107-3163`). It supplies the `useRoot`. Each subsequent physical edge separately calls `require_relation_ancestry(edge.relation, useRoot)`; support-member transitions carry the root unchanged.

An Entry state outside those cases returns `MissingUseAncestry`. `require_relation_ancestry` is itself a bounded LIFO search over dependency parents. It rejects out-of-range initial relation IDs as `InvalidRelationReference`; reserves stack and seen capacity for `min(relationCount, 65,536)` or returns `SearchLimit`; charges one visit per pop and one per dependency scanned, with overflow or `>65,536` returning `SearchLimit`; accepts when the popped relation is the ancestor; validates traversed child/parent indexes; follows both parents of Replay and the single parent for the other listed dependency kinds; and returns `MissingUseAncestry` if exhausted (`candidate_context.rs:3165-3220`). Each ancestry call has its own counter.

After both searches succeed, the caller requires exactly one path from each; empty maps to `MissingCommonEndpoint` and a non-singleton maps to `AmbiguousPath` (`candidate_receiver.rs:755-764`). It re-reads the first physical Entry edge through `current_internal_emission` and compares emission/admission/slot/bound once more before retaining both path vectors (`:765-786`). The retained vectors are copied with `try_reserve_exact`; failure is `SearchLimit`.

## Error and correspondence boundary

All search, checked-reader, Internal-emission, and ancestry errors propagate through `provider_entry_certificate` as unavailable `CurrentEmissionGap`s. Relevant distinctions are `BoundMismatch`, `WrongEntrySlot`, `MissingEmission`, `AmbiguousPhysicalSlot`, `MissingAdmission`, `MissingRelation`, `ForeignRelationPair`, `MissingInternalCertificate`, `MissingUseRoot`, `AmbiguousUseRoot`, `InvalidRelationReference`, `MissingUseAncestry`, `MissingCommonEndpoint`, `AmbiguousPath`, and `SearchLimit`. Catch-fact/provider selection also maps its own missing/ambiguous cases to unavailable. The machine never converts failure to an empty successful candidate list.

No factoring change was made: the existing function already presents the transition cases in executable order, and extracting helpers would not strengthen source correspondence. This is a source-grounded map, not a Rust execution trace or proof of the R57/R50 relation. R57 retains the native owner tables and selected successful paths, but does not persist a worklist trace. Lean must connect its bounded reached-candidate relation to these exact Rust transitions and make any encoding of owner rows/current slot reads an explicit premise. In particular, do not equate this search with validating all slots: an unreachable malformed slot is not read here, while an all-slot R57 traversal may fail on it. Likewise distinguish reached malformed alternatives, branch-local cycles, second paths, late Entry ancestry failures, and `(root,target,None)` from `(root,target,Some(use))`.

## Frozen inputs and limits

R58 contract: `041c75869d316019cbf1f791873ac7a95fdd334d1f7760b303c667d5a0933eed`
R58 source receiver baseline: `8d491e52ed9922e982c93a694e8c065bb065ca5f50bff76c255a5303eba1e016`
Read-only `candidate_context.rs`: `8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89`
Read-only `candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
Read-only R57 Lean model: `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63`
Read-only R57 outcome: `b33e106b1f6ca031b548a1516e8e06b278e100deb5dd9685ac91f2608232d0cc`
Read-only independent R57 review: `ea4e5bb4f60b4b4b9d314bb44d1092777e0e49a123ca9b458a79f8225bd9949e`

This lane made no source edits, tests, builds, Cargo, formatter or type-check runs. The proof still needs to connect its transition relation to actual owner-derived values and preserve the distinct mode/error behavior. No runtime execution claim is made.
