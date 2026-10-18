# Frozen implementation handoff — Replay constructor observation repair r6

Sprint: `npair-replay-constructor-lineage-20261018-r6`, revision 6  
Contract SHA-256: `68a518fa706613d523a9fe3a6be2394fb491e132e048b1299144532258d85fff`  
Assignment: r6 implementation repair, handoff revision 1  
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, still OPEN, closure 0.

## Frozen artifacts and source recovery

- `crates/yu-solver/src/candidate_scheme.rs`, SHA-256 `d8c53522685e9bdfc1ba00380f222f4936d8d8df3302248fcde31e093668c484`.
- Removing the complete r6 test addition in memory recovers the pinned r4 scheme baseline byte-for-byte, SHA-256 `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc`.
- `crates/yu-solver/src/candidate_context.rs`, SHA-256 `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca`.
- Removing only the new r6 test accessor in memory recovers the pinned r5 context baseline byte-for-byte, SHA-256 `22a42a41253161f33d68f9670ee64868c684c99bc692380c018f76a013abe147`.
- r5 implementation handoff reused: `tasks/agent-loop/inbox/20261018-replay-constructor-separate-test-repair-impl.md`, SHA-256 `4e3555e7a9b348a849e177062a54b9b763c74fe12c444de177159fd5f00b4bd8`.
- No other path was written by this assignment.

## Repair outcome

Only the r5 test function in `candidate_scheme.rs` changed. FunctionPort observations now first select every edge whose parent is the selected Replay child and whose field is the requested field. The test checks this unfiltered cardinality is one before checking the exact typed pair and `[Swap, Swap, Preserve, Preserve]` operation; it then requires four distinct child relation IDs.

Added one `#[cfg(test)]` read-only accessor in `candidate_context.rs`. It returns each admission ID and complete retained admission record keyed by relation, together with exact associated emission IDs and records. It adds no storage or production behavior. The test prints these typed records, selects the unique relation-keyed admission for the full `row.lower_input` key, and requires one associated emission whose bound equals the admission bound, physical slot equals readback slot, readback bound equals the same complete key, and phase is `ConstructorAfterAppend`.

The existing row completeness, route identity, source occurrence ancestry, drain linkage/classification, mutation controls, and final authentication result checks remain. Output is collected before assertions. Missing drain linkage remains `NotRetainedReachabilityUnknown`; the test does not infer `NotReached`.

## Checks, limits and status

Checks performed: in-memory SHA-256 reconstruction of both frozen source baselines; `git diff --check` on the two leased source files. Both baseline hashes matched and diff check passed. No test, build, runtime, or Cargo process ran. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN. The 300-second implementation cap was respected; exact active seconds are not available from the runtime receipt.

This is provisional source-evidence instrumentation only. It does not establish that the exact test passes, choose between sharing and lost fresh separation, prove source/native correspondence, or close the original parent. The independent instrumentation review and separately gated exact invocation remain pending.

Next related step inside the envelope: freeze and independently review these exact source bytes against the two r5 blockers and baseline pins. Writer state: STOPPED; writes ended at this handoff. No descendants or unresolved implementation leases.
