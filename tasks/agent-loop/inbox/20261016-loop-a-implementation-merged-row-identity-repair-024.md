Request-ID: LOOP-A-I17-R1-MERGED-ROW-IDENTITY-REPAIR-024
Revision: 1
From: implementer (`/root/i17_merged_row_identity`; requested gpt-6-luna/high, observed runtime settings UNKNOWN)
To: next_action_selector
Parent-gate: I17 canonical CandidateGraphRow identity verification; original source correspondence, soundness/principality, Simple-sub/F5, and production gates remain OPEN
Baseline: frozen I17 source SHA-256 `401b2406c7c4ac01d217752f431a9006eb5452731d71f90c7993ab293a0848e5`; preserve I17 inbox `20261016-loop-a-implementation-merged-row-identity-023.md` unchanged
Kind: implementation
Claim/task: Apply only the R27-accepted warning repair by removing the unused `RowKey` import from the I17 test, then rerun the selected native identity test without that warning.
Missing-evidence: None beyond verifying the exact repair has no unused-RowKey warning and preserves the passing I17 native behavior.
Owners: `crates/yu-solver/src/shadow_apply.rs::tests::candidate_graph_row_hashing_uses_merged_representatives`; this repair changes only its test import
Depends-on: R27 found no correctness issue; I17-R1 exact accepted repair
Scope: One import-token removal in the leased source and this receipt. I17 inbox023 and all other paths remain untouched. No production, semantics, graph, test assertion, or API changes.
Acceptance: The original native command exits successfully with 1 passing test and no unused-RowKey warning; literal diff contains only the removal shown below; source and receipt hashes are frozen.
Proposed-outputs: `crates/yu-solver/src/shadow_apply.rs`, this repair receipt
Checks/resources: Exactly one serial test command, 180s timeout, `CARGO_BUILD_JOBS=2`, one test thread; no other tests and no Git commands. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --lib shadow_apply::tests::candidate_graph_row_hashing_uses_merged_representatives -- --exact --test-threads=1` → exit 0, 1 passed, 0 failed, 714 filtered, 0.01s test / 5.24s compile. Output contained no warning.
Prior-work: Reuses the frozen I17 test, which selected an actual same-SCC retained parent/copy union and checked canonical Eq/Hash and HashMap first-row retention. R27 found no correctness issue. Adapted only by deleting the unused import identified in the initial I17 compile output. The earlier I17 recursive CLI result remains 1 passed, 21 filtered; it was retained without rerun, as assigned.
Priority-reason: Clears the bounded compile warning without altering the accepted regression behavior.
Stop/escalate: Completed without obstruction. Requested Luna/high; observed runtime model/effort UNKNOWN. No independent review claimed and no proof or production gate closed. Freeze source and receipt for dispatcher/reviewer intake.

## Literal baseline diff

```diff
--- a/crates/yu-solver/src/shadow_apply.rs
+++ b/crates/yu-solver/src/shadow_apply.rs
@@ -2168 +2168 @@
-        use crate::candidate_scheme::{Graph, Row, RowKey};
+        use crate::candidate_scheme::{Graph, Row};
```

Frozen source SHA-256: `3fb9335e94ded08ec800d3d4dd9ce6097bc74e3b2966dc70c0b34aadd4c547f7`.
