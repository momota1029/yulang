# R12 amendment 01 — narrow syntax repair and final audit

Authority: approved by Luna at the R12 material-blocker boundary, following selector recommendation `/root/r21_closeout_selector`. This is a primary-issued, exact sequential continuation under the existing R12 fixed outcome; it changes only the remaining time allocation and final attempt budget. It is not an implementation or semantic expansion.

## Authenticated basis

- R12 contract SHA256 `7c7573abd1778414300f78b7b0271d5d3479b7f3e9c296a343bfb51c6102ecd4`; R12 manifest SHA256 `057f4dafaa51ab8343a090de4f789adf2bce1d4e8db08d630551cb1d013f9a8c`.
- Frozen proof revision 1 artifact SHA256 `ed099b3f78fc4d7138d2342b81bf39938bcfbf90433ce5a5ac036a5bef6c5d68`; handoff SHA256 `0dec12d68266bd8abf3e858eb47d406fb29cfbc8a2b40d3c15518e9d96f9efe3`.
- Audit 1 plan SHA256 `096a97fd8f4dfcfe3d08616b8261b789f22212b24669eb8bc072de90b30153fc`; exit 1, 12.92 seconds, max RSS 798608 KiB, zero printed theorem types or axiom reports. Receipt SHA256 `00a9fdc3795cec81e4e7b16ec090bfb4e566bd244a20538edf76dcdce7953376`.
- Observed first blockers: multiline `HelperState` record update parse at line 80; allocator projection simplification at line 106; Lean reserved identifier `prefix` at line 116 onward; reservation projection proof at line 146. These are build/elaboration findings, not mathematical counterexamples.

## Exact continuation authority

Reallocate 90 seconds from the NOT_STARTED independent-review allocation to proof continuation. Updated total allocation stays 1200 seconds: source 200; proof 690 total including this new 90-second continuation; fresh independent review 160; primary 150. Do not infer spare time from the stopped proof author's original 600-second packet; its remaining duration is UNKNOWN.

- **Proof continuation:** same registered `lean_prover` identity, fresh bounded 90-second turn. Renew only the exact artifact and proof-handoff leases listed below. Maximum 30 seconds for repair, then stop writing and freeze the sequential revision. Repair the record-update syntax and rename reserved `prefix` consistently. Reassess allocator/reservation proof obligations after those parser repairs. Proof tactic/elaboration adjustments are permitted only if they preserve every operation/model field and fit within 30 seconds. No intermediate Lean/Lake/checker probes. Stop if the fix requires a model/operation change, new assumption, endpoint equality, changed theorem meaning, or exceeds 30 seconds. Preserve revision 1 and audit-1 receipts.
- **Final audit:** primary may release exactly one final pinned Lean 4.35.0 audit after freezing a new attempt-2 project copy and complete plan. Attempt timeout at most 60 seconds; combined audit wall time at most 72.92 seconds (12.92 already spent plus 60). Audit 2 is the last invocation. Require all nine theorem types and transitive axiom audits.
- **Independent review:** fresh nonauthor `compiler_referee`, 160 seconds, only after frozen revision 2 and audit-2 receipts. It must inspect both revisions, operation scope, all theorem types/axioms and exact remaining Rust/path limitations.
- **Primary:** 150 seconds, including this amendment/adjudication. Source lane is frozen and its 200-second allocation is spent.

Exact renewed write leases: `notes/theory/lean/YulangClosure/FormalPermissionHelperFrames.lean` and `tasks/agent-loop/inbox/effect-permission-helper-frames-r12-proof.md`. Primary owns all project/cache/generated output, audit plan, receipts, reviewer dispatch and closeout. Zero Astra/descendants; no tests, Cargo, compiler source, instrumentation, dependencies, or Git.

Before audit 2, freeze artifact/handoff revision 2, exact nine theorem roots, fresh project/copy inventory, all dependency/tool hashes, argv/environment and separate stdout/stderr/status/resource paths. Do not reuse the audit-1 project or `.lake` cache.

## Stop and gate

If syntax repair cannot freeze in 30 seconds, allocator/reservation obligations need any operation/model semantic change, the revised build/audit fails, complete types/axioms are unavailable, or reviewer capacity cannot be retained, close R12 **CLOSED_INCOMPLETE**. No automatic extension or third audit. Rust execution correspondence, full-path/relative-path mapping, reservations, original parent and production gates remain OPEN regardless of audit outcome.
