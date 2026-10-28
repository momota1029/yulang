# R16 independent pre-run review

Verdict: ACCEPT. STOP after pre-run stage; eligible to resume the same grant for post-Cargo review only after Luna ACKs frozen Cargo-1 logs.

The reviewer independently verified all 446 file pins and 16 parent pins, plus the contract, manifest, implementation handoff and source handoff hashes. All R15 pins are preserved byte-identically after the path prefix; Cargo.toml, Cargo.lock and the candidate are unchanged. All 12 workspace members and 15 path dependencies resolve. The whole-snapshot scan found 66 literal include references and two `include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), literal))` references; all 68 targets resolve and are pinned. No build.rs is present, and the fresh target directory is absent.

Read source-first: same-graph publication at `candidate_scheme.rs:2915-2954` retains interned negative Function roots and validates existing entries; missing or wrong nodes yield `ReceiptMismatch`, consistent with R14. The focused test is at `candidate_scheme.rs:8158`; `lib.rs:210-211` and the `shadow-apply-candidate` to `shadow-f5` feature relation were verified. The missing R15 compile-time inputs are now present. No blocker was found.

This ACCEPT authorizes only the single contracted Cargo invocation. Compile/runtime evidence and all source-parent gates remain unestablished. No tools, builds, tests, Cargo, Git, checker or writes were used by the reviewer. Review fit within the <=90 second pre-run stage; observed model/effort: UNKNOWN; process CPU/RSS unavailable.

## Post-run review (same grant)

Verdict: execution evidence ACCEPT; DONE REJECT; record `CLOSED_INCOMPLETE` under the contract rule for any focused test failure. Independently reauthenticated all 446 file pins, 16 parent pins, and the exact four supplied log hashes. The argv matches the single contracted command, feature, filter and target. Resource record: Cargo/rustc 1.95.0; UTC 12:42:08.494526–12:44:04.869947; 116.375 seconds; exit 101; no limit termination; affinity [0]; 570 samples; peak sampled process-group RSS 1,859,252,224 bytes; final sampled process count zero. RSS sampling is not continuous proof.

The test compiled and ran; stderr:461–463 reports failure after the test. stdout:3,58 reports one failure and 816 filtered out. Panic at candidate_scheme.rs:8428 reports that `emission_cases.first()` found no authenticated FreshUse route. The independent bounded positive observation: same-invocation capture/lookup joins for graphs 3/6, relation 8, root Term index 264, owner index 11 with Negative Function children [12,13,14,15]; and graphs 9/11, relation 150, root index 366, owner index 12 with children [13,14,15,16]. `session.execute()` returned `Ok`. `EvidenceCoverage { gaps: 56 }` remains. The failed assertion does not reveal which individual authentication guard is responsible, and none of the intended rejection stages was reached.

No additional command, build, test, metadata, Lean, Git, checker, or write was performed by the reviewer. Post-run review STOPPED within the same grant. All parent/source/production gates remain OPEN.
