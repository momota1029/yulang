# R72 Rust source projection — frozen handoff

Sprint ID / contract revision and SHA-256: `EFFECT-PERMISSION-COMPLETED-INSTANCE/20261031-R72`, revision 1, `15c19d0acc062f47909b6a14f72742da9a5e4babf6e1cde1106e91fe455f7f06`.

Assignment ID / handoff revision: `/root/r72_rust`, revision 1.

Parent gate / original theorem and scope locator: the unchanged Yulang inference/executor soundness, effects, principality and termination goal, retaining original Simple-sub A/B and R66 Root quantifiers. R72 advances only the approved completed-reification source/native seam; see the frozen R72 contract and the R71 bounded return-refinement outcome.

Baseline / direct dependency hashes: baseline `ce5842b0823e6febcc64b496c18e71d4438ad915`; all 32 input-manifest pins matched before writing. R71 completed receiver `eb16e965e13a969760eeda00068edfa80e8ca37020dc16cb9c330de74f432c2f`; R71 Lean module `428ce6d7c93f37266111db8b0a4568069d6fb63f56c9ad1d856d6b107773f215`; R71 input manifest `f354089d8e24c971a1776b16f7d75874a58cfcb11e0cf6a8102aa60a5295ce57`.

Role / actual worker ID / current session / launch receipt: Rust implementation author `/root/r72_rust`; current-session launch receipt is held by Luna. No descendants.

Requested model and effort / observed model and effort: Luna / high requested by the fixed contract; runtime telemetry is unavailable, so observed model and effort are UNKNOWN.

Exact leased paths / authors: only `crates/yu-solver/src/candidate_receiver.rs` and this handoff; author `/root/r72_rust`.

Outcome class: implementation, bounded source-native projection evidence.

End-to-end behavior achieved: the completed successful-return carrier now constructs a private `InventoryCompletedInstancePrimitiveProjection` solely from `InventoryCompletedReificationView`. The projection borrows the exact owner, encoded Term and separate ComponentId identity tables, all completed source fact and provenance rows, interpreted fact rows, occurrence and edge rows, and owner Value/Effect bounds and representatives. The previously built branded-Term and component-position maps are moved into the existing encoded table; no second inventory or serialized snapshot is constructed. `internal_root_view` obtains and checks this projection before consuming the same completed reification.

Executable rejection checks: the projection gate returns `BoundMismatch` for a foreign owner, stale bounds, omitted fact/provenance/interpretation/edge rows, reordered or substituted source pointers/indices, mismatched identity/occurrence/slot ownership, and changed raw/canonical lower or upper endpoints or current representatives. It retains separate Term and ComponentId namespaces. Coordinate conversion/resource overflow remains `SearchLimit`; malformed owner/table coordinates remain `BoundMismatch`.

Parent/source/native correspondence: `InventoryPackage` supplies the R71 completed carrier only after `reify_qualified_facts` succeeds. The projection reuses that carrier and its already-checked encodings, verifies the same owner session/store and exact ordered rows, then the existing `internal_root_view_from` consumes the completed result. This is source-side finite projection evidence only. No compiled Rust execution, Lean package decode/replay, allocator equivalence, or native runtime equivalence is established here.

Prior evidence reused / rejected: reused the reviewed R69 endpoint owner tables, R70 encoded branded identity tables, and R71 successful-return carrier and ordered fact/provenance/occurrence rows. Rejected reconstructing a second inventory or taking a supplied interpreted package as source evidence. R71's open source/native instance gap remains open until the Lean lane constructs its package from these concrete owner tables and rows.

Artifact locator and hash / frozen review snapshot: `crates/yu-solver/src/candidate_receiver.rs`, SHA-256 `9dfac06c82d62eb2c012f2f8b3a5affa6a85a397429302925463ee05a5cdf282`. Exact frozen review snapshot is the final file bytes at that hash.

Checks, omitted cases and resource budget: all 32 pins were verified before writing. `git diff --check -- crates/yu-solver/src/candidate_receiver.rs` passed. No Rust build, Cargo, test, formatter, Lake, cache, target, scratch, worktree, environment, dependency or configuration operation was run or created. Assignment bound: 1,400 seconds; work stopped within the assigned bound. No independent Rust compile or runtime evidence is claimed.

Mutual TODO: `R72-SOURCE-PROJECTION-TO-LEAN-PACKAGE-01`; original parent: the R66 same-witness qualified-read refinement, with R71 successful-return equations retained. First missing evidence: construct the Lean R71 `Package` from the exact R72 borrowed encoded tables, representative/competitor rows, complete facts and endpoint rows, plus provenance owner and original-index rows; derive rejection of foreign/stale/omitted/reordered/substituted rows without assuming a supplied package or faithfulness law. Source owner: this R72 Rust projection; proof owner: `/root/r72_proof`, exact leased module `notes/theory/lean/YulangClosure/CompletedNativeInstanceR72.lean`. Required inputs: this frozen Rust artifact and pinned R69–R71 definitions. Proposed output: a checked finite decode and exact R71 replay with unchanged original R66 witnesses and premises. Falsifier: any accepted input can alter owner, namespace, table coordinate, endpoint, row order, provenance occurrence, original index, representative or competitor list while replay still succeeds.

Remaining OPEN: Lean source/native correspondence and R71 package construction/replay; actual R66 source Root construction; Rust compilation/runtime; native allocation/resource/failure equivalence; original A/B; whole-language effect hygiene, soundness, principality, termination and production. No semantic boundary changed; no provisional runtime claim is made.

New paths: this handoff only. Disposable scratch outputs: none.

Worker state / writes stopped receipt: STOPPED / WRITES STOPPED; no processes or descendants remain active. No Git mutation was performed.

Commit-ready milestone: pending fresh independent R72 review and Luna adjudication/integration.
