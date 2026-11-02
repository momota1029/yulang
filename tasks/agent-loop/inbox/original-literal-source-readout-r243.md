# R243 original literal source readout — frozen handoff

- Sprint/contract revision: R243, admitted contract SHA-256 `58995da0b2880560bf63be81b8d59c07c516e6dd162d6624b7f0d1a74d98674e`, `tasks/agent-loop/sprints/original-literal-source-readout-r243.md`.
- Assignment/handoff revision: `/root/sol_r243_source_readout`, revision 1.
- Session: `01a1873a-a93b-7dc3-a8ce-028a7b543a80`; launch receipt: primary NEW_TASK and current-session worker row. Role: researcher; requested Sol/high; observed model/effort UNKNOWN.
- Baseline commit: `cddf5d23fe73f78c49f579b30ecc6e6a8287f8f2`, supplied by primary's read-only HEAD receipt. Worker ran no Git command.
- Parent: unchanged `SourceProblem.InferenceSoundness`, `notes/theory/lean/YulangClosure/Contracts.lean:128–130`. Parent delta zero; accepted L1/canonical generation and complete eight-form source domain preserved.
- Outcome class: research-only bounded static source evidence (`source-native-evidence` category); not an execution result, semantic counterexample, theorem, Rust correctness result or independent review.

## Result and first missing edges

The artifact contains an eight-payload map and the exact HIR/constraint/admission/result chain. Unit, bool, integer spelling and string spelling have retained source forms. `LocalSourceExpr` retains authentic occurrence, parse source, range and lexical scope (`crates/yu-hir/src/module/local_source.rs:313–323`, `Builder::set_at_range:1520–1549`). `LocalSourceForm` / `Builder::expression` has no floatBits, bytes, path-literal or character payload variant/arm (`:348–440`, `:1881–2278`). Those are source-owner representation coverage gaps, not source restrictions or permission to remove original cases.

`emit_candidate_source` records occurrence-to-owner and occurrence-to-HIR joins (`crates/yu-solver/src/candidate_source.rs:1052–1069`) and component positions. Its literal `Work::Finish` branch emits four type/effect relations with occurrence-local slots 0–3, ignoring payload fields (`:1587–1606`). `append_source_facts` makes `Action::Fact(j)` from the occurrence-vector indices (`:2262–2264`); `execute_candidate_action` invokes admission (`:2481`). `InferenceSession::admit_collected_fact` records provenance and constrains live endpoints (`crates/yu-solver/src/lib.rs:11546–11590`). `FactId` differs from occurrence identity: canonical facts carry terms; provenance carries cause/occurrence.

**Retained HIR provenance is not an original decoded-row join.** `finish_observations` retains original HIR and occurrence-to-HIR indexing (`lib.rs:20326–20349`), and `FrozenInferenceData::hir_for_occurrence` can select that HIR (`:7836–7842`). For known owner/index, `HirModule::local_source_for` (`crates/yu-hir/src/module.rs:2022–2029`) plus `LocalSource::expression` (`local_source.rs:174–178`) recovers the retained form; an exact-occurrence search recovers it without inverting a constraint. Global payload loss is therefore not established.

The **first missing original readout edge in the inspected result chain** is the absent join from `(retained HIR, owner, occurrence, source payload/spelling, solved facts)` into `SourceAssignment.row site`. Exact consumer boundary: `finish_observations` constructs classification-only `SolvedProjection {value,effect}` (`lib.rs:20146`); `CandidateInference::source_occurrence_observation` constructs occurrence/cause/fact records and bounded origin observations (`crates/yu-solver/src/shadow_apply.rs:2251–2294`, especially `:2273`). Neither constructs the original descriptor/value/root/event row or establishes implementation-occurrence-to-original-site correspondence. This is a bounded chain inspection, not a repository-wide absence theorem.

R241's exact consumer still needs the complete-prefix decode, `declarations literal (state.assignment.row site)`, final-root descriptor classification and `inputs.ground (state.assignment.row site)` (`OriginalLiteralCarrierRealizationR241.lean:57`). R242 input dependence and Return/event premises remain untouched. Source lexical scope, implementation root and pure-effect bounds were not substituted for original scope, root, event, witness or contextual effects. Written-target annotations, synthesis endpoints and final-root ports remain distinct.

## Derivation, coverage and checks

Minimal symbolic comparison: hold authentic-coordinate parameters `o`, component positions `p` and term arena fixed at the literal branch; its four records for `Boolean(true)` and `Boolean(false)` are identical because `b` is never read. A decoder of only that projection cannot recover both bits. This is a conditional syntactic erasure argument, not two authenticated parsed files with equal IDs, a mutated run or a source-qualified counterexample. Retained HIR is an additional input outside that argument.

All eight original forms have explicit rows. Integers retain token spelling; strings retain delimited source spelling, with decoding to original payload unproved. Interpolation/generated text retains its separate distinction. No source/native parser behavior or alternate runtime path was tested. Projection coverage outside `batch.projection_order` was not established. The occurrence observation has a 256-row cap and completeness flags.

Commands/checks: `sha256sum`; scoped `rg -n`; focused `nl -ba`/`sed` reads. All seven dependency hashes and contract rechecked unchanged immediately before freezing. No build/test, Cargo, cache/scratch output, compiler edit, Git, network, descendant or quarantined-runtime access. No experimental seed/range/mutation. Zero heavy processes; one lightweight read command at a time. Exact active wall time and CPU/RAM peaks were not instrumented; primary runtime receipt is needed for numerical consumption. Envelope: 1,200 active seconds. Large initial read output was truncated; all cited ranges were subsequently read in focused chunks.

Oracle independence: observations come from actual hashed source fields/calls, not assumed checker transition rules; semantic implementation correctness and R241/R242 theorem verification are shared/unverified inputs for this assignment. Falsifier: an exact in-scope constructor/consumer that already builds the original row with payload, coordinates and the original relation facts; another type constraint or source key alone does not suffice.

## Frozen artifact and dependencies

Artifact: `notes/theory/2026-11-02-original-literal-source-readout-r243.md`, revision 1, SHA-256 `24b9052cc55914521e7d5cb045431f65ec7c1af465c2f0b90ed3718f125b65f3`.

| Dependency | SHA-256 |
|---|---|
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `notes/theory/lean/YulangClosure/OriginalLiteralCarrierRealizationR241.lean` | `49bbe56ee5525f1a7a5b3db2d5c2b04737468cdaa864c761fd6465e1af914d8a` |
| `notes/theory/lean/YulangClosure/OriginalLiteralInputDependenceR242.lean` | `b5a5ac8580d71ee15dd595fd2712316451df28a68398a524d558f72a12cee649` |
| Direct call/consumer: `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| Direct call/consumer: `crates/yu-solver/src/shadow_apply.rs` | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` |
| Direct source lookup: `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |

Only named direct calls/consumers in the last three files were inspected. Dependency changes: none.

## Next action and cessation

Recommended next action: planned fresh `compiler_referee` review of this frozen pair. Then Luna may dispatch a separately leased exact original carrier/readout proof bridge. This handoff grants no Rust or semantic authority.

Mutual TODO `R243-ORIGINAL-LITERAL-ROW-JOIN-1`: owner Luna for scheduling/authority and the next constructive proof owner for discharge; original parent unchanged; required input is the retained authentic payload/occurrence relation plus original complete-prefix assignment/readout and declaration/ground relations; proposed output is an applied bridge or a precise further missing premise. Four absent representations remain explicit coverage obligations owned at `LocalSourceForm` / `Builder::expression`. No implementation amendment is proposed here.

**STOPPED-writing, revision 1:** both exact lease paths are frozen upon this handoff write and ensuing hash read. Worker will make no further writes. Sole author is `/root/sol_r243_source_readout`; zero descendants, generated outputs or unresolved descendant leases. No shared state, runtime lease or compiler file was changed. Independent review is pending; this is not gate completion.

## Commit packet

- Exact leased/changed paths: `notes/theory/2026-11-02-original-literal-source-readout-r243.md`; `tasks/agent-loop/inbox/original-literal-source-readout-r243.md`.
- Baseline SHA: `cddf5d23fe73f78c49f579b30ecc6e6a8287f8f2`.
- Changed dependency hashes: none; full frozen dependency hashes above.
- Review status: unreviewed, research-only; fresh compiler_referee required.
- Checks already run: hash equality and focused static source/locator inspection; no executable verification.
- Proposed research-checkpoint commit message: `research: trace original literal provenance and missing readout bridge (R243)`.
- Shared-record deltas intentionally deferred to Luna/curator: record RESULT then REVIEW with frozen pair hashes, set this worker STOPPED, preserve all UNKNOWN/quarantined leases, record unchanged parent delta zero and the row-join/representation obligations, attach independent-review disposition, integrate only this exact pair when appropriate. No task/index/authority/question-board edits by worker.
