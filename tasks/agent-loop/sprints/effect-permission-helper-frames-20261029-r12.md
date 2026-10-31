# EFFECT-PERMISSION-HELPER-FRAMES/20261029-r12

Status: admitted by Luna under the unchanged ongoing inference/executor research goal, after R11 `CLOSED_COMPLETE_CONDITIONAL` and the selector's sprint-end recommendation. This packet investigates actual local helper frame obligations used by R11. It grants no compiler-semantic or production-promotion authority.

## Fixed outcome

Extract the relevant helper operations and callees at the 13 R11 local frame cuts. From explicit source operations, construct checked frame-lifting lemmas that preserve only fields untouched by those operations, then apply supported equalities to the corresponding R11 `FunctionFrames`/`TreeFrames` premises. Keep reservation availability and native execution correspondence separate.

The source model must distinguish term construction (writes `store.terms`), sampling (reads Effect vectors and changes accounting fields), Vec reservation (capacity change without row append), and concrete permission ports (copy/accounting, the designated permission append, then completion). Do not classify the permission append itself as frame-preserving. Do not assume desired endpoint equalities, invent successful executions, use empty frames for unknown executions, or replace source operations with a whole `TreeFrames` oracle.

Preserve R11 immutable. Keep helper-return cuts, permission path identities, event rows, sequential states and allocation order. A frame lemma only claims the projection justified by the operations/callee; reservations, external primitive behavior and Rust/native authenticity remain separate.

## Lanes, leases and resources

- **Source:** Luna/high, read-only, 200 seconds. Exact output `tasks/agent-loop/inbox/effect-permission-helper-frames-r12-source.md`. Inspect pinned `crates/yu-solver/src/candidate_effect.rs` and `crates/yu-solver/src/lib.rs`; provide a complete operation/callee-to-cut table, every protected field, explicit writes/reads, permission append location, and unresolved alias/callback/primitive-library dependency.
- **Proof:** registered `lean_prover`, 600 seconds. Exact writes `notes/theory/lean/YulangClosure/FormalPermissionHelperFrames.lean` and `tasks/agent-loop/inbox/effect-permission-helper-frames-r12-proof.md`. Transcribe identified operations with actual mutated fields; prove preservation of Effect-row count and the justified permission prefix/delta; assemble only supported R11 frames.
- **Independent review:** fresh nonauthor `compiler_referee`, 250 seconds, after frozen source/proof and primary audit. Exact output `tasks/agent-loop/inbox/effect-permission-helper-frames-r12-review.md`.
- **Primary:** Luna, 150 seconds for input/copy inventories, audit releases, review/adjudication and closeout. Total 1200 seconds; zero Astra and zero descendants.

## Audit and stop contract

Use pinned Lean 4.35.0, a fresh isolated project under `/tmp/yulang-effect-permission-helper-frames-20261029-r12/lean-project/`, explicit copied dependency inventory and separate attempt/raw/resource paths. Permit at most two separately released focused audits, each at most 90 seconds and at most 120 seconds combined. Freeze complete inputs, artifact and dependency hashes, theorem roots, checker/tool hashes, exact argv/environment, project copy receipt, and distinct stdout/stderr/status/resource paths before each release. Require complete theorem types and transitive axiom audits for every public declaration.

Falsifiers: omitted write/callee, protected-field alias, hidden allocation, misplaced permission append, or a new premise merely restating `TreeFrames`. If execution-to-operation correspondence cannot be established, record the exact boundary; a theorem about an operation transcription does not certify Rust execution. Stop on lease conflict, changed source pin, budget/attempt exhaustion or a required scope/assumption change. No tests, Cargo, instrumentation, compiler-source edits, dependency installation or Git operations.

## Parent gates

Success discharges only individually supported frame obligations. Reservation availability, complete Rust projection/native authenticity, original parent, effect hygiene, consumer, soundness, principality, termination and production remain OPEN unless separately established under their own authority.
