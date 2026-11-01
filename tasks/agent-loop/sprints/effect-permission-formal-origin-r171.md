# Sprint R171 — authenticate the collected Lambda and annotation

Status: **ADMITTED** under the continuing Yulang Rust/Lean soundness goal.
Branch / baseline: `yulang3` / `6dc6aa855` (pushed).
Primary: Luna. Original parent remains
`YulangClosure.SourceProblem.InferenceSoundness` in `Contracts.lean:127`.
R169/R170 results remain conditional; no source/native closure is claimed.

## Fixed outcome

The target is soundness of **Yulang type inference**, including its inferred
effect rows, against the original source typing rules. Rust is the implementation
whose constraint-generation steps must be related to that semantics; Rust
runtime or machine correctness is outside this sprint's goal. R171 is only an
intermediate compiler-construction lemma, not a substitute for an inference
derivation or the parent theorem.

Prove, from the actual finite registration construction, that a collected
formal registration identifies the same owner, Lambda occurrence, parameter,
and annotation read by its `FormalEntry` action. Apply this fact to R169's
frozen successful trace so that the action's annotation is the annotation
observed at the selected source Lambda. Then state exactly how that fact enters
Yulang's inferred-effect judgment and the original `InferenceSoundness`
obligation; if R169 lacks that inference derivation, keep it explicitly open.
Do not add a bare uniqueness premise, change the original parent quantifiers,
or replace its shared witness.

The source lane maps the exact clean construction path from HIR parameter ID
generation through Lambda registration, ID-map update, annotation lookup and
Action construction. It may report `NO_SAFE_CODE_SLICE`; it has no source-write
authority. A code change requires a concrete reachable counterexample and a
separately admitted scope.

## Frozen inputs and exact outputs

- R169 trace module:
  `notes/theory/lean/YulangClosure/FormalEntryPrestateBridgeR169.lean`, SHA-256
  `bb0aaffe95f99881b089807a202991c4349a7c61e9ebb0f42f56d7f080a7baf4`.
- `crates/yu-solver/src/candidate_source.rs` SHA-256
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`.
- `crates/yu-solver/src/candidate_effect.rs` SHA-256
  `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`.
- `crates/yu-hir/src/module.rs` SHA-256
  `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`.
- `crates/yu-hir/src/module/local_source.rs` SHA-256
  `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`.
- Proof output: `notes/theory/lean/YulangClosure/FormalEntryOriginR171.lean`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-formal-origin-r171-proof.md`.
- Source handoff: `tasks/agent-loop/inbox/effect-permission-formal-origin-r171-source.md`.

The source handoff is a frozen R171 proof input after the source lane stops:
`tasks/agent-loop/inbox/effect-permission-formal-origin-r171-source.md`,
SHA-256 `8db9a9730932aedd162ad4c918000c6c73176323eae797be022a197db2174f22`.
The proof lane may read this exact handoff; no other source-lane path is added.

## Required construction invariants

Track the actual append-only registration vector and the ID-to-registration
map updates. Establish any needed uniqueness from the HIR constructors and ID
generation, not from the map's final lookup alone. Account for duplicate map
keys, checked ordinal increments, source owner identity, Lambda index,
parameter ID, and annotation identity. Show that the selected registration's
stored Lambda/parameter is the one whose annotation produces the `Action`.
Then transport the established owner/annotation identity into the exact R169
trace fields. Preserve source and native identities as distinct until the
proved join.

Falsifiers include two distinct Lambda parameters sharing an ID, map overwrite
that redirects a registration, owner/index substitution, a construction
snapshot that mixes pre- and post-update state, or a different annotation
reaching the action. If a source invariant cannot be derived from the pinned
constructors, state the exact missing premise and stop that application.

## Lanes, resources, and review

- Proof lane: registered `lean_prover`, at most 2400 seconds, only the new
  module and proof handoff. Use the pinned Lean 4.35.0 and authenticated existing
  imports. Verification is in-memory stdin; no Lake build/helper, output file,
  cache growth, target, environment, scratch, Cargo, Rust build, or tests.
  At most two Lean invocations, one CPU, 1 GiB memory. Stop if required
  dependencies are absent or cannot be authenticated without generating files.
- Source lane: registered `researcher`, at most 600 seconds, read-only on the
  four exact Rust/HIR inputs and R169 module; only its source handoff is writable.
  No builds, tests, Cargo, Git, or unrelated/quarantined path inspection.
- Fresh independent proof and source reviewers: 300 seconds each, against frozen
  hashes. No self-review. Astra 0. Total ceiling 3600 seconds.
- All UNKNOWN rows and quarantined leases remain unchanged. No capacity override.

## Closure boundary

A passing theorem and fresh review establish only the exact finite collector to
`FormalEntry` owner/annotation correspondence. Rust execution realizing the
full R169 `Trace`, R116 selected-source/operation/endpoint decoding, R45/R54,
Catch consumption, complete effect hygiene, principality, termination and the
original `InferenceSoundness` theorem remain separate open obligations. Only
Luna stages explicit reviewed paths and pushes a complete coherent range.
