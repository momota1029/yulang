# Sprint EFFECT-PERMISSION-CAPTURE-20261028/r1

Status: ADMITTED after dispatcher consultation and primary authority/dependency
reconciliation. This bounded sprint advances the unchanged whole Yulang
inference goal; it does not redefine its completion condition.

Branch / baseline: `yulang3`, `233b221d6`.

## Authority and frozen inputs

- User goal: implement and prove Yulang inference and soundness, especially
  effect hygiene, using Rust and Lean and primary-owned incremental Git pushes.
- Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
  §§1, 3, 5; preserve every supported original source program, lawful finite
  Simple-sub history and retained extrusion occurrence, all original scopes,
  correlated witnesses, complete Call, effect hygiene, soundness, required
  principality, ordinary progress and inference termination. No quantifier,
  accepted source form or parent claim is weakened here.
- Governing behavior: Authoritative
  `notes/design/2026-10-11-yulang-inference-top-level-principles.md` and
  `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5.
  Contravariant `[E]` grants local subtraction permission; only the actual
  handler removes actual inflow, symbolic dependencies remain, and independent
  same-row contributions retain their lineage. No new semantics are selected.
- Prior sprint `FORMAL-PERMISSION-PROJECTION-20261028/r8-amendment-05` is closed
  INCOMPLETE. Its outcome is
  `tasks/agent-loop/history/formal-permission-projection-20261028-r8-addendum-05-outcome.md`,
  SHA-256 `1e3b6f64068f541c98f03eec396dbeea4c47df90dbc88925888126a50462c90b`.
  Its conditional accounting result does not establish outer H1 or remove a
  parent premise.
- Existing untracked r1 candidate is immutable reference input only:
  `notes/theory/lean/YulangClosure/OriginalFormalPermissionProjection.lean`,
  SHA-256 `287908091421872e42a07214199351794f2b81d881c161797516a7f218171be3`;
  proof handoff SHA-256
  `5dd1842a36fdab29deff532f1b23d240679f659b891c411fb1803ee9ec530a84`;
  review SHA-256
  `a64d9bafde670a2c6e580741c8fc94e58b8d4b417c6e2768330ebf505f868203`.
  Do not edit or overwrite these paths. Authenticate and check exact bytes before
  reusing any declaration; preserve the recorded failed-check evidence.
- Source pins: `candidate_effect.rs`
  `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f`;
  `candidate_scheme.rs`
  `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5`;
  `shadow_apply.rs`
  `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d`;
  playground `scheme.rs`
  `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0`.
- Lean pins: toolchain `leanprover/lean4:v4.35.0`; `lakefile.toml`
  `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`;
  `lake-manifest.json`
  `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`;
  existing `OriginalEffectHygiene.lean`
  `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`;
  `WholeMetatheory.lean`
  `65777d3da4fb2a28b25e961049afb88f3ed750c30d04ae73bdc907ef5f93de26`.
- Other user/workspace edits remain out of scope and untouched. In particular
  `tools/inference-playground/src/runtime/machine.rs` and `receiving.rs` remain
  `UNKNOWN_WRITER`/QUARANTINED. No writer may read or write through those paths.

## Original outcome and measurable result

The current Lean candidate proves exporter facts for an arbitrary `Graph` but
does not construct the permission's original Function/Tuple port or the capture
map that identifies that port's exported image. The Rust implementation has
the corresponding producer/capture/export path, but its path traversal is
embedded in `CandidateGraphExport::formal_effect_permissions`.

Advance this exact gap with a paired source/proof seam:

1. The Rust lane extracts that existing traversal into a small private kernel
   used by `formal_effect_permissions`, preserving every successful output,
   source metadata, Function/Tuple branch and rejection/error branch. It must
   not change annotation semantics, solver constraints, ordinary inference,
   public APIs or runtime behavior. Reuse existing focused Rust tests; do not
   change expected output.
2. The Lean lane constructs a source-shaped formal Function/Tuple pair with
   composed polarity, allocated/shared effect ports, capture endpoint
   interning/expansion and formal-root publication. Prove that each represented
   retained permission path resolves to the captured image of its originating
   allocated port, then compose that fact with the structural export projection.
   The endpoint identity must follow from the modeled constructor/capture
   algorithm; it cannot be an assumed graph equation, `LocalLaws` field or
   invocation of the arbitrary-graph theorem alone.
3. A fresh independent reviewer checks the frozen Rust correspondence, Lean
   theorem types/axioms and whether the source identity conclusion is hidden in
   assumptions.

Before: graph-only inversion and source construction/capture notes, with no
verified identity bridge. After: a pinned, checked, independently reviewed
conditional constructor-to-export correspondence and a Rust kernel whose
observable behavior is preserved—or an exact falsifying source case/first
unsupported recurrence. This is a genuine smaller source premise, not closure
of original effect hygiene or whole soundness.

Falsifier: an actual successful originating source construction, capture and
export whose returned Function/Tuple port differs from the captured image of
the constructor-allocated permission port, or a Rust refactor changing any
existing projection success/error result.

## Owners, exact leases and stages

### Constructive Lean lane — one registered `lean_prover`

- Sole artifacts:
  `notes/theory/lean/YulangClosure/FormalPermissionCaptureConstruction.lean`
  and `tasks/agent-loop/inbox/effect-permission-construction-proof.md`.
- Scratch/build lease:
  `/tmp/yulang-effect-permission-capture-20261028-r1/lean-project/` only.
- Stage A: authenticate all listed dependencies, inspect/verify the r1 candidate
  in an isolated copy before reuse, and retain failed evidence.
- Stage B: define explicit source pair/port, polarity, capture/interner and path
  projection data; prove the constructor-port image and metadata preservation
  by structural induction over Function/Tuple paths and shared endpoints.
- Stage C: compose with successful export projection; run pinned Lean 4.35.0
  checks on every delivered theorem and complete transitive axiom audits.
  Retain failures and do not claim unverified declarations. No `sorry`, `admit`,
  project axiom or assumed source/capture law.
- Stop if the actual constructor recurrence cannot be represented faithfully
  within the pinned owners or if the image theorem requires an unsupported
  premise. Record that exact boundary and keep all parent gates OPEN.

### Rust implementation lane — one registered `implementer`, Luna/high

- Sole tracked code path: `crates/yu-solver/src/shadow_apply.rs`.
- Sole handoff: `tasks/agent-loop/inbox/effect-permission-construction-rust.md`.
- Scratch build lease:
  `/tmp/yulang-effect-permission-capture-20261028-r1/rust-target/` only.
- Inspect `candidate_effect.rs`, `candidate_scheme.rs` and playground
  `scheme.rs` read-only. Extract the exact path traversal and returned path/port
  identity from `formal_effect_permissions` into a private helper; keep the
  caller on that helper. Record a source crosswalk from formal constructor to
  capture interning/root publication to this consumer and the playground
  projection. Do not claim the playground is runtime/source acceptance.
- Run only the existing focused `yu-solver` permission-projection tests after
  the primary releases the one heavy-process slot. No new expected output,
  semantics, public API, dirty runtime file, tests in another owner or broad
  workspace suite.
- If inspection finds that the helper would add proof-hostile duplication,
  change behavior, or has no useful checked source seam, stop and report the
  exact two inspected owners and `NO_SAFE_CODE_SLICE` instead of making a
  cosmetic edit.

### Independent review — one fresh non-author `compiler_referee`

- Sole review output: `tasks/agent-loop/inbox/effect-permission-construction-review.md`.
- Review frozen Rust diff and handoff plus Lean source, handoff and checker
  records. Verify source correspondence against pinned owner bytes, theorem
  types/axioms, no hidden port-image premise, preserved result/error branches,
  exact metadata/path handling and omitted source/native cases.
- No self-review, production approval or whole-parent closure. Review only once
  both deliverables and verification evidence freeze; one batched repair/delta
  review may occur inside the same budget.

## Shared boundaries and resources

- At most two producers, zero Astra assignments, one independent reviewer.
  All other existing unknown/quarantined identities and path leases remain
  untouched. New outputs are disjoint from untracked r1 candidate files and
  quarantined runtime paths.
- 3,600 active-work seconds total: Lean 1,200; Rust 900; reviewer 450; primary
  600; dispatcher 150; contingency 300. Charge actual known overruns; do not
  reclaim unused grants or reset budgets. No automatic renewal.
- One CPU and at most 1 GiB RSS for each heavyweight verification. Only one
  Cargo/Lean build/test process may run at a time; the primary releases that
  slot sequentially. Maximum four lightweight probes and one heavyweight build
  per lane. No network, dependency changes, toolchain installation, runtime
  instrumentation or nested CLI.
- Reconsult the dispatcher at a counterexample, unsupported source recurrence,
  authority/dependency/lease/resource change, cross-lane seam or sprint end.
  Internal proof/refactor stages continue without per-step consultation.
- Whole A/B, full effect hygiene/subtraction, complete Call, whole soundness,
  required principality, progress/termination, source/native and production
  gates remain OPEN. The user goal remains active beyond this sprint.
- Luna owns current-state synchronization, review assignment/adjudication,
  staging, commit and push. Stage only this contract/current state, both frozen
  lane outputs, review and outcome. Preserve every unrelated dirty/untracked
  path. No blanket clean, stash, reset, force-push or edit to frozen main.

