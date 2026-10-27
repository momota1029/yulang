# Sprint EFFECT-PERMISSION-LIVE-CAPTURE-20261028/r1

Status: ADMITTED after sprint-end selector consultation. This packet continues
the user's unchanged Yulang inference and executor soundness goal; it does not
replace or narrow the whole-language completion conditions.

Baseline: branch `yulang3`, commit `88c2fad87`.

## Goal and governing semantics

Derive the relation between an actual retained formal permission produced by
Rust construction and the port returned after Rust's live graph capture and
export. The previous checked Lean catalog result is a conditional helper only;
it does not establish actual Rust construction or capture. The first open
owners are `candidate_effect.rs:1414–1544,1658–1698` and
`candidate_scheme.rs:1713–1722,2670–2703,2784–2799`.

Preserve the Authoritative rules in
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5 and
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`: contravariant
`[E]` grants local subtraction permission, only actual handler inflow is
subtracted, symbolic dependencies remain and independent same-row lineages
remain distinct. This sprint changes no language meaning or accepted source
form. Original parent `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1, 3, 5 keeps all original quantifiers and remains OPEN.

Prior bounded result is
`tasks/agent-loop/history/effect-permission-capture-20261028-r1-outcome.md`,
SHA-256 `b34da562b35a9156cad644c10a6d534233a99b6e82addb15aa851f72b7aa5933`.
Its finite catalog theorem and tests do not remove the live-capture premise.
The user's broad objective remains active after this sprint.

## Frozen inputs

Source hashes at admission:

- `crates/yu-solver/src/candidate_effect.rs`:
  `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f`
- `crates/yu-solver/src/candidate_scheme.rs`:
  `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5`
- `crates/yu-solver/src/shadow_apply.rs`:
  `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`
- `crates/yu-solver/Cargo.toml`:
  `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- `tools/inference-playground/src/scheme.rs`:
  `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0`
- Prior checked conditional model:
  `notes/theory/lean/YulangClosure/FormalPermissionCaptureConstruction.lean`,
  `181d5075e2fa3ed5f4adfe4029b368461638b6ac6f62341ec165e6e3980ee13c`.
- `OriginalEffectHygiene.lean`:
  `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`;
  `WholeMetatheory.lean`:
  `65777d3da4fb2a28b25e961049afb88f3ed750c30d04ae73bdc907ef5f93de26`.
- Lean toolchain, lakefile and manifest hashes:
  `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`,
  `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`,
  `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

The prior untracked `OriginalFormalPermissionProjection.lean` and its proof and
review handoffs remain immutable, unrelated reference inputs. Do not edit or
overwrite them. Preserve all runtime `UNKNOWN_WRITER` leases and every other
quarantine. No access to `tools/inference-playground/src/runtime/machine.rs` or
`receiving.rs`.

## Productive lanes and exact leases

### Lean construction lane — one registered `lean_prover`

- Sole repository outputs:
  `notes/theory/lean/YulangClosure/FormalPermissionLiveCapture.lean` and
  `tasks/agent-loop/inbox/effect-permission-live-capture-proof.md`.
- Scratch only:
  `/tmp/yulang-effect-permission-live-capture-20261028-r1/lean-project/`.
- Preserve the prior `FormalPermissionCaptureConstruction.lean` unchanged and
  use its checked catalog theorem only as a separately pinned conditional
  result. Derive `Origin`, source metadata and the allocated-row witness from
  the represented successful recursive constructor; do not pass `Origin` or
  endpoint-image identity as a free source premise.
- Model the live `Capture::intern`, `pending.pop`, Function/Tuple node
  expansion, row expansion and subsequent bound/evidence/context discovery.
  Prove a simulation up to explicit index renaming and exact canonical
  representative premises; establish index stability and the actual retained
  negative-root publication condition without assuming universal root arrival.
- If the exact source recurrence cannot be represented, freeze the strongest
  checked sub-result and identify the first unsupported call/transition. Do not
  claim source/native or whole-parent closure.
- Run at most four lightweight probes and one pinned Lean 4.35.0 heavy check;
  retain every failure. One CPU and at most 1 GiB RSS. No root/default-target
  integration unless the primary separately grants it.

### Rust source-observation lane — one `implementer`, Luna/high

- Sole write leases:
  `crates/yu-solver/src/candidate_effect.rs`,
  `crates/yu-solver/src/candidate_scheme.rs`, and
  `tasks/agent-loop/inbox/effect-permission-live-capture-rust.md`.
- Scratch only:
  `/tmp/yulang-effect-permission-live-capture-20261028-r1/rust-target/`.
- Add a minimal provisional `#[cfg(test)]` observation at the existing
  constructor/capture owners. Record originating occurrence/path and allocated
  row, canonical endpoint identities, intern/push/pop/expand/row/bound events,
  retained-root publication and the returned port. The observation must not
  change solver choices, source preflight, recovery, API or runtime behavior.
  Do not introduce a successful path by bypassing an existing refusal.
- Prefer an actual approved source-to-candidate route. If only an internal
  producer fixture is reachable, label that boundary and retain source
  acceptance OPEN. If an observer cannot be isolated from solver behavior,
  stop with `NO_SAFE_CODE_SLICE` and owner-specific reasons.
- The instrumentation is provisional. Luna owns cleanup or retention after
  review; no cross-lane edits.
- At most four lightweight inspections and one focused heavy Cargo invocation
  after the trace code freezes. Use the candidate feature and a filter matching
  only the new trace test. One CPU, at most 2 GiB RSS, 240-second cap, same
  leased target directory. Before execution, verify machine headroom and
  serialize against Lean. If headroom is unavailable, leave Rust WAITING while
  Lean continues. The previous sprint observed 1,652,828 KiB RSS for a focused
  candidate-feature test build; do not repeat a 1 GiB envelope.

### Fresh independent review — one `compiler_referee`

- Read-only review of frozen Lean/Rust outputs and source pins. The role returns
  the review by message; Luna records a clearly identified transcription at
  `tasks/agent-loop/inbox/effect-permission-live-capture-review.md` under a
  primary-only lease.
- Check `Origin` derivation, constructor metadata, exact LIFO/worklist model,
  canonical endpoint and row representatives, index renaming, root arrival,
  projection and any hidden endpoint-image assumptions. Authenticate Lean
  theorem types/axioms and the Rust trace. A finite observed trace is source
  evidence, not the universal invariant.
- No self-review, production approval or whole-parent closure.

## Success, falsifier and resource envelope

Before: a checked finite catalog model, a Rust export-path extraction and an
OPEN actual constructor/live-capture bridge. After: an independently checked
source-derived `Origin` plus a live worklist simulation that applies to the
original parent, and an authenticated real construction/capture trace—or a
precise unsupported source recurrence/`NO_SAFE_CODE_SLICE` with the parent
premise retained. Falsifier: a valid live trace violates the proposed
simulation; an actual exported wrong port additionally retains original
occurrence/path identity.

Total envelope: **3,600 seconds**: Lean 1,200; Rust 900; review 450; primary
300; dispatcher 150; contingency 600. At most two producers, zero Astra.
Serialize all heavy Cargo/Lean processes. Heavy invocation maximum: one Cargo
and one Lean check. No automatic renewal. Stop the Rust run on timeout, RSS
over 2 GiB, altered artifact hashes, source refusal or changed solver behavior;
no retry. Charge actual known overruns and preserve full parent scope.

At sprint end or a material blocker/counterexample/authority/dependency/lease
change, consult the dispatcher. Internal related proof/refinement steps stay
inside these limits. Luna owns current-state synchronization, adjudication,
staging, commit and push; workers never use Git. Keep all Simple-sub A/B,
effect-hygiene/subtraction, complete Call, whole soundness, principality,
ordinary progress, termination, source/native and production gates OPEN unless
their original obligations are separately closed.
