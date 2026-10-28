# Sprint EFFECT-PERMISSION-SOURCE-ORIGIN-20261028/r1

Status: ADMITTED after selector consultation and closure of
EFFECT-PERMISSION-LIVE-CAPTURE-20261028/r1 as CLOSED_INCOMPLETE. The user's
broad Yulang inference/executor soundness goal remains unchanged and active.

Baseline: branch `yulang3`, commit `3de302c74`.

## Goal and governing semantics

Connect actual source-approved construction of retained formal permissions to
the correct parameter row, live capture, and the existing permission export
path. The prior 25-theorem Lean result remains conditional research mathematics.
The prior Rust trace fixture captured `parameter` instead of the constructed
row `parameter_live_base + parameter`; its empty `negative_formal_roots` result
is withdrawn as evidence of formal-root non-arrival. Preserve its bytes and
review as historical evidence; do not edit them.

Preserve the Authoritative rules in
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5 and
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`: contravariant
`[E]` grants local subtraction permission, only actual handler inflow is
subtracted, symbolic dependencies remain, and independent same-row lineages
remain distinct. Do not alter language meaning, source preflight/refusal,
solver-choice, recovery, APIs, expected outputs, or runtime behavior. The
original parent `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1, 3, 5 and all whole-language obligations remain OPEN.

## Frozen source and dependencies

Hashes at admission:

- `crates/yu-solver/src/candidate_effect.rs`:
  `f0b08ea8cee26e372b2a2e0b8076b82e4e6e29fa73618fe9cddfe360df117b8f`
- `crates/yu-solver/src/candidate_scheme.rs`:
  `33c066da527c3251d106aa9ca9a4f77d3f54844478ea2f6f2258933a5eb30852`
- `crates/yu-solver/src/shadow_apply.rs`:
  `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`
- `crates/yu-solver/Cargo.toml`:
  `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- Prior checked live-capture model:
  `notes/theory/lean/YulangClosure/FormalPermissionLiveCapture.lean`,
  `0e1bd4f2ae95e798561e014595e66ec9b6d9b342dbd2b15d0d5c9d346838c53e`.
- Prior construction catalog:
  `notes/theory/lean/YulangClosure/FormalPermissionCaptureConstruction.lean`,
  `181d5075e2fa3ed5f4adfe4029b368461638b6ac6f62341ec165e6e3980ee13c`.
- `OriginalEffectHygiene.lean` `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`;
  `WholeMetatheory.lean` `65777d3da4fb2a28b25e961049afb88f3ed750c30d04ae73bdc907ef5f93de26`.
- Annotation authority `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`;
  inference principles `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`;
  original parent `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
- Lean toolchain `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`;
  lakefile `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`;
  manifest `058325944d936e85c1f601e68e3147f790dbbd0d0286357949466ce1ad3504c3`.

All runtime `UNKNOWN_WRITER` leases and every quarantine remain untouched.

## Rust source-qualified observation lane — one `implementer`, Luna/high

- Sole write leases:
  `crates/yu-solver/src/candidate_effect.rs`,
  `crates/yu-solver/src/candidate_scheme.rs`, and
  `tasks/agent-loop/inbox/effect-permission-source-origin-rust.md`.
- Scratch only:
  `/tmp/yulang-effect-permission-source-origin-20261028-r1/rust-target/`.
- Correct the capture input using the constructor's checked parameter-row
  mapping. Assert that the captured root is the row linked by the same
  constructor/domain identity; retain occurrence/path, row, endpoint identity,
  canonical representative, LIFO intern/pop/expand, row/bound/evidence/context,
  root publication, structural walk and returned effect port.
- Fix the eager test-build endpoint formatting finding by constructing trace
  text only inside the enabled recorder path. Keep all recorder behavior under
  `#[cfg(test)]` and ensure disabled observation adds no event allocation.
- Add a separate attempt through the ordinary source-solve entry and actual
  definition capture/export without bypassing preflight. If source preflight
  refuses the case, preserve the exact refusal owner and stage. Do not change or
  bypass that refusal. Label an internal-only trace as such.
- If a safe observer or approved route is unavailable, stop with
  `NO_SAFE_CODE_SLICE` and owner-specific reasons.
- At most four lightweight inspections and one focused Cargo invocation after
  code freezes. Before execution, confirm at least 4 GiB available memory and
  that the heavy slot is free. Use one CPU, <=2 GiB RSS, <=180 seconds, and this
  leased target directory. Exact test filter and final command go into the
  handoff before launch. No retry. Stop on timeout, RSS breach, source refusal,
  another owner, or changed solver behavior.

## Lean source-origin lane — one registered `lean_prover`

- Sole repository outputs:
  `notes/theory/lean/YulangClosure/FormalPermissionSourceOrigin.lean` and
  `tasks/agent-loop/inbox/effect-permission-source-origin-proof.md`.
- Scratch only:
  `/tmp/yulang-effect-permission-source-origin-20261028-r1/lean-project/`.
- Preserve both prior Lean modules unchanged. Model the actual successful
  recursive constructor with scoped symbol/view memo hits and misses, fresh
  allocations including delegated `candidate_signature_effect` allocation,
  and explicit metadata/path/allocated-row witnesses. Derive `Origin`; do not
  assume it or the memo result as a free premise.
- Relate the exact parameter/domain/root identity and canonical endpoint keys
  to the live capture trace. State concrete LIFO node writes and row/bound/
  evidence/context discovery recurrence explicitly. Prove only the transitions
  actually represented; if a universal recurrence is unsupported, freeze the
  strongest checked sub-result and identify its first missing source transition.
- Preserve explicit membership requirements: numeric `idxOf` equality alone
  does not prove the endpoint exists, a root arrived, or a port was exported.
- At most four lightweight probes and one pinned Lean 4.35.0 check, one CPU,
  <=1 GiB RSS, <=120 seconds. Preserve failures. No root/default-target
  integration without separate primary authority.

## Independent review, success and falsifier

After both lanes freeze, Luna assigns one fresh read-only `compiler_referee`;
the primary transcribes its message to
`tasks/agent-loop/inbox/effect-permission-source-origin-review.md`.
Review the corrected offset and assertions, source-preflight route, constructor
memo/allocation model, canonical transport, exact live recurrence, complete
Lean theorem types/axioms, trace/source identity and all assumptions.

Success: a checked constructor-derived origin connected to the correct
parameter/root and source-qualified capture/export, or a precise source
refusal/unsupported recurrence with the parent premises preserved. A valid
source-approved live trace that violates the proposed relation is a falsifier.
A finite trace remains finite evidence, not universal proof.

## Resource envelope and boundaries

Total: **2,700 seconds**: Rust 600; Lean 1,200; review 300; primary 200;
dispatcher 100; contingency 300. At most two producers, zero Astra. One
focused Cargo invocation and one pinned Lean heavy check; serialize heavy
processes. No automatic renewal. Only Luna synchronizes current state, adjudicates,
stages exact paths, commits and pushes. All Simple-sub A/B, effect-hygiene/
subtraction, whole soundness, principality, progress, termination, source/native
and production gates remain OPEN unless their original obligations are
separately closed.
