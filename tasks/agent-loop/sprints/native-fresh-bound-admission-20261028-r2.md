# Sprint NATIVE-FRESH-BOUND-ADMISSION/r2 — actual emission to same-bound readback

Status: CANDIDATE until Luna records admission and exact leases in `current.json`.
Branch `yulang3`; primary baseline `23a7028cf0b3eeef5e0d601f145fecc4112539e9`.
Research base `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`.
R1 remains `CLOSED_INCOMPLETE`; its eligibility failure is not changed. R1 review SHA `a18c4c255b116435a9a51b34fa76deb0a09121a3199307063b64df033cad905b`; outcome SHA `fe52daae6f64d959ef8e0aa1a58bcfc476075954207d77d5b7105de06084e701`.

## Original parent and fixed boundary

Preserve the original `YulangClosure.SourceProblem.InferenceSoundness` claim and all its quantifiers:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

Keep the supported-source domain, lawful finite histories, retained extrusion occurrences, shared witness, source/native correspondence, Simple-sub A/B claims, effect hygiene, principality, termination and executor obligations fixed and OPEN. The selected effect policy is unchanged: contravariant annotations grant local subtraction permission; covariant annotations allow the concrete effect; actual inflow, residuals, variable connections and handler subtraction stay distinct. No semantic, public API, production, expected-output, golden, or diagnostics change is authorized.

R1's proof producer read the Lean README body before finding the base packet's malformed 63-character hash. Amendment 01 recorded this as a non-waivable R1 procedure deviation and prohibited R1 acceptance/checks. That disposition is final for R1 and does not carry over as evidence or authority. For this packet Luna has re-authenticated every pin below, including the corrected README hash; each producer and reviewer must ACK exact contract hash and exact write lease before any source/artifact body read.

## Bounded target

Authenticate this actual per-bound chain:

```text
ordinal/source_bound/antecedent/use_origin
  → mapped relation
  → admitted relation (may differ on an unscoped route)
  → driver-returned emission ID
  → physical relation slot
  → same-bound completed raw readback
```

Record mapped and admitted relation IDs separately. Follow the driver-returned emission ID and existing admission/emission iterators; preparation copies, root-set equality, relation counts, or a model that directly inserts these facts cannot authenticate the native cause. Keep identity as a logical nonphysical value. Distinguish effective-root changes from raw-image loss and preserve duplicate bound occurrences. Do not claim the temporal prepared-root attachment theorem, all FreshUse coverage, or the original parent.

## Exact source and authority pins

Luna assembled the clean R2 Rust workspace from the research base and exactly these three current frozen source overlays before producer ACKs:

- `candidate_scheme.rs`: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`
- `candidate_effect.rs`: `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`
- `shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`

Admitted Rust owners/manifests:

- `candidate_context.rs`: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
- `candidate_extrusion.rs`: `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- `candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- `lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- workspace `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- workspace `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- solver `Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

Read-only R1 evidence (context only; do not use as a replacement source baseline):

- R1 contract `fd040b8a5a1702b54c06c44fa88a8316433dc950a62d453de48db3f73e2e6e2c`
- R1 Amendment 01 `51f0867e885940a163a5f9c31bd751593911830da9edfefb54788c321f17f0d1`
- R1 review `a18c4c255b116435a9a51b34fa76deb0a09121a3199307063b64df033cad905b`
- R1 outcome `fe52daae6f64d959ef8e0aa1a58bcfc476075954207d77d5b7105de06084e701`
- R1 Rust source `894e0b9d158bbcf5a7f7184eca740762ee03623e07d83bcf250fdc46bcb9edb5`
- R1 Lean source `9327161449d8f286b15af23394033b35615b8530363587ca79d22f5d1a40be9f`

Lean 4.35.0 and theorem/authority pins:

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `NativeFreshScopeTransport.lean`: `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
- `NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
- `OriginalEffectHygiene.lean`: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` (constructor/consumer seam only)
- Lean `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
- Lean `lakefile.toml`: `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`
- Lean `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- Lean `README.md`: `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`
- selected effect policy `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`
- `notes/design/2026-10-24-birth-level-scc-intrusion.md`: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`
- `notes/theory/2026-10-24-birth-level-scc-intrusion.md`: `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa`
- `notes/progress/2026-10-26-inference-soundness.md`: `fd5ff5eb032e3fe276deab0213ede2e073fe0f6bf43c32daca19b6e258ba84b1`
- `docs/yulang-whole-proof-closure-ja.md`: `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`

No new source owner or semantic authority is admitted. Any required dependency change needs a Luna-authored versioned amendment before its body is read.

## Parallel lanes and exact outputs

**Implementation — registered implementer, Luna/high, 800 seconds.** Write only:

- `isolated/native-fresh-bound-admission-r2/crates/yu-solver/src/candidate_scheme.rs`
- `tasks/agent-loop/inbox/native-fresh-bound-admission-r2-rust.md`

Starting from the uninstrumented admitted scheme source, add a test-only recorder tied to actual driver-returned emission IDs and existing admission/emission iterators. Keep source-bound, antecedent, `use_origin`, mapped relation, admitted relation, emission ID, physical slot and same-bound raw readback distinct and explicitly joined. Add authentic completed scoped and unscoped cases. Mutate antecedent, emission, mapped/admitted pairing and duplicate-bound association against fixed native evidence; require each mutation field and route to exist. Do not treat preparation copies or sets/counts as native authentication. Preserve identity as logical, never row zero. No production/API/semantic/expected-output changes.

**Constructive proof — registered `lean_prover`, Sol/high, 700 seconds.** Write only:

- `notes/theory/lean/YulangClosure/NativeFreshBoundAdmissionR2.lean`
- `tasks/agent-loop/inbox/native-fresh-bound-admission-r2-proof.md`

Define the actual successful scoped and unscoped branches from admitted Rust and derive same-bound admission/emission/readback correspondence using the returned emission ID. Preserve mapped/admitted distinction and duplicate owner identity. Do not directly insert the desired attachments into `publish` and call that a native bridge. Keep prepared-root time variation, all FreshUse routes, and the original parent OPEN. No `sorry`, `admit`, project axiom, or unchecked theorem claim.

## Review-gated execution

Both producers ACK exact contract SHA, identity, requested/observed model-effort (UNKNOWN if hidden), exact write leases, grant and session before body reads. No deviation is waivable.

After freeze, a fresh read-only `compiler_referee` (Sol/medium, 300 seconds) performs source-first acceptance review of the recorder and proof before any build/check. It ACKs before body reads, authenticates all pins/hashes, tests the source correspondence on paper, and returns ACCEPT_FOR_BOUNDED_CHECKS or REJECT. It runs no checks. REJECT means no execution.

Only after ACCEPT_FOR_BOUNDED_CHECKS may Luna run up to two focused Cargo attempts (aggregate 120 seconds, 2 GiB RSS, 1 CPU) and one pinned Lean 4.35.0 attempt (`-j1 -M1024`, aggregate 180 seconds), one heavy process at a time. Then a second fresh read-only `compiler_referee` (Sol/medium, 200 seconds) authenticates retained output/logs and performs final correspondence review; it does not rerun checks. Final acceptance requires both review stages and check receipts. A failed check or either rejection closes the packet incomplete. Primary total cap 400 seconds.

## Falsifiers, capacity and Git

Falsifiers include one successful route where mapped and admitted IDs are conflated despite differing, a driver emission not tied to its same-bound physical slot, a raw readback from another bound, duplicate-bound reassociation accepted, or a mutation accepted despite changing its named field. A valid result establishes only this admission slice; it cannot close the prepared-root temporal theorem or parent.

R1 workers/reviewer are STOPPED and their evidence archived. Preserve `/root/effect_permission_module_environment_source` as UNKNOWN and its path quarantined; preserve every other UNKNOWN/quarantine and the prior eleven-identity capacity override without double-counting. Peak assignments: primary + existing UNKNOWN + two producers + one sequential reviewer = 5. No Astra lane. Total envelope 2,400 seconds: implementation 800 + proof 700 + staged reviews 500 + primary 400. No contingency expands authority.

At sprint end archive exact hashes, resources/runtime (UNKNOWN if unobserved), both review stages, check receipts, unresolved gates and next seam; sync `current.json` and run `python3 tools/agent_sprint.py check`. Luna alone stages explicit coherent paths after inspecting the full outbound range/upstream and pushes a small reviewed checkpoint. Never force-push, include unrelated dirty/untracked files or touch quarantined paths.
