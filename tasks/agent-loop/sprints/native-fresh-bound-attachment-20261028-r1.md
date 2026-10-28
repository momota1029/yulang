# Sprint NATIVE-FRESH-BOUND-ATTACHMENT/r1 — per-bound FreshUse attachment

Status: CANDIDATE until Luna records admission and exact leases in `current.json`.
Primary branch `yulang3`; primary baseline `f83a5f84be91f6da6213c12193121c56b2ccafcf`.
Research base `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`.
R5 is `CLOSED_INCOMPLETE`; outcome SHA `48f8b049d9d9120cc8e68306074ef5249673f6772bc236c845d64f466b5c1075`; review SHA `2070fffef29d9c692a394981453373a7b46964ae75636e6ef669c7ea7207e97e`.

## Original claim and fixed boundary

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness` in `notes/theory/lean/YulangClosure/Contracts.lean`:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

Preserve its supported-source domain, lawful finite-history domain, retained extrusion occurrence, shared source witness, source/native correspondence, original Simple-sub A/B claims, effect hygiene, principality, termination, and executor quantifiers. This packet does not close or weaken the parent.

The effect policy remains fixed: contravariant concrete annotations grant local subtraction permission; covariant annotations allow the concrete effect; actual inflow, residuals, variable connections, and handler subtraction remain distinct. No semantic, public API, production solver, expected-output, golden, or diagnostic change is authorized.

## R5 reviewed failure and exact unresolved premise

R5 established useful source footprint facts but was rejected. Its review found identity confused with physical row 0, a map-image mutation not observed by the predicate, effective roots conflated with retained raw roots, loss of per-bound ownership/multiplicity, missing authentic cases, and no successful native-driver interpretation.

The exact target here is the time-separated per-bound relation:

```text
captured bound identity and original parent
  → preparation-time key ↦ image
  → later admission cause and effective root
  → mapped relation and child raw context
  → completion/restoration
  → actual borrowed readback for that same bound
```

Preparation records effective parent roots before restoration. Admission later rereads the parent's effective root; the child stores its mapped image as a raw context. Raw constructor retention alone does not prove that the prepared image is attached or selected. Preserve each source bound's identity, antecedent, use origin, parent, key→image association, mapped relation, admission state, raw context, completion, and readback association. Keep logical identity separate from allocated nonidentity rows. Distinguish mutable effective roots from retained raw constructors. Analyze Replay/full-key interner aliasing and discharge/residual writes without assuming that all prepared images are observable.

## Exact admitted input pins

Rust source in the clean research workspace is assembled from the research base and exactly these overlays:

- R5 candidate instrument `candidate_scheme.rs`: `7fd3e16f2a6f856b925e2675d8a485fc25b90775a4b5a81f39d027c71874ef4a`
- `candidate_effect.rs`: `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`
- `shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`

Other admitted Rust owners:

- `candidate_context.rs`: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
- `candidate_extrusion.rs`: `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- `candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- `lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- workspace `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- workspace `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- solver `Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

Read-only R5 evidence:

- contract `6f488e11f0d1e7eb8d86fec5fc30e7fbca454faca6691255d11a71120ddab6fa`
- outcome `48f8b049d9d9120cc8e68306074ef5249673f6772bc236c845d64f466b5c1075`
- review `2070fffef29d9c692a394981453373a7b46964ae75636e6ef669c7ea7207e97e`
- Rust handoff `ef7589f15d1a163c994a792362491ca011976cf3729bbe09a42a439d16a8f9a5`
- proof handoff `0d4ea0a63bfcd7b41e076b2e0afd9c29715fb3908615e15e06b98dbdd0acb0cf`
- core handoff `f3668e20dca09c53662babf263a15c4d1dc7e9b3869aed61fbeed316966219c0`

Lean 4.35.0 and theorem/authority pins:

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `NativeFreshScopeTransport.lean`: `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
- `NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
- `OriginalEffectHygiene.lean`: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` (constructor/consumer seam only)
- Lean `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
- Lean `lakefile.toml`: `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`
- Lean `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- Lean `README.md`: `8d27e0b90fc4eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`
- selected effect policy `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- original-claim context `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`
- `notes/design/2026-10-24-birth-level-scc-intrusion.md`: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`
- `notes/theory/2026-10-24-birth-level-scc-intrusion.md`: `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa`
- `notes/progress/2026-10-26-inference-soundness.md`: `fd5ff5eb032e3fe276deab0213ede2e073fe0f6bf43c32daca19b6e258ba84b1`
- `docs/yulang-whole-proof-closure-ja.md`: `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`

No new owner or semantic authority is admitted. Any dependency change requires a Luna-authored versioned amendment before body reads.

## Parallel bounded lanes and exact outputs

**Rust implementation — registered implementer, Luna/high, 900 seconds.** Write only:

- `isolated/native-fresh-bound-attachment-r1/crates/yu-solver/src/candidate_scheme.rs`
- `tasks/agent-loop/inbox/native-fresh-bound-attachment-r1-rust.md`

Extend the test-only observation through the actual module/local FreshUse consumers. Correlate every event to an immutable per-bound owner record containing source-bound identity, antecedent, use origin, original parent, preparation-time key→image map, mapped relation, effective roots before/at admission, child raw context, completion, and same-bound borrowed readback. Treat logical identity as a logical value, never a fabricated physical row. Authenticate map keys and images as pairs. Separate effective-root changes from retained raw data. Add explicit authentic module/local specimens for identity, successful empty, real pre-bound pause, shared DAG with selected child/weight, and discharged-parent restoration. Mutations must non-vacuously reject image replacement/swap, missing image, key replacement, duplicate-bound reassociation, and wrong effective root against unchanged route evidence. No production code, public API, semantic behavior, or expected-output changes.

**Constructive proof — registered `lean_prover`, Sol/high, 900 seconds.** Write only:

- `notes/theory/lean/YulangClosure/NativeFreshBoundAttachmentR1.lean`
- `tasks/agent-loop/inbox/native-fresh-bound-attachment-r1-proof.md`

Define transitions from admitted Rust branches and derive the per-bound mapping from native source-bound/admission causes through Transport dependencies and child raw contexts to borrowed readback. Account for interner alias, Replay, discharge, residual writes, and owner/multiplicity. Prove an actual attachment condition without assuming seed inclusion, all-image observability, exact mapping, or the desired conclusion; alternatively provide the shortest exact successful reachable counterexample. Apply any result to the unchanged source interpretation. No `sorry`, `admit`, project axiom, or unchecked theorem claim.

## Success predicates, falsifiers and review gate

Accept the bounded outcome only if each authentic route is explicitly asserted, every required mutation changes the actual predicate against unchanged evidence, and a source-grounded transition proof connects every successful relevant branch to per-bound readback; or if the exact successful reachable counterexample records capture, alias key, all successful operations, completion, and first omitted image. Otherwise close `CLOSED_INCOMPLETE` with the first unproved branch. Finite specimens do not prove the universal parent.

Both producers ACK the exact admitted contract SHA, worker identity, requested/observed model-effort (UNKNOWN if hidden), exact outputs, grant and session **before any body read**. No deviation is waivable.

After both producers stop and outputs freeze, assign a fresh independent read-only compiler_referee, requested Sol/medium, 600 seconds. Reviewer ACKs before body reads, checks source before handoffs, authenticates hashes, examines identity, key→image pairing, ownership/multiplicity, authentic cases, transition/readback correspondence, and all overclaims. Reviewer runs no checker, Cargo, build, tests, Lean/Lake, formatter, or Git. Luna records the read-only verdict.

**No execution checks before reviewer acceptance.** If accepted, Luna alone may run at most two focused Cargo attempts (aggregate 180 seconds, 2 GiB RSS, 1 CPU) and two pinned Lean 4.35.0 attempts (aggregate 240 seconds, `-j1 -M1024`), one heavy process at a time. If review rejects, run no Cargo/build/tests/Lean/Lake. Static state checker remains scheduling evidence only. Primary integration/verification cap 600 seconds; unused resources do not transfer from r5.

## Live capacity, resources, stop and Git

R5 producers and reviewer are STOPPED and archived. Preserve `/root/effect_permission_module_environment_source` as UNKNOWN with its path quarantined, preserve `UNKNOWN_WRITER` and every other quarantine, and retain the already applied eleven-identity capacity release without counting it twice. Do not change capacity/path ownership without separate authority. R6 has no Astra lane. Assignment envelope is primary + still-UNKNOWN assignment + Rust producer + proof producer + reserved reviewer = 5. Total sprint grant is 3,000 seconds: Rust 900 + proof 900 + review 600 + primary 600. No contingency expands producer/check authority.

Exact output leases are admitted only in Luna-owned `current.json`. After freeze/review, archive a unique outcome with exact hashes, grants/runtime (UNKNOWN where not observed), verdict, checker status, unresolved parent/effect gates, and next seam; sync current and run `python3 tools/agent_sprint.py check`.

If the bounded outcome is accepted and permitted checks/audits pass, Luna alone stages explicit intended files after inspecting the entire outbound range and current branch/upstream, then pushes a small coherent checkpoint. Rejected research may be preserved only as clearly labeled incomplete evidence, with no production promotion. Never force-push, stage unrelated dirty/untracked work, include pending questions, or touch quarantined paths.
