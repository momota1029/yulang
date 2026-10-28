# Sprint NATIVE-COMPLETED-EMISSION-READBACK/r3 — completed native readback

Status: CANDIDATE until Luna records admission and exact leases in `current.json`.
Branch `yulang3`; primary baseline `84e95affbfc96df92a8053092f3044189cbde33c`.
Research base `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`.
Prior R1 and R2 remain CLOSED_INCOMPLETE. Their reviews, deviations and
unchecked candidate artifacts remain historical context only. R1's pin-order
failure and R2's read-only Git deviation are preserved without waiver.

## Original parent and fixed boundary

Preserve the original `YulangClosure.SourceProblem.InferenceSoundness` claim and
all quantifiers:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

Keep the supported-source domain, lawful finite histories, retained extrusion
occurrences, shared witness, source/native correspondence, Simple-sub A/B,
effect hygiene, principality, termination and executor obligations fixed and
OPEN. Keep the selected effect policy unchanged: contravariant annotations
grant local subtraction permission; covariant annotations allow the concrete
effect; actual inflow, residuals, variable connections and handler subtraction
remain distinct. No semantic, API, production, expected-output, golden or
diagnostic change is authorized.

## Bounded outcome and falsifiers

Starting from the driver's actual returned emission ID, establish the completed
native chain:

```text
invocation identity → returned emission → admission → current relation
  → scoped flow → raw transformer lookup → addressed physical bound slot
```

Read the values from the completed native structures. Do not infer completed
readback from insertion receipts, preparation copies, root sets, counts or a
model that directly inserts the target facts. Keep mapped and admitted relation
IDs separate, treat root 0 as logical identity, and preserve duplicate
invocation ownership. Use the existing raw-transformer and physical-slot
readers. Include authentic scoped, unscoped and duplicate-invocation cases.

The fixed native evidence must reject mutations of antecedent, emission ID,
mapped/admitted association, duplicate reassociation, flow root and physical
slot. No required witness may be skipped. Success is only this bounded native
readback/source bridge; it does not prove prepared-root temporal preservation,
all FreshUse routes, the original parent or production readiness.

## Exact authority, baseline and dependencies

Authority: `rules/goal-driven-sprints.md`; `notes/design/2026-10-16-goal-driven-sprints.md`;
the original parent and effect policy pinned below. Original parent remains
`YulangClosure.SourceProblem.InferenceSoundness`.

Primary baseline is current HEAD `84e95affbfc96df92a8053092f3044189cbde33c`;
research workspace base is `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`.
The Rust workspace is assembled from that research base plus the exact frozen
source overlays below. Provisional R1/R2 outputs are not source inputs.

Frozen Rust source owners:

- `candidate_scheme.rs`: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`
- `candidate_effect.rs`: `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`
- `candidate_context.rs`: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
- `candidate_extrusion.rs`: `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- `candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `candidate_scope.rs`: `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`
- `shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- `lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- workspace `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- workspace `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- solver `Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

Lean 4.35.0 project and authority pins:

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `NativeFreshScopeTransport.lean`: `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
- `NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
- `OriginalEffectHygiene.lean`: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` (constructor/consumer seam only)
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
- `lakefile.toml`: `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`
- `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- `README.md`: `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`
- effect policy `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- top-level inference principles: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- intrusion source preservation: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`
- birth-level SCC design: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`
- birth-level SCC theory: `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa`
- inference soundness progress: `fd5ff5eb032e3fe276deab0213ede2e073fe0f6bf43c32daca19b6e258ba84b1`
- whole-proof closure: `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`

R2 outcome `be7203c8d00c7f7c4984eeaac82a6acc0ff7a467f435cea5bf495269bd1ddf52`
and review `f857c64b05d89c34115410e73497f7b03ca608bff20f6e8942ae583dc236c812`
are context only. Any needed pin change requires a Luna-authored amendment
before the added source body is read.

## Lanes, leases and budgets

**Implementation — registered implementer, Luna/high, 1,200 seconds.** Exact
writes:

- `isolated/native-completed-emission-readback-r3/crates/yu-solver/src/candidate_scheme.rs`
- `isolated/native-completed-emission-readback-r3/crates/yu-solver/src/candidate_extrusion.rs`
- `tasks/agent-loop/inbox/native-completed-emission-readback-r3-rust.md`

Add test-only recording and a test-only wrapper around the existing private
physical-slot reader. Join real invocation identity, returned emission,
admission, current relation/flow/raw transformer and re-read addressed slot.
Keep the observer behavior inert outside tests and do not alter production,
public API, semantics or expected outputs.

**Constructive proof — registered `lean_prover`, Sol/high, 1,000 seconds.**
Exact writes:

- `notes/theory/lean/YulangClosure/NativeCompletedEmissionReadbackR3.lean`
- `tasks/agent-loop/inbox/native-completed-emission-readback-r3-proof.md`

Derive preservation of each referenced admission/emission row, relation/flow/
transformer and addressed physical slot through every successful native child
transition to restoration completion; then derive completed lookup. Read/write
footprints must come from actual native write branches. A `DriverReturns`
assumption that asserts preservation is not closure. If an unpinned child writer
is required, stop before reading it and return its owner and first write site.
No `sorry`, `admit`, project axiom or unchecked theorem claim.

Both producers ACK the exact contract SHA, identity, lease, requested/observed
settings and session before source or artifact body reads. No deviation is
waivable. One frozen handoff per lane; scratch/generated outputs stay inside the
assigned isolated workspace or are declared before creation.

**Review and execution gate.** First, a fresh read-only `compiler_referee`,
Sol/medium, 700 seconds, reviews frozen sources and direct dependencies without
running checks. It returns ACCEPT_FOR_BOUNDED_CHECKS or REJECT. REJECT means no
execution. Only on acceptance, Luna may run focused Cargo evidence (aggregate
120 seconds, 2 GiB RSS, 1 CPU) and one pinned Lean 4.35.0 check (`-j1 -M1024`,
aggregate 180 seconds), one heavy process at a time. A second fresh read-only
reviewer (Sol/medium, 300 seconds) authenticates retained outputs, theorem types,
complete axiom audits and source correspondence without rerunning checks. Any
rejection or failed check closes this packet incomplete. Primary cap: 700 seconds.

Total envelope: 3,600 seconds: implementation 1,200 + proof 1,000 + staged
reviews 1,000 + primary 400. Astra 0. Peak new assignments: two producers and
one sequential reviewer; preserve UNKNOWN workers, reservations and quarantined
paths. No budget renewal or authority expansion.

## Completion, boundaries and integration

Success requires a frozen Rust and Lean source review accepted before checks,
retained allowed execution evidence, final independent review, authentic
scoped/unscoped/duplicate witnesses, all named mutations rejected, printed
theorem types and full transitive axiom audits, and honest parent application.
No successful native counterexample or parent theorem closure is inferred from
finite tests. If a required source is outside the pin set, stop and return to
Luna for a versioned amendment.

At sprint end record exact artifact hashes, runtime/resource receipts (UNKNOWN
if unobserved), reviews, checks, remaining premises and next seam. Synchronize
`current.json`; run `python3 tools/agent_sprint.py check`. Only Luna stages exact
intended paths, inspects full outbound range and upstream, then pushes a safe
coherent checkpoint. Never force-push, include unrelated dirty files, or touch
quarantined paths. Stop on user STOP/session end, a genuine counterexample,
material authority/dependency/lease change, review rejection or budget limit.
