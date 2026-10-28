# Sprint NATIVE-FRESH-USE-CONTEXT-COVERAGE/r5 — native restoration and effect-context observation

Status: CANDIDATE until Luna records live admission and exact leases in current.json.
Branch / primary baseline: yulang3 / 1d59e3accb3d6c2a6ead91ebc0c6a471c671c981.
Research base: bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d; clean isolated workspace with exactly the three current frozen Rust overlays below.
Prior sprint: r4 CLOSED_INCOMPLETE, outcome SHA 244a6faecfab19e1c9b8958ccbb0406b3e7b6d03b0225da2acf980161d42c84a; review SHA 39c1600e74d4661f22eaa7e1a7c498673fb1a508a9b8a352736525effcac59c1.

## Original claim and bounded outcome

The unchanged parent remains `YulangClosure.SourceProblem.InferenceSoundness` in `notes/theory/lean/YulangClosure/Contracts.lean`:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

Preserve its original supported-source domain, shared source witness, source/native correspondence, original Simple-sub A/B claims, effect hygiene, principality, termination, and executor quantifiers. This sprint does not close or weaken that parent.

**Fixed outcome:** construct the missing successful-native-execution interpretation and restoration/readback argument for FreshUse Context renaming at completed module/local consumers, or exhibit the shortest actually reachable successful Rust trace whose restored readback omits a prepared Context image or required weight. The result must materially resolve whether the source-to-native bridge used by effect-annotated FreshUse consumers is available. It must not claim the whole effect-hygiene theorem.

The selected effect policy remains authoritative and unchanged: contravariant concrete annotations grant local subtraction permission; covariant annotations allow the concrete effect at that position; actual inflow, residuals, variable connections and handler subtraction remain distinct. No source/API/semantic/production change is authorized.

## R4 evidence and required method change

R4 is CLOSED_INCOMPLETE. Its reviewer found that `completed_native_control_domain` derives facts from a handwritten `NativeRun` without interpreting actual successful Rust execution; its restoration/readback monotonicity premise is not derived from the native driver; selected-weight lemmas assume selection; and the only added Rust test constructs synthetic observations. Its mutation helper can silently omit shared-child/weight cases and lacks replacement-key mutation. Preserve R4 bytes as read-only rejected research.

R5 must use source transition read/write-footprint and interning-alias analysis, not another disconnected abstract traversal. Relate every successful `rename_contexts_impl` branch to the Lean transition relation. Analyze Replay reuse, canonical-owner/interner changes, and discharge/residual writes against the captured original roots and the exact post-restoration readback selection. No premise may simply assume seed inclusion, exact domain equality, all-image observability, or restoration noninterference.

## Exact source and authority inputs

Primary baseline is commit `1d59e3accb3d6c2a6ead91ebc0c6a471c671c981`; isolated research base is `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`. Construct a clean R5 Rust workspace from the research base and overlay exactly:

- `crates/yu-solver/src/candidate_scheme.rs` — `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`
- `crates/yu-solver/src/candidate_effect.rs` — `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`
- `crates/yu-solver/src/shadow_apply.rs` — `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`

Admitted source pins:

- `candidate_context.rs` — `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
- `candidate_extrusion.rs` — `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- `candidate_source.rs` — `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `term.rs` — `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- `lib.rs` — `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- workspace `Cargo.toml` — `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- workspace `Cargo.lock` — `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- `crates/yu-solver/Cargo.toml` — `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

Lean and theorem inputs:

- `notes/theory/lean/YulangClosure/Contracts.lean` — `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `NativeFreshScopeTransport.lean` — `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
- `NativeScopeTransformer.lean` — `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
- Lean `lean-toolchain` — `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` (Lean 4.35.0)
- Lean `lakefile.toml` — `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`
- Lean `lake-manifest.json` — `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- Lean `README.md` — `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`
- `OriginalEffectHygiene.lean` — `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` (accepted constructor/consumer seam only; not whole hygiene closure)
- selected policy `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` — `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` (read-only semantic authority; no change requested)

Read-only original-claim and correction context, inherited from r4's admitted amendment:

- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` — `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` — `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`
- `notes/design/2026-10-24-birth-level-scc-intrusion.md` — `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`
- `notes/theory/2026-10-24-birth-level-scc-intrusion.md` — `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa`
- `notes/progress/2026-10-26-inference-soundness.md` — `fd5ff5eb032e3fe276deab0213ede2e073fe0f6bf43c32daca19b6e258ba84b1`
- `docs/yulang-whole-proof-closure-ja.md` — `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`

R4 read-only research inputs:

- base contract `a7ed1ad46c45c9a69e4db807f874b709716a7265dbe9d00eaa88275c7fbda11c`
- Amendment 01 `d8f5695ff461270e52d6a27bf0f09593a48a65e5fa2f4c5f5c6b77043730d02f`
- rejected Rust source `4540af4c5f0c1c2f69f26363195a5b8b8c735c2638235aa9fd7cc390754d221e`
- Rust handoff `6ae81be632c07d7935efe787f36581c953ed62fd5650289f83bcb9db02fb097e`
- unchecked Lean source `442c41c863e33396ea0759acc2e438d41fa2cd09033c2af18d221a1357bd3ace`
- proof handoff `b2a821bd17bcfb792f5a90d95ffe8303f947970aac2f48d1a00846d5cdd2090d`
- review `39c1600e74d4661f22eaa7e1a7c498673fb1a508a9b8a352736525effcac59c1`
- outcome `244a6faecfab19e1c9b8958ccbb0406b3e7b6d03b0225da2acf980161d42c84a`

No other source owner or semantic authority is admitted. A needed new dependency requires a Luna-authored versioned amendment before body reads.

## Two continuing lanes and bounded core packet

**Implementation — implementer, Luna/high, 1,000 seconds.** Write only:
- `isolated/native-fresh-use-context-coverage-r5/crates/yu-solver/src/candidate_scheme.rs`
- `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r5-rust.md`

Add test-only source witnesses through actual module and local FreshUse consumers. Cover identity without fabricated row zero, successful empty, real pre-bound pause with observable Partial/Unavailable, shared DAG, guaranteed selected child/weight, discharged parent, restoration and post-bound readback. Independently retain roots, exact map domain/images and later admission roots. Exercise every source root and native-map delete/insert/replace-key mutation against unchanged authentic construction/readback evidence. No production logic or expected-output change.

**Constructive proof — registered lean_prover, Sol/high, 1,000 seconds.** Write only:
- `notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR5.lean`
- `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r5-proof.md`

Define transitions from the admitted Rust branch structure, prove each successful branch correspondence and exact domain, then model restoration reads/writes and derive sufficient observation of every prepared image and weight at the real completed consumers. Alternatively, deliver the exact reachable successful native counterexample. Apply any valid result as the missing premise/bridge for the unchanged source interpretation; keep inference soundness, effect hygiene, A/B, principality, termination and production gates explicitly OPEN. No `sorry`, `admit`, project axiom or unchecked theorem claim.

**Astra core proof — astra_prover, medium, at most 300 seconds and 3 substantive stages.** Attack the named core risk: Replay reuse or canonical interning may alias a captured original parent, while restoration changes discharge/residual selection. Use a multi-stage constructive source-transition/footprint argument or produce a concrete abstract candidate that Sol can test against the actual driver. Write only:
- `notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR5Core.lean`
- `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r5-core.md`

This is complementary research, not a reviewer. The main proof lane must not assume its result before it freezes; any dependency or integration needs a primary-authored versioned amendment. No checks, caches, Git or descendant workers.

## Success predicates, falsifiers, exclusions

Accept only if the frozen source establishes the promised authentic cases and every mutation is non-vacuous, and the frozen Lean result relates all successful native rename/restoration paths to those observations without assuming the conclusion. Or accept a concrete shortest successful source/native trace with the first missed image and exact constructor, rename, restoration, admission and readback states.

If all successful paths cannot yet be interpreted, report the exact first unproved Rust branch and why; the sprint remains CLOSED_INCOMPLETE. No local configuration witness alone counts as a reachable counterexample. No finite specimen proves universal source correctness by itself.

Expected outputs, goldens, diagnostics, language semantics, APIs, effect policy and production solver behavior remain unchanged. The provisional instrument is not a production fix. The original parent and all other gates remain open.

## Authority, leases, review and integration

Every worker ACKs the exact admitted contract hash, ID, requested/observed model and effort (UNKNOWN if hidden), exact output leases, remaining grant and current session BEFORE any body read. A read-before-ACK deviation disqualifies contract-compliant acceptance; do not waive it after the fact.

Freeze outputs before assigning a fresh independent read-only `compiler_referee` reviewer, requested Sol/medium per its registered role, 600 seconds, exact output `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r5-review.md`. Reviewer must ACK first, inspect source before handoffs, authenticate all hashes, assess source transitions, alias/restoration footprints, each authentic specimen and every mutation, and may not run checks.

After review acceptance only, Luna may run at most two focused Cargo attempts (aggregate 180 seconds, 2 GiB RSS, 1 CPU) and two pinned Lean 4.35.0 attempts (aggregate 240 seconds, `-j1 -M1024`), one heavy process at a time. Reject means no tests/build/Cargo/Lean/Lake. Primary verification/integration budget 500 seconds; contingency 200 seconds is not producer authority. No budget carries from r4.

The live roster at admission: /root RUNNING; all listed children completed; no child RUNNING/WAITING. One unreconciled `/root/effect_permission_module_environment_source` assignment remains UNKNOWN and its exact path remains QUARANTINED. The prior user capacity release of its exact eleven identities remains idempotently applied; do not count released assignments twice. Capacity plan: primary + the still-UNKNOWN assignment + implementation + proof + Astra + reserved reviewer = 6. Preserve all UNKNOWN rows and every quarantine; no path is released. No new capacity override is requested.

Fresh sprint envelope: 3,600 seconds = implementation 1,000 + proof 1,000 + Astra 300 + review 600 + primary 500 + contingency 200. At most six active/reserved/unknown assignments including coordinators/leaves, one Astra assignment, three Astra stages. At most four lightweight probes and one heavy build/test, 1 CPU/1 GiB/120 seconds per lightweight probe unless stricter; all aggregate caps above govern checks.

## Frozen outputs, stop and push

R5 candidate Rust workspace overlays are assembled by Luna and hash-checked before producer ACK/body reads. Both production and proof artifacts freeze before review. If accepted and pinned checks/audits pass, Luna integrates the coherent intended subset only; no worker Git.

Luna alone stages explicit paths after inspecting the entire outbound range and current branch/upstream. Push a small coherent checkpoint to the current branch after review and checks. Never force-push or include unrelated tracked modifications, untracked research artifacts, pending questions, scratch/build outputs, or quarantined paths.

At sprint end, archive unique outcome with exact hashes, per-lane budget charge/runtime (UNKNOWN when unobserved), reviewer verdict, checker status, all remaining parent/effect gates, and next actionable seam; sync current.json and run the static checker.
