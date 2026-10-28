# Native FreshUse Context coverage — R5 Rust handoff

## Assignment and frozen inputs

- Sprint / contract: `NATIVE-FRESH-USE-CONTEXT-COVERAGE/r5`, SHA-256 `6f488e11f0d1e7eb8d86fec5fc30e7fbca454faca6691255d11a71120ddab6fa`.
- Assignment: `/root/native_fresh_use_context_coverage_rust_r5`, session `NATIVE-FRESH-USE-CONTEXT-COVERAGE-20261028/r5`.
- Requested runtime: Luna/high. Observed model and effort: UNKNOWN.
- Exact outputs: `isolated/native-fresh-use-context-coverage-r5/crates/yu-solver/src/candidate_scheme.rs` and this handoff only.
- Runtime use / remaining from the 1,000-second grant: UNKNOWN; no runtime meter was exposed.
- Direct implementation inputs stayed at the frozen hashes in the contract: `candidate_scheme.rs` baseline `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`; `candidate_context.rs` `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`; `candidate_extrusion.rs` `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`; `candidate_source.rs` `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`; `term.rs` `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`; `lib.rs` `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`; `candidate_effect.rs` `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`; solver manifest `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`; workspace manifest/lock `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a` / `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`.
- Exact r4 rejection reused: review SHA `39c1600e74d4661f22eaa7e1a7c498673fb1a508a9b8a352736525effcac59c1`; rejected Rust SHA `4540af4c5f0c1c2f69f26363195a5b8b8c735c2638235aa9fd7cc390754d221e`; rejected outcome SHA `244a6faecfab19e1c9b8958ccbb0406b3e7b6d03b0225da2acf980161d42c84a`.

## Contribution

The leased Rust file now has test-only Context coverage carried with actual `FreshUse` maps. The pre-rename observation captures every bound relation root, each root's `context_payloads` closure, and the distinct local-weight domain. After `rename_fresh_contexts`, it records the exact Context and weight map domains/images.

At completed module and local consumers, the instrumentation selects relation roots from actual `BoundAdmissionCause::FreshUse` records with the same `use_origin`, checks their count against source bounds, reads their current Context roots, and passes those actual restored relations to `retained_input`. It then compares the selected post-restoration roots against the expected mapped source roots and checks every mapped image and referenced weight against the retained evidence readback. An absent admission, missing map image, unsupported constructor (including `BothFromRight` without its retained owner), or incomplete readback returns `ReceiptMismatch` in the test instrument.

The exact pre-bound local pause status is exposed as `LocalScriptObservation.context_completion`; `DriveOne` records `Partial`, and the route becomes `Complete` only after all bound restorations and final link admission finish. Identity is retained as the logical `ContextId(0)` root and excluded from physical stored-row requirements.

The existing source-owned Display/where fixture now requires actual module and local FreshUse routes with shared non-identity Context children and nonempty weight images. Against each unchanged route observation, the test helper mutates every source root, map key by delete/insert/replace, map image, selected shared child, every target, each weight key/image/readback, a later admission root, and completion disposition. Each mutation must fail the same coverage predicate. The separate module route accounting fixture also asserts a completed actual module readback.

This is a provisional, test-only source/native observation. It does not change production behavior, APIs, semantics, effect policy, expected output, inference decisions, or the theorem status. It does not prove the universal source/native bridge or original inference-soundness claim.

## Source/native correspondence and open TODOs

The Rust correspondence observed here is:

`Graph.bounds relation roots -> Context::relation_context -> Context::context_payloads -> FreshUse Context/weight remaps -> bound restoration emissions/admissions -> same-use FreshUse admission roots -> retained_input readback`.

The source-side quantifier and judgment remain the unchanged `YulangClosure.SourceProblem.InferenceSoundness` in `Contracts.lean`. No Lean proof was changed or run by this lane. The proof lane must still relate every successful `rename_contexts_impl` branch (Replay, canonical interning, and all constructor cases) and every restoration write/read selection to this observed route without assuming seed inclusion, exact domain, image observability, or noninterference.

TODOs for Luna's frozen handoff:

1. Independently inspect that admission selection by `use_origin` and the source-bound count identify exactly the bound rows represented by each original root, including duplicate roots and any discharged/residual path. The test observation currently compares root sets after selection; it does not itself prove owner-level root-to-bound bijection.
2. Add/verify a source-authentic scripted pre-bound pause specimen that reads back `Partial` from `LocalScriptObservation` after a real `LocalRun::Paused`. The observation surface is implemented; this handoff does not claim that such a script was executed.
3. Keep R4's failed handwritten `NativeRun`, assumed selected-weight lemma, and disconnected synthetic mutation fixture rejected. The new mutation assertions are tied to actual route observations but remain unexecuted pending independent review.
4. Continue the proof-to-owner bridge for every native branch and map exact source bound ownership to the actual selected readback. Keep inference soundness, effect hygiene, A/B, principality, termination, executor, and production gates OPEN.

## Checks and provisional boundary

Not executed: Cargo, build, tests, Lean/Lake, checker, formatter, Git, cache-producing commands. R5 requires frozen producer outputs and independent review before focused checks; review has not happened. Static evidence only: source inspection, contract/dependency hash readback, and a read-only diff against the pinned scheme baseline. No executable result or successful Rust trace is claimed.

No Simple-sub bypass was restored. No output expectation, diagnostic, source domain, inference choice, or selected effect policy was changed. The selected policy remains: contravariant concrete annotations grant local subtraction permission; covariant annotations allow the concrete effect at that position; inflow, residuals, variable connections, and handler subtraction remain distinct.

## Freeze and STOP receipt

- Rust artifact SHA-256: `7fd3e16f2a6f856b925e2675d8a485fc25b90775a4b5a81f39d027c71874ef4a`.
- Handoff ID/revision: `native-fresh-use-context-coverage-r5-rust`, revision 1; handoff hash to be authenticated by Luna after receipt.
- Exact changed paths: the two leased paths listed above. No generated files, caches, scratch files, or other paths were created.
- This worker stopped writing after freezing the Rust artifact and handoff. No descendants or additional leases.
- Classification: provisional source/native observation, pending independent reviewer. This producer does not certify its own work.
- Next related step within the envelope: freeze and independently review these bytes; only after acceptance run the contract-authorized focused Rust checks. If reviewer rejects, retain as incomplete research and run no checks.
