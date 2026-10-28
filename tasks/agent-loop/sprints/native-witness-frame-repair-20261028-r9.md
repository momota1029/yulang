# NATIVE-WITNESS-FRAME-REPAIR/r9

Status: DRAFT FOR LUNA ADMISSION. This is a distinct bounded packet following R8 `CLOSED_INCOMPLETE / REJECTED`; it does not reopen R8. Branch `yulang3`. Baseline `7b3ad7074` plus exactly the three frozen R7 Rust overlays. Input manifest: `tasks/agent-loop/sprints/native-witness-frame-repair-20261028-r9-inputs.json`, SHA-256 `9268a0d7cd0eb3a674ba10fd2ec4dba63a25007c2f32fd513510ce44f47cc544` (76 files). No worker starts until Luna records admission and exact leases in `current.json`.

## Original goal and bounded outcome

Preserve the unchanged parent `YulangClosure.SourceProblem.InferenceSoundness` in `notes/theory/lean/YulangClosure/Contracts.lean`:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Keep the full supported source domain, original quantifiers, shared source witness, immutable-birth Value qualification, and annotation-effect hygiene policy unchanged. `NativeCorrespondence`, source/native correspondence, the parent theorem, and production remain OPEN. The only goal here is to repair R8's two local check blockers so the same conditional frame candidate and frozen Rust witness can produce retained checked evidence. R8 failed under its own contract; this packet authorizes a fresh bounded correction route.

Success evidence: the exact focused Rust fixture executes successfully on the frozen R7 witness, and the seven unchanged R8 conditional theorem declarations have checked types and complete transitive axiom audits with no `sorryAx` or project axiom. This does not prove `extract`, standard-library I/O behavior, native correspondence, the original parent, or production.

## Exact inputs and snapshot

The 76-entry manifest authenticates the immutable R7 proof snapshot and its 19 inputs, R8's 38 pinned inputs, R8's final conditional candidate, proof/review/outcome records, all eight R8 check logs, and the initial R9 snapshot files. All 76 actual hashes were checked while preparing this candidate manifest; workers authenticate their assigned entries before reading bodies. The proof lane reads source only from `isolated/native-readback-and-callback-r7-proof-input-r2/` and the pinned R8 candidate/handoff/review/logs. It must not read the mutable R9 Rust source body. The Rust owner works only in the isolated R9 tree.

`isolated/native-witness-frame-repair-r9/` was created from `git archive 7b3ad7074` and exactly these overlays:

```text
crates/yu-solver/src/candidate_scheme.rs    c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d
crates/yu-solver/src/candidate_context.rs   19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec
crates/yu-solver/src/candidate_extrusion.rs 2fa4cdf965785fc43ff9792af36c1dd86a01d50cf863229de2ddb721878d2477
```

The initial Lean candidate was copied byte-for-byte from R8 SHA-256 `0a89a8090650a985c4dd277a4c3c6a2398039ddd7987a2460938b88e0a07a3cc` to the R9 snapshot. Do not modify, repair, or overwrite the R8 snapshot or its records.

## Leases and resources

Aggregate envelope: **1,800 seconds**, no renewal; Astra 0. Luna is sole Git integrator and owns all shared state. Exact lane budgets:

- Luna implementation lane: 300 seconds; may edit only the isolated R9 `candidate_scheme.rs` to construct the fixture's own intended retained evidence inside the owning test. Keep provenance and mutation assertions, fixture meaning, dependencies, expected outputs and semantics unchanged. Do not copy a test-local variable across Rust test scopes.
- Registered `lean_prover`, Sol/high: 600 seconds; may edit only the isolated R9 `NativeExternalEffectFrameR8.lean` and one proof handoff. Preserve all seven theorem types, `WriteAll`, every prefix, the `extract` premise, and all model state/prefix meaning. Repair only syntax/elaboration/proof terms. No adding assumptions, weakening results, source-domain narrowing, project axioms, `sorry`, `admit`, or trusted I/O projection premises.
- Fresh `compiler_referee`, Sol/medium: 400 seconds; one review receipt. Authenticate inputs, review source-first, gate the initial checks, then review any single authorized repair revision and final retained logs. No check execution, writes beyond the receipt, or Git.
- Luna primary verification/integration: 500 seconds; exactly the conditional check attempts below, retained logs, adjudication and records.

Proof handoff: `tasks/agent-loop/inbox/native-witness-frame-repair-r9-proof.md`.
Review receipt: `tasks/agent-loop/inbox/native-witness-frame-repair-r9-review.md`.
Outcome: `tasks/agent-loop/history/native-witness-frame-repair-20261028-r9-outcome.md`.
Primary shared state: `tasks/agent-loop/current.json`.

Only after independent initial review accepts both frozen outputs may Luna run, sequentially, under one CPU and 2 GiB RSS per Cargo process / one CPU and `-j1 -M1024` per Lean process:

1. At most two Cargo attempts total, each max 90 seconds and total Cargo wall max 180 seconds:

```text
CARGO_TARGET_DIR=isolated/native-witness-frame-repair-r9/build-target cargo test --manifest-path isolated/native-witness-frame-repair-r9/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

2. At most two Lean attempts total, each max 60 seconds and total Lean wall max 120 seconds:

```text
lake env lean -j1 -M1024 YulangClosure/NativeExternalEffectFrameR8.lean
```

Lean cwd is `isolated/native-witness-frame-repair-r9/notes/theory/lean`. Keep exact argv, tool versions, full stdout/stderr, exits, timing, CPU/RSS in these exact paths:

```text
isolated/native-witness-frame-repair-r9/logs/cargo-1.argv
isolated/native-witness-frame-repair-r9/logs/cargo-1.stdout
isolated/native-witness-frame-repair-r9/logs/cargo-1.stderr
isolated/native-witness-frame-repair-r9/logs/cargo-1.resources.json
isolated/native-witness-frame-repair-r9/logs/cargo-2.argv
isolated/native-witness-frame-repair-r9/logs/cargo-2.stdout
isolated/native-witness-frame-repair-r9/logs/cargo-2.stderr
isolated/native-witness-frame-repair-r9/logs/cargo-2.resources.json
isolated/native-witness-frame-repair-r9/logs/lean-1.argv
isolated/native-witness-frame-repair-r9/logs/lean-1.stdout
isolated/native-witness-frame-repair-r9/logs/lean-1.stderr
isolated/native-witness-frame-repair-r9/logs/lean-1.resources.json
isolated/native-witness-frame-repair-r9/logs/lean-2.argv
isolated/native-witness-frame-repair-r9/logs/lean-2.stdout
isolated/native-witness-frame-repair-r9/logs/lean-2.stderr
isolated/native-witness-frame-repair-r9/logs/lean-2.resources.json
```

Exact generated-path leases: R9 `build-target/`, R9 Lean `.lake/`, and only the 16 log files above. No other scratch/cache/generated paths or source edits.

## Single bounded repair round

After the first authorized attempt of each eligible check, one internal repair round is allowed within the original author budgets and exact write leases. It may address only the first-check diagnostics that are local to the admitted R9 owners. The Rust fix must put the intended retained evidence in its owning fixture without moving/changing assertions or expected outputs. The Lean fix must make the same seven candidate theorem bodies elaborate and prove the same propositions under the same assumptions. Any semantic/model mismatch, need for a stronger assumption, new source owner, fixture expectation change, dependency change, or resource boundary stops R9 incomplete.

Any changed output is frozen with a new hash, reauthenticated against its unchanged dependencies, and freshly reviewed before a second attempt. No second attempt runs against bytes the reviewer has not accepted. A passing first attempt is not repeated. No third attempt, dispatcher round, or revision is authorized. Final reviewer audit checks every theorem type and complete transitive axiom output, including the actual final bytes.

## Review, stop and interpretation

Fresh review reads source before candidate explanations; verifies the owning fixture's local witness construction and unchanged mutations/assertions; verifies theorem types are exactly preserved and no premise hides projection preservation; covers all partial I/O and callback prefixes retained in R8; and checks every `#print` plus complete `#print axioms`. It authenticates all 76 inputs and each revision/output/log before acceptance.

Stop on any input mismatch, changed protected dependency, test/expected-output change, missing source premise, lost prefix, changed theorem type, `sorryAx`/project axiom, review rejection, unmodeled owner, exceeded budget, or missing resource evidence. Preserve exact failures. A failed check may enter the one in-scope repair round only when the finding is the authorized local scope/Lean construction defect; otherwise close incomplete.

This packet does not establish `extract`, std I/O laws, exact native trace extraction, source/native correspondence, `InferenceSoundness`, effect hygiene, language completeness, or production readiness. No R8 result is retroactively promoted; all original proof and production gates stay OPEN.
