# NATIVE-EXTERNAL-EFFECT-FRAME/r8

Status: ADMITTED by Luna after source snapshot and all manifest entries were authenticated.
Branch: `yulang3`. Baseline: clean source commit `7b3ad7074` with exactly the three frozen R7 Rust candidate files overlaid. R7 remains CLOSED_INCOMPLETE/REJECTED; this is a distinct packet, not an R7 revision.

## Original goal and bounded outcome

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness` in `notes/theory/lean/YulangClosure/Contracts.lean`:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceProblem.NativeCorrespondence` remains separate. Preserve the original quantifiers, full supported source domain, one shared source witness, immutable-birth Value qualification, and annotation-effect hygiene policy. No parent or production gate is promoted.

This packet has two independent outcomes:

1. **Conditional external-effect frame:** construct `YulangClosure.NativeExternalEffectFrameR8` for the admitted `sample_f4_resources` callback path. Preserve all callback Result/panic prefixes and model `Sink` checksum/failed/count, `BufWriter` buffer, external file trace, excluded-interval-before-baseline ordering, and the `write_all` partial-progress/result boundary. Keep publication-before-callback, completed-trace argument evaluation, TLS trace return, and detached matrix mutation/panic/restore as distinct prefixes. State every external interface premise in theorem types; do not assume that I/O preserves the launch-evidence projection. Derive the model state's separation from the pinned source owner/field structure. If the source-to-interface bridge cannot be justified without an extra assumption, deliver only a clearly conditional candidate and leave source correspondence OPEN.
2. **Frozen Rust witness check:** verify the exact R7 rev1 test-gated physical-bound helper repair on a new isolated snapshot copied from `7b3ad7074` with the three exact R7 files overlaid. Do not edit Rust source, test source, fixture text, dependencies, expected outputs, or semantics. The target is `replay_constructor_lineage_observes_rejected_cross_route_authentication`.

R7's missing theorem and external-I/O obstruction remain recorded. R7 rejection grants no checks or edits; any R8 check below is authorized only by this separately admitted contract and its review gate.

## Exact immutable inputs

- Rust/check tree: `isolated/native-external-effect-frame-r8/`, a clean archive of commit `7b3ad7074` with only these R7 rev1 files overlaid:
  - `crates/yu-solver/src/candidate_scheme.rs` SHA-256 `c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d`
  - `crates/yu-solver/src/candidate_context.rs` SHA-256 `19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec`
  - `crates/yu-solver/src/candidate_extrusion.rs` SHA-256 `2fa4cdf965785fc43ff9792af36c1dd86a01d50cf863229de2ddb721878d2477`
- Proof source: the exact 19-entry read-only input manifest `tasks/agent-loop/sprints/native-readback-and-callback-20261028-r7-proof-inputs-r2.json`, SHA-256 `e49700a9c8e446633de567c3cafe6ce6eb71d77ca42a393b0c6164c5b93d1aec`, rooted at `isolated/native-readback-and-callback-r7-proof-input-r2/`.
- R7 provenance: contract, amendment 01, Rust handoff, proof obstruction handoff, independent review, and outcome as pinned in `tasks/agent-loop/sprints/native-external-effect-frame-20261028-r8-inputs.json` (SHA-256 `076b26e9fd35fb60cdc3ce4ca0cab926a424ca3b64cd22aa45b28ae49ecda577`).
- Workers authenticate the manifest and every assigned input before reading bodies. Proof bodies are read only from the immutable 19-file snapshot. No transitive path expansion is implied.

## Leases and resources

Aggregate envelope: 1,800 seconds, no renewal. Astra: 0.

- Luna source/admission/snapshot preparation: 300 seconds. Luna primary verification/checks/integration: 400 seconds. No separate Rust writer assignment.
- Registered `lean_prover`, Sol/high: 700 seconds, one Lean source and one proof handoff.
- Fresh `compiler_referee`, Sol/medium: 400 seconds, one review receipt.
- No Rust writer worker. Luna owns one conditional Cargo check after review acceptance.

Exact writes:

```text
Proof:
  isolated/native-external-effect-frame-r8/notes/theory/lean/YulangClosure/NativeExternalEffectFrameR8.lean
  tasks/agent-loop/inbox/native-external-effect-frame-r8-proof.md
Reviewer:
  tasks/agent-loop/inbox/native-external-effect-frame-r8-review.md
Primary:
  tasks/agent-loop/current.json
  tasks/agent-loop/history/native-external-effect-frame-20261028-r8-outcome.md
  isolated/native-external-effect-frame-r8/build-target/        # only after acceptance
  isolated/native-external-effect-frame-r8/notes/theory/lean/.lake/ # only after acceptance
  isolated/native-external-effect-frame-r8/logs/cargo.argv       # only after acceptance
  isolated/native-external-effect-frame-r8/logs/cargo.stdout     # only after acceptance
  isolated/native-external-effect-frame-r8/logs/cargo.stderr     # only after acceptance
  isolated/native-external-effect-frame-r8/logs/cargo.resources.json # only after acceptance
  isolated/native-external-effect-frame-r8/logs/lean.argv        # only after acceptance
  isolated/native-external-effect-frame-r8/logs/lean.stdout      # only after acceptance
  isolated/native-external-effect-frame-r8/logs/lean.stderr      # only after acceptance
  isolated/native-external-effect-frame-r8/logs/lean.resources.json # only after acceptance
```

No other scratch, formatting, generated outputs, source edits, or path expansion is authorized. The proof worker runs no Lean/Lake/build/check. Reviewer runs no checks, Git or descendants.

## Review and conditional verification gate

Fresh source-first review must authenticate all pinned inputs and accept both the conditional Lean artifact and frozen Rust source for bounded checks. Reject if any partial external write, buffer advance, local Sink update, excluded-interval ordering, callback prefix, or panic is omitted; if a source-to-interface premise silently asserts projection preservation; if Rust endpoint reconstruction loses lane/owner/polarity; or if a frozen R7 limitation is promoted.

Only after acceptance Luna may run, sequentially:

1. Exactly one focused Cargo attempt, max 90s, 1 CPU, 2 GiB RSS:

```text
CARGO_TARGET_DIR=isolated/native-external-effect-frame-r8/build-target cargo test --manifest-path isolated/native-external-effect-frame-r8/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

2. Exactly one pinned Lean 4.35.0 direct module check, max 120s, `-j1 -M1024`, one process:

```text
lake env lean -j1 -M1024 YulangClosure/NativeExternalEffectFrameR8.lean
```

Retain full argv, versions, stdout/stderr, exit, timing, CPU/RSS, and every theorem type plus complete transitive axiom audit. The same reviewer performs final retained-log/hash review within the 400-second assignment. Rejection, failed checks, missing audits, or time/resource boundary closes R8 incomplete. No retry or revision is implied.

## Stop and non-goals

Stop on any input mismatch, new unpinned owner, unmodeled external effect, lost prefix, incompatible source/model bridge, insufficient grant, review rejection, or resource boundary. Preserve all failures and exact first obstruction. This packet does not prove the standard-library implementation, full native correspondence, the original parent, language completeness, effect hygiene, or production readiness. Unknown/quarantined paths and workers remain unchanged.
