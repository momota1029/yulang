# Sprint R212 — resume checked abstract Simple-sub core

Status: **ACTIVE**. The user explicitly authorized creating the missing Lean
cache in this turn. R211 remains frozen as `STOPPED_INCOMPLETE`; this sprint
reopens its mathematical objective without rewriting that record.
Branch / baseline: `yulang3` / `338ed55ec`.
Parent roots: unchanged `Contracts.SourceProblem.InferenceSoundness`,
`PrincipalCoverage`, `InferenceTermination`, and `SourceScopedCoverage`.

## Fixed outcome

Resume construction of the concrete endogenous abstract Simple-sub core and
prove its whole-run soundness against `CoreProblem.originalConstraints`.
Keep the original R211 theorem gate, listed Value/Effect constructors,
four-port Functions, extrusion, occurrence-qualified intrusion, and
generalization/publication boundaries. This is core mathematics only; it does
not close an original source root without an exhibited application.

## Authorized cache build and resource envelope

Only the existing pinned project at `notes/theory/lean` may be used. The user
authorized cache creation. Build only these named OLean facets, sequentially
in dependency order, with no other Lake target:

```text
Contracts
SimpleSubConstraintSyntax
SimpleSubConstraintSoundness
SimpleSubRegularSolutions
SimpleSubRegularConstraintSoundness
SimpleSubLatticeCertificates
SimpleSubGeneralizationSoundness
SimpleSubScopedPublication
SimpleSubRegularPublication
SimpleSubLatticeInference
SimpleSubLatticeDecision
SimpleSubLatticeGrowingInference
```

For each module `MODULE`, invoke only:

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= \
  /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake \
  --no-cache --fail-fast build +YulangClosure.MODULE:olean
```

Run from `notes/theory/lean`, one command at a time. Do not build default
targets, C/native facets, Rust, Cargo, a new environment, worktree, target,
scratch tree, or remote cache. Use Lean 4.35.0, one CPU, and the existing 1 GiB
Lean memory setting. The exact output whitelist and each file's initial
present/absent status are frozen in
`tasks/agent-loop/sprints/abstract-simple-sub-core-r212-artifacts.json`; that
manifest has SHA-256
`b162fbde8a83096f5bd2e5e9efe076ce07e7cfa8306e27ab551e46f1d359e1f2` and is the
cache lease set, not a directory-wide lease. Write only paths listed there; do
not delete or replace existing outputs. Stop if incremental
`.lake` growth exceeds 256 MiB (370,268,667 apparent bytes total), an invocation
exceeds 180 seconds, aggregate build time exceeds 1,200 seconds, or any frozen
dependency/input hash changes. Record newly created files and apparent and
allocated `.lake` sizes before and after each module. No cache cleanup is
authorized by this sprint.

Source import closure for the named target was inspected read-only: 12 local
modules total; 11 required `.olean` files were absent at intake. Their source
files total 321,003 bytes. The measured `.lake` baseline and current filesystem
availability are recorded in the artifact manifest; the cap remains 256 MiB
regardless of free-space readings.

After the targeted build, define and prove the R211 theorem in:

- `notes/theory/lean/YulangClosure/AbstractSimpleSubCore.lean`
- `tasks/agent-loop/inbox/abstract-simple-sub-core-r212-proof.md`

Use at most two focused pinned `check_lean.py` invocations, each capped at 120
seconds, one CPU and 1 GiB RSS. Report complete declaration types and
`#print axioms` audits. If the endogenous model or proof cannot meet the R211
gate, stop with the exact definition/proof obstacle; do not replace it with a
conditional lemma or claim source-root progress.

## Authority, leases, and review

Primary owns this contract, current state, semantic adjudication, independent
review assignment, integration, and Git. One registered `lean_prover` is the
sole writer of the new Lean module, proof handoff, and exact cache artifact
paths enumerated by the manifest. No concurrent Lean build or verification
writer may use this project.
The stop-reviewer from R211 is not the proof author; after the module and
handoff freeze, Luna assigns a fresh independent reviewer to check the
equations, non-vacuity, source-operation coverage, theorem type, and complete
axiom audit. Review is capped at 600 seconds and uses no build or cache writes.

## Parent accounting and stop boundary

R211 correctly records `0/4 roots; 0/5 packages`. Preserve that count unless
the checked core theorem is actually applied to an unchanged original parent
premise. Whole-run core soundness alone has zero `InferenceSoundness` delta.
Literal L1 remains adopted; its independent generation/readout bridge and
same-scoped source application remain open. Principality, source coverage,
source termination, and native correspondence remain separate.

Stop on changed hashes, build failure, the cache/time limits, a semantic
authority conflict, a legal accepted run falsifying the theorem, or a model
that supplies histories, successful certificates, or arbitrary graph/reference
data instead of constructing them from `initial` and `step`. Do not modify
pending typed-Union questions or unrelated dirty/quarantined paths.
