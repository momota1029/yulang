# R163 outcome — typed Alt licensing

Status: **CLOSED_INCOMPLETE**. The requested non-leaf typed Alt case was not
constructed; no new theorem declarations or semantic instances were added.

## Findings

The admitted target was the first missing selected Alt input for the unchanged
R159 `SourceAppAdmissionR159.app_admission_iff`. The proof lane found that
`SourceContributionConstruction` already contains the conditional selected
branch projection and receiver insertion/readback. Its `Relations.alternative`
family is supplied for arbitrary child/result relation types; it does not derive
the original typed Union clause's selected branch/result relation or the
dependent governed-field equations needed to identify projected fields in the
original result schema. Supplying that map as an assumption would restate the
missing obligation, so the contract's missing-owner stop condition applies.

The exact missing owner is the original typed Union clause constructor at the
native signature/IF intake: construct the branch/result relation and dependent
field correspondence from authoritative typing and local evidence, then apply
the already available guarded Alt projection. This is an open source
interpretation prerequisite, not a counterexample or semantic change.

## Lane outcomes and review

- Rust lane: **`NO_SAFE_CODE_SLICE`**. Five previously reviewed clean owners
  retain structural endpoints but construct no selected typed Alt witness,
  dependent field evidence or licensed consumer. The source map was independently
  reviewed **PASS**, no findings. Handoff SHA-256:
  `e1070d37f7dcd8316ff01564b3841b857bc43acfc1a6d0f165384a7c96a64935`.
- Lean lane: existing conditional Alt projection was identified and reused as
  the boundary. Pinned Lean 4.35.0 build/direct audit and the unchanged audit
  validator passed; no build was rerun by the reviewer. Four complete reused
  theorem types were audited, each with `[propext]`. No typed Alt theorem was
  added. Proof/source obstruction review: **PASS**, no findings.
- Original P and independent A remain OPEN, as do source/native closure and
  production readiness. R161 remains conditional; R162's graph diagnostic is
  not elevated to a counterexample.

## Frozen artifacts

- Contract: `tasks/agent-loop/sprints/effect-permission-typed-alternative-licensing-20261102-r163.md`
  SHA-256 `0fe3e9eca97fe3ce41a9d5178120ac4d3aac8975fbc8ff6ad1b6a46ebb805ec9`
- Lean module: `notes/theory/lean/YulangClosure/TypedAlternativeLicensingR163.lean`
  SHA-256 `990386ef000a00de35d9f341471da58d7e77b6def7048389b718ef65d3fc7957`
- Note: `notes/theory/2026-11-02-typed-alternative-licensing-r163.md`
  SHA-256 `e3900b4a594d0fc2cf717d45996266d9d0427dafe2e42747ab582f901dabefea`
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-typed-alternative-r163-proof.md`
  SHA-256 `76e2b88047c29d62c0117f1eefbf642b19a84fd3fb6621cc7f530a1e4c16cf01`
- Rust handoff and review are recorded in the R163 history/inbox pair and were
  pushed in commit `3e0facdc7`.

No Rust code, tests, Cargo build, new environment, cache, worktree or scratch
output was created. Unknown workers and quarantined paths were preserved.
