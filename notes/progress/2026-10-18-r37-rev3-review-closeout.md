# R37 revision 3 review closeout

## Parent result

The original theorem remains unchanged and closes no conditions: `0 -> 0`. The bounded source obstruction remains: ordinary Call does not provide the result-description owner, complete ordered telescope, or typed correspondence to `NativeInterface.result`; `TypedPortRef(R)`, typed C/D `CopyScope`, and typed publication remain open. No semantic adoption or production promotion follows.

## Frozen target

- Contract `tasks/agent-loop/sprints/authentic-apply-copy-bridge-20261018-r37-rev3.md`: `b19c4131f79476f787b8ef424e46f38a396598234dab5400215025938bd0d250`.
- Candidate `crates/yu-solver/src/candidate_scheme.rs`: `8c370e47d5e8692a618fedf41be07d7ae3ac961f9070bfed6730e2b8e2f1137e`.
- Integration test `crates/yu-solver/tests/candidate_local_self_recursion.rs`: `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55`.
- Candidate production prefix is byte-identical to baseline: 119639 bytes, `bc809becb6dc89149e2d00057f1d65b879121668f5485fef9d6a493d64f08a18`.
- Candidate progress note: `f96a77882aaef72e119450cf53a81d8a6fe01d5d897d40dc4452e51c4e1f839f`; handoff: `cb0a9dd389dcfa9bdc479429494f57f16ee09bacfde7929f4bb7b76f71b6d713`.

## Independent review results

Both fresh reviews are BLOCKED on the exact same frozen bytes. Reviews were read-only and returned final receipts; no review files were written.

1. Compiler review `/root/r37_rev3_compiler_review`, 180s charged: prior-fresh map-hit acceptance is vacuous. The all-row test requires each reconstruction-time representative to equal its final representative, while selection chooses the first capture row in the final class. On any successful join, the selected row therefore has `canonical_rows_hit=false`. The required owner-authenticated `existing_image != source_representative` acceptance is never established.
2. Compiler and spec reviews independently found a missing temporal bridge. Reconstruction records `source_representative` at `candidate_scheme.rs:1583/1602`, but the predicate later compares it to final `state.intrusion.rep(...)` at `:2245-2246`. Local-use execution and source actions can continue after reconstruction, and intrusion settlement can merge representatives (`candidate_source.rs:1675-1688`, `candidate_intrusion.rs:593/600`, solver drain at `lib.rs:12136/12372`). `ReconstructedRowObservation` retains no epoch, stability proof, or merge chain. A lawful later merge can invalidate the present-day equality. Required outcome: `MISSING_RETAINED_EVIDENCE` until an owner-authenticated temporal edge or stability invariant exists.

Other audited controls remain explicit: indexed Parent field authentication, signed C/D coordinates, both helper routes, structural trigger comparison, exact Apply event, forged-parent rejection, nonvacuous missing-event control, and negative substitutions. Those controls do not close the two blockers.

## Implementation and checks

The R3 code remains a test-only, unexecuted candidate. No Cargo, build, test, or probe ran because both clean-review gates failed. `git diff --check` and `python3 tools/agent_sprint.py check` passed; these are formatting/static-state checks only. Production code and expected outputs were not changed.

R37 budget: 4440 seconds charged before reviews; both 180-second review grants are fully charged; 300 seconds remain, but the Cargo gate is not met. The R3 repair writer and both reviewers stopped. The candidate and its reports remain frozen for the next owner decision.

## Next discriminating evidence

The source/native owner must retain the reconstruction-time identity relation across subsequent constraint settlement, or establish that the relevant representative is stable through the inspection boundary. The native test must also select an actual later canonical-map-hit row and assert that its prior fresh image is accepted. Without both, another assertion rewrite would repeat the same unsupported edge.
