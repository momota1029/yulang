# R175 activation receipt

Sprint `SOLUTION-FORMAL-READBACK/20261102-R175`; branch `yulang3`, baseline
`59fce5ec0`. The unchanged goal is Yulang type/inferred-effect soundness
against original source typing rules; runtime/machine correctness is excluded.
R174 closed incomplete after independent PASS for the bounded
`BLOCKED_SOLUTION_CARRIER` result. Parent inference soundness remains OPEN.

## Admission and frozen boundary

R175 is a read-only admission preflight: determine whether the existing
original semantics and actual inference carrier determine a pre-invocation
`FormalAssignment` from the same successful solution. Value must read the
original `Descriptor` from prepared `native_root`; Computation must read the
complete `Interface` from `native_root` plus `entry_effect`, preserving the
prior telescope and source coordinate. No `solves`, carrier identity or
readback function may be assumed. Return the exact READY input set or
`BLOCKED_SEMANTIC_AUTHORITY`; do not claim parent closure.

Contract SHA-256: `a5f02d6cbe5383262943f17637315420d2f8747219bdd750f9448d50f45ebc40`. Every listed R173/R174, Rust API and Lean source hash
matched before admission. No additional path is authorized. `candidate_context.rs`
remains excluded unless a later exact packet pins it.

## Roster and leases

Live roster synchronized before admission: Luna active; all prior agents
completed/STOPPED. No active worker displaced. Existing UNKNOWN assignments,
quarantines, 16-slot capacity receipt and runtime-path quarantines remain
unchanged. R174 source writer had stopped and its reviewed handoff was committed/pushed; its exact completed output lease was relinquished. No quarantined/UNKNOWN path lease was released.

Read-only lanes: `/root/solution_formal_readback_r175_source` (`researcher`,
600s) audits API route/callers/result semantics and prepared formals;
`/root/solution_formal_readback_r175_proof` (`lean_prover`, 900s) audits
concrete original meanings and possible same-solution registration. Both send
findings to Luna and hold no write lease. A fresh independent reviewer gets
300s after the integrated handoff freezes.

Luna's sole output lease is
`tasks/agent-loop/inbox/solution-formal-readback-r175.md`. No builds, tests,
Cargo, runtime inspection, environment/cache/target/scratch, source edits,
worker descendants or additional output paths are admitted. Worker exact-
contract acknowledgements are pending.

## Contract revision 2

The source lane identified `crates/yu-solver/src/candidate_call.rs` as the
first additional owner needed for the public candidate formal observer. Luna
pinned SHA-256 `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
before content reads. The dependency is read-only; no semantic result or write
authority changed. Updated contract SHA-256: `514b13bf3934ac9723afe3f66776a0a036f0844604e373d326dc2faab436f7ba`.

## Contract revision 3

Luna pinned the original semantic authority set named by the proof lane before
further worker reads. The exact paths and hashes are in contract revision 3;
their purpose is to distinguish source-side authority from the still-missing
Rust-solution interpretation. Luna had hash-verified these files before its
initial bounded orientation read. No worker had read them under revisions 1
or 2. Updated contract SHA-256: `7660e19661ecf4d6d3fbf2ee51c7ab699952ce5966c3f07aa3d9dde32f0e5f9f`.

## Source lane finding (revision 2)

The source researcher stopped after the pinned `candidate_call.rs` trace. The
ordinary public `SolvedModule::solve` path and default-off candidate route are
distinct; successful `Ok` results can retain conflicts. The candidate
computation-source observer exposes prepared `native_root`/`entry_effect`
handles for Computation, while its Value branch returns `None`; a different
Call observer can expose an authenticated Value root only for a formal-use
Call. These are structural observations, not source Descriptor/Interface
readback or parent solution semantics. External caller coverage is unverified.
No source output file was written.

The proof researcher acknowledged contract revision 3, verified all 28 frozen
input hashes before reading the newly admitted authority sources, and resumed.

## Contract revision 4

The proof lane identified an existing annotation/effect policy explicitly
delegated by the pinned directional effect addendum for annotated callback and
Computation cases. Luna hash-pinned
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` at
`a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` before
its content is read. This is an existing semantic correction, not a new user
choice. Updated contract SHA-256: `28e6e31c0dfdbfe6da6cc611cd0a0aa40b7d133d6b1fd5802ba31a7749be88a9`.

The proof worker stopped at this unpinned boundary after reporting that the
authority documents retain independent Descriptor/Interface interpretations,
source scopes and effect rules; no Rust solution readback equation was found
in the frozen set. Those are bounded findings, not an exhaustive absence claim.

Proof lane acknowledged revision 4, verified all 29 frozen dependencies before
reading the existing annotation/effect policy, and resumed.

## Contract revision 5

The proof lane read annotation/effect policy §1.1–1.2 under revision 4. It
confirmed that the policy does not choose a solver representation or close
source-subtraction/hygiene gates, and preserves the original provider,
assignment, typed position, shared variables and correlated Function
obligations. It points to the existing 2026-10-16 declared-envelope correction
and receipt, whose exact hashes are pinned in revision 5 before those contents
are read. The correction is integrated at `cfded839e`; no new semantic choice
is requested. Updated contract SHA-256: `ff99c7a8a633d5ecdf54c9fb0aaadb32ca8c0ea4d4a4fee41e209152b783409b`.

Proof lane acknowledged revision 5 and verified all 31 hashes before reading
the approved 2026-10-16 effect-envelope correction and receipt.

## Contract revision 6

The v5 receipt named two actual annotation/type-construction correspondence
owners as the consuming evidence. Luna pinned their exact hashes before new
reads; both are existing source correspondence, not a new semantic choice.
The receipt expressly leaves complete source/native Result/context and
subtraction proofs open. Updated contract SHA-256: `8648768e6130022fe3052a216f4755392987b281a9cda9a193e85237b7d7c316`.

Proof lane acknowledged revision 6 and verified all 33 frozen dependencies
before reading the two existing actual-owner correspondence documents.


## Contract revision 7 and frozen outcome

The source typing/effect authority was already present in the pinned inputs.
The missing fact is registration of the actual successful inference solution
and its original Descriptor/Interface readback. Revision 7 separates
`BLOCKED_SOLUTION_REGISTRATION` from a genuine `BLOCKED_SEMANTIC_AUTHORITY`;
no new semantic choice was identified. Updated contract SHA-256:
`db9e77b97ec86ef32e8de0ababc3b5daa25ef09d4b961cbe8153c4a5cb0f22ca`.

Both R175 lanes are confirmed stopped. The proof lane delivered a source-level
Lean declaration audit, not freshly Lean-printed types or a theorem. Luna's
integrated handoff is
`tasks/agent-loop/inbox/solution-formal-readback-r175.md`, SHA-256
`7c3f30d1938c10ccd843c153aae10665552c8d123d999b4de4769af4cc03621c`. Outcome: `BLOCKED_SOLUTION_REGISTRATION`; original parent
`InferenceSoundness` remains OPEN. Review was pending at the handoff freeze; its
final PASS is recorded below. No UNKNOWN rows, quarantined paths, or other
leases were changed.


## Independent review receipt

Fresh reviewer `/root/r175_readback_review` returned **PASS**, with no
outstanding blocking, major or minor findings, for contract rev7
`db9e77b97ec86ef32e8de0ababc3b5daa25ef09d4b961cbe8153c4a5cb0f22ca` and
integrated handoff SHA-256
`7c3f30d1938c10ccd843c153aae10665552c8d123d999b4de4769af4cc03621c`. The
review caught and verified correction of the public wrapper/private result
return distinction (`CandidateInference::solve` versus `run_candidate`). It
confirmed the solution-registration classification, unchanged parent quantifiers
and shared witness, whole-telescope boundary, and declared-permission/inflow/
residual distinctions. Parent remains OPEN; no theorem or production gate
closed. Review was read-only; no builds/tests/Lean/Cargo/runtime/Git.
