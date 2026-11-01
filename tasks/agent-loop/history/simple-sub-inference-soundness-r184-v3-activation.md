# R184 v3 activation — concrete Simple-sub inference soundness

State: admitted parent-linked mathematical proof packet. Baseline: `yulang3`
at `513af1ce8664581bd76480674e8275fb0bad1a7a`.

The user redirected the research plan from repeated owner-local source/native
investigations to parent-first mathematical proof. The backward map separates
the original `InferenceSoundness`, `SourceScopedCoverage`, `PrincipalCoverage`,
`InferenceTermination`, and later `NativeCorrespondence` obligations. R184
targets only forward type/effect soundness. Coverage waits until the one
canonical generator/constraint denotation is frozen; principality, termination
and Rust simulation remain distinct.

Contract: `tasks/agent-loop/sprints/simple-sub-inference-soundness-r184-v3.md`,
SHA-256 `PENDING`.

R184 v1 stopped before proof construction because its authenticated
`OriginalSourceEnvironment.lean` imported an unpinned source interpretation. The
proof assignment stopped with no writes/processes and both outputs absent. The
independent parent-map reviewer passed the dependency map only. V2 adds the
source interpretation, its two imported Lean owners, its three named
semantic authorities, the R184 v1 stop receipt, and the existing canonical
SimpleSub syntax/inference/soundness modules. No R184 v2 worker was launched;
v3 preserves the same 1800-second additional grant. Luna authenticated all 22 direct-input digests before
content access; exact paths and hashes are in the versioned contract.

Exact output paths were absent at reactivation:

- `notes/theory/lean/YulangClosure/SimpleSubInference.lean`
- `tasks/agent-loop/inbox/simple-sub-inference-soundness-r184-proof.md`

One `lean_prover` owns both exact outputs, at most 2400 seconds, and the sole
Lean verification/cache responsibility. The worker must preserve the original
source domain and same-solution/shared-witness theorem. Fresh independent
mathematical/source review follows the frozen handoff, 600 seconds. No Rust,
implementation, Cargo, build, test or runtime activity is assigned. No
semantic alternative may be selected without a user decision. The parent gate
remains OPEN until the full theorem is proved and independently reviewed.

R184 v1 budget accounting: 2400 seconds reserved/charged at the original proof
grant. V2 grants at most 1800 additional proof seconds (4200 cumulative of the
7200 sprint envelope). The new launch must use a fresh runtime receipt; the old
STOPPED worker is not recorded RUNNING.

The dispatcher selected inspection and reuse of the three existing mathematical
modules before any new model is defined. R184 v1's 2400-second grant remains
charged; v3 grants at most 1800 additional proof seconds (4200 cumulative of
the 7200 sprint envelope). No v2 runtime assignment or output existed.
