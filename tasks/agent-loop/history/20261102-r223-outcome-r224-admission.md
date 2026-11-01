# R223 outcome and R224 admission — 2026-11-02

## R223: reviewed incomplete

R223 targeted a finite parameter-preserving quotient of variable-to-variable
bound SCCs. The frozen result is mathematically checked for its stated
structural scope, but it does not discharge an unchanged parent premise.

- Contract rev. 3: `tasks/agent-loop/sprints/parameter-preserving-bound-cycle-quotient-r223.md`, SHA-256 `df9393be7ea3432ca8cf28af13610fdded5430b20b6fdf0f49668e2b83edf980`.
- Lean module rev. 2: `notes/theory/lean/YulangClosure/AbstractBoundCycleNormalizationR223.lean`, SHA-256 `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee`.
- Proof handoff: SHA-256 `82a30aaea95f67830f8459932c8240064831cacaba94d17188d192d27f4abcc0`.
- Independent falsifier: SHA-256 `e7a5d0e5ae8340020e9f7664e108fe1a74416a4da62307db2ac5595523fb7eed`.
- Fresh review: SHA-256 `13050f6b4babe6cb16741a5fa263ff1ea8240e560dd20ee935f21086c7c1e311`.

The pinned R223 target build succeeded with Lean/Lake 4.35.0, one CPU and
`-M1024`. The bundled declaration checker accepted all 65 authored declarations
and their exact types and axiom audits. No `Classical.choice`, project axiom,
`sorryAx`, or proof hole was found. Standard axiom use was 4 declarations with
none, 34 with `[propext]`, and 27 with `[propext, Quot.sound]`.

The fresh referee found no defect in the submitted theorem statements, but
blocked completion on three missing applications/invariants: (1) source-derived
coverage and ownership coherence for generic shared publication factorization;
(2) accepted-state allocation, representative, retained-row and metadata
invariants for physical extraction; (3) the guarded readout correspondence for
structural recursive bounds outside variable-to-variable SCCs. The independent
falsifier supplied additional mathematical discriminators for publication
coverage. None was a source-qualified refutation.

The checked packet is not applied to `SourceProblem`. **Parent delta: 0; roots:
0/4; packages: 0/5.** R223 closes as reviewed incomplete. Do not count the local
theorem total as parent progress.

## R224: admitted continuation

I admit the dispatcher’s within-authority proposal, “paper-rule constraining
soundness,” after checking it against the local paper and current Lean
definitions. The original four roots, quantifiers, accepted source semantics,
Call, and both value/effect kinds remain fixed. R224 replaces the R223
guarded-readout dependency for this soundness route with a checked operational
constraining argument, if the approved definitions support one. It does not
close an original parent by itself.

The pinned local copy of *The Simple Essence of Algebraic Subtyping* has SHA-256
`5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698`.
Section 3.2.2 specifies that constraining inserts a bound before recursively
propagating through opposite bounds and uses a cache of comparisons. Section
5.1.2 explicitly permits `μ α . α`, with hypotheses delayed until descent under
a Function or Record constructor. Section 5.3.1, Lemma 2 states the target:
successful constraining from consistent bounds preserves consistency and gives
`E⁻ st₀ ≤ E⁺ st₁`; its proof strengthens induction with the cache and permits
temporary inconsistency for variables in that cache.

The fixed Yulang model has a concrete structural constraint syntax and
single-step preservation lemmas, including insertion/replay/extrusion/intrusion,
but `AbstractSimpleSubCore` explicitly has no complete accepted run relation.
The existing structural `Step` does not itself define the paper’s mutable bound
state, comparison cache, dynamic recursive propagation or guarded hypothesis
unlocking. These facts make exact transition authority the first gate: R224 must
construct those rules from already approved Yulang semantics or freeze the
first missing equation and its owner. It must not invent a transition, assume
`LocalLaws`, or replace the original roots with a restricted subalgorithm.

Contract: `tasks/agent-loop/sprints/paper-constrain-soundness-r224.md`.
Implementation and review receipts are linked from current state when frozen.

R223 resource receipt: the only generated output was in the existing pinned
`notes/theory/lean/.lake/build`; its apparent size increased from 124,639,889
to 131,264,002 bytes (+6,624,113 bytes, about 6.32 MiB), below the authorized
64 MiB cap. No worktree, project, environment or scratch cache was created.
The target Lean process used at most 568,228 KiB RSS. R224 retains the same
cache-only policy and cap, with its own exact whitelist.

Required repository checks passed: `python3 tools/agent_sprint.py check` and
`python3 -m unittest discover -s tools -p 'test_agent_sprint.py'` (62 tests).
These are workflow consistency tests, not Lean proof or source correspondence
evidence. No Rust/Cargo check was run.
