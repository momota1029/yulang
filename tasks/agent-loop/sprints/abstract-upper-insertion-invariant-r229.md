# Sprint R229 — actual upper-insertion storage invariants

Status: **ADMITTED** by Luna on 2026-11-02 after dispatcher closeout. Branch
`yulang3`; baseline `5bfbf47a4`. This continues the unchanged Simple-sub goal.
The separate R228 AnnCallReadout authority question remains open; this sprint
does not adopt it or depend on it.

Contract revision: **2**, correcting one transcribed dependency SHA-256 only.
The source file is unchanged; no proof/owner artifact was written under rev1.

## Parent outcome and exact scope

R223 provides checked finite variable-bound quotient and all-term solution
transport, but fresh review identified that physical-row extraction and
representatives were not connected to lawful states of the actual R212
operation. Derive the strongest useful storage invariants for finite histories
that begin at `CoreProblem.initial` and advance **only** by successful calls to
`CoreState.insertPendingUpper` in
`notes/theory/lean/YulangClosure/AbstractSimpleSubCore.lean:144–193`.
Apply the resulting theorems to R223's existing physical extraction,
representative resolution, class-level and quotient results.

This is an actual partial operation, not the missing full accepted-run or
whole solver relation. It excludes lower insertion, opposite-bound replay,
extrusion, intrusion, equality/coalescing, publication, and terminal solver
acceptance. No source domain, accepted semantics, joint Function/effect
comparison or original parent quantifier changes.

Success requires checked theorems establishing, for every `problem.inputValid`
and every successful upper-insertion history from `problem.initial`:

1. Per-kind physical row counts equal the original allocation lengths and
   representative vectors remain exactly `List.range` for that kind.
2. Each physical row retains its original level and `nonGeneric` flag; all
   lower-bound lists remain empty. Prove, rather than assume, that no
   opposite-bound replay is generated in these histories.
3. Every stored upper-bound owner and every variable dependency is an allocated
   same-kind row, with the operation's dependency-level inequality. Preserve
   every original demand constraint, including duplicates, exactly as the
   multiset/permutation union of pending demand clauses and physical row
   clauses. Use the actual inserted upper bounds and full source terms.
4. At terminal pending-empty states, R223's physical extraction and resolved
   bounds equal the original demand store up to permutation; no padding,
   nonexistent row, or unallocated coordinate can enter an allocated row's
   variable-bound SCC/quotient class. Apply R223's normalized-store and
   all-term results through these proved facts.

The theorem may state the partial operation's true narrower domain and exact
preconditions, but it must not assert the generic R223 `CoreState` invariants
for arbitrary records. If any conjunct is false, freeze the smallest actual
successful history and correct only the unsupported claim.

Measured result target: discharge the accepted-state storage/representative
blocker (2) of reviewed R223. This does not by itself close a root or prove
whole-run Simple-sub soundness. Parent delta is **0** unless an unchanged
original parent application is demonstrated. Current roots **0/4**, packages
**0/5**.

## Fixed dependencies and owner inspection

- R212 operation: `notes/theory/lean/YulangClosure/AbstractSimpleSubCore.lean`,
  SHA-256 `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c`.
- R223 contract: `tasks/agent-loop/sprints/parameter-preserving-bound-cycle-quotient-r223.md`,
  SHA-256 `df9393be7ea3432ca8cf28af13610fdded5430b20b6fdf0f49668e2b83edf980`.
- R223 theorem module: `notes/theory/lean/YulangClosure/AbstractBoundCycleNormalizationR223.lean`,
  SHA-256 `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee`.
- R223 proof handoff SHA-256
  `82a30aaea95f67830f8459932c8240064831cacaba94d17188d192d27f4abcc0`; fresh
  review SHA-256
  `13050f6b4babe6cb16741a5fa263ff1ea8240e560dd20ee935f21086c7c1e311`.
- Structural constraints: `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean`,
  SHA-256 `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`.
- Generalization dependency: `notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean`,
  SHA-256 `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246`.
- Rust source owners to authenticate:
  `crates/yu-solver/src/candidate_extrusion.rs` SHA-256
  `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`;
  `crates/yu-solver/src/lib.rs` SHA-256
  `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`.

Reauthenticate exact declarations and all pins before proof. R223's reviewer
findings on generic publication coverage and non-var-var guarded readout remain
open and explicitly outside this packet. The approved mixed Function/effect
semantics stay joint; structural `Sub` is not that semantic resolver.

## Lanes and exact leases

1. **Constructive Lean proof — registered `lean_prover`, ≤2,400 seconds.** Own
   only `notes/theory/lean/YulangClosure/AbstractUpperInsertionInvariantR229.lean`
   and `tasks/agent-loop/inbox/abstract-upper-insertion-invariant-r229-proof.md`.
   Define finite successful histories from the exact initial state and
   upper-insertion operation. State/ prove each invariant and the permutation
   conservation. Derive terminal R223 applications through the actual
   hypotheses, retaining both kinds, all four Function ports, labels, optional
   fields and duplicate bounds. Do not add assumptions for the invariant under
   proof, a whole-run relation, or parent/source typing.
2. **Rust/source correspondence — registered `researcher`, read-only, ≤900
   seconds.** Own only
   `tasks/agent-loop/inbox/abstract-upper-insertion-invariant-r229-owner.md`.
   Inspect the authenticated `candidate_extrusion.rs` insertion/restoration
   path and `lib.rs` live-task dispatch. Report exact data/operation relation,
   write-before-drain ordering, replay domain, and exclusions relative to the
   R212 abstract partial operation. Do not edit Rust, run Rust/Cargo/tests, or
   infer that candidate effect resolution is structural Simple-sub.
3. **Fresh independent review — `compiler_referee`, read-only, ≤600 seconds.**
   After both reports freeze, own only
   `tasks/agent-loop/inbox/abstract-upper-insertion-invariant-r229-review.md`.
   Challenge the induction relation, failed-call exclusion, duplicate
   conservation, representative identity, row/dependency levels, both kinds,
   terminal no-padding argument and exact R223 theorem application. Reject any
   whole-solver or original-parent claim not proved.
4. **Implementation:** `NO_SAFE_CODE_SLICE`. The Rust lane is correspondence
   inspection only; no algorithm, API, compiler, or test change is authorized.

## Verification, resources and stop conditions

The user authorizes new Lean cache files in the existing pinned project only,
under the existing aggregate 64 MiB growth cap. Current cache baseline is
131,264,002 bytes. All R229 input dependencies are present in that cache. Luna
is the sole build/cache writer after the Lean module freezes. Only these new
outputs are allowed:

```text
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractUpperInsertionInvariantR229.olean
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractUpperInsertionInvariantR229.olean.hash
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractUpperInsertionInvariantR229.ilean
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractUpperInsertionInvariantR229.ilean.hash
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractUpperInsertionInvariantR229.trace
notes/theory/lean/.lake/build/ir/YulangClosure/AbstractUpperInsertionInvariantR229.c
notes/theory/lean/.lake/build/ir/YulangClosure/AbstractUpperInsertionInvariantR229.c.hash
notes/theory/lean/.lake/build/ir/YulangClosure/AbstractUpperInsertionInvariantR229.setup.json
```

All are absent at admission; stop before build if this changes or Lake needs an
additional output. Re-read `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`; resolve and verify Lean/Lake 4.35.0. Build only the
frozen module's `:olean` target and run the bundled focused declaration checker
plus complete axiom audit. One verification owner, one CPU, process `-M1024`,
one heavy Lean process, no default/full build, test, Rust/Cargo, extra
environment, worktree, project, cache directory or cleanup.

Aggregate active-work envelope: ≤4,200 seconds (proof 2,400 + Rust/source
mapping 900 + review 600; primary verification within remaining time), zero
Astra. Stop at a real counterexample, failed invariant, resource cap, newly
required transition/semantic premise or the assigned budgets. A stopped leaf
does not imply its owner stopped unless the actual receipt says so.

Luna owns verification, exact hash/state synchronization, theorem-type and
axiom audit, integration adjudication, explicit-path staging and non-forced
Git push of the intended coherent range. Dispatcher next consultation follows
a counterexample, expanded transition need, authority/resource/dependency
change, integration seam or closeout.
