# Sprint R230 — operational owner-local publication factorization

Status: **ADMITTED** by Luna on 2026-11-02. Branch `yulang3`; baseline
`9137e14caa418cd3f686fc892b9cea9502a70b5f`. This continues the unchanged
`research/simple-sub-intrusion` goal. R229 is closed and its checkpoint is
pushed. Parent roots remain open.

Contract revision: **1**. User authorization in this conversation explicitly
permits generating Lean cache artifacts. Use only the existing
`notes/theory/lean/.lake/build`; do not create an environment, worktree, project
copy, scratch cache, or additional cache directory.

## Original parent and success evidence

The unchanged parents are `SourceProblem.SourceScopedCoverage` and
`SourceProblem.PrincipalCoverage` in
`notes/theory/lean/YulangClosure/Contracts.lean`. SourceScopedCoverage requires
one solution of the generated constraints that remains `sameScoped` with the
same source witness. PrincipalCoverage additionally needs a principal solution
and factorization of every original derivation through that same scoped
witness. This packet does not prove either parent: its goal is to remove the
reviewed R223 owner-local publication blocker for R229's actual operational
histories, rather than leave factorization at fixture-only scope.

Prove a structural Simple-sub theorem for every valid problem and every R229
history starting at `CoreProblem.initial` and advancing only by successful
`CoreState.insertPendingUpper` calls. Preserve both kinds and all structural
constructors, including all four Function ports, record labels/optional flags,
tuple order and variant payloads. Compute roots from the actual query term's
variables; do not accept a supplied coverage certificate. Derive all metadata,
closure and eligibility conditions used by publication from the history and
R223 quotient facts.

Required result:

1. Derive bound-level closure and uniform capture eligibility in each actual
   variable-bound SCC from R229's preserved levels and non-generic flags.
2. Construct owner-local publication with existing
   `ScopedPublication.Published` rules and the query-computed roots. Establish
   that every queried term coordinate is covered.
3. Construct normalized publication and one valuation for every requested
   fresh use, sharing inactive anchors. Prove both directions of solution
   transport and mutual structural `Sub` factorization of the original query
   under each use.
4. Apply the result to R229 terminal histories and the actual self-cycle and
   upper-only cases. State exact premises and exclusions; do not assert source
   generation or a source-scoped witness.

Do not assume `StoppedClosed`, class-uniform eligibility, publication
equivalence, query coverage, or a shared valuation. Derive these or stop at the
first counterexample/missing operational premise. Do not add independent
effect-port comparisons as Yulang semantics. This remains a structural model.

Success is measured by replacing R223's fixture-only owner-local factorization
with a checked theorem instantiated on the R229 operation histories, and by
identifying the exact remaining source-to-parent bridge. Parent delta remains
**0** unless an unchanged original source parent is actually applied with its
same-witness premises; roots remain **0/4** and packages **0/5** absent such
evidence.

## Fixed dependencies and exact outputs

Reauthenticate before writing:

- R229 module `notes/theory/lean/YulangClosure/AbstractUpperInsertionInvariantR229.lean`,
  SHA-256 `8f2132e050ea6a0de47eb7da3685d6116d8aedf64d59b02b399204d96735946a`.
- R223 module `notes/theory/lean/YulangClosure/AbstractBoundCycleNormalizationR223.lean`,
  SHA-256 `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee`.
- Publication `notes/theory/lean/YulangClosure/SimpleSubScopedPublication.lean`,
  SHA-256 `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f`.
- Generalization `notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean`,
  SHA-256 `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246`.
- Native owner `crates/yu-solver/src/candidate_scheme.rs`, SHA-256
  `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e`;
  `crates/yu-solver/src/candidate_source.rs`, SHA-256
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`.

Exact writable leases:

- Proof: `notes/theory/lean/YulangClosure/AbstractUpperPublicationFactorizationR230.lean`
- Proof handoff: `tasks/agent-loop/inbox/abstract-upper-publication-factorization-r230-proof.md`
- Read-only native correspondence handoff: `tasks/agent-loop/inbox/abstract-upper-publication-factorization-r230-owner.md`
- Fresh independent review: `tasks/agent-loop/inbox/abstract-upper-publication-factorization-r230-review.md`

No Rust, compiler, source semantics, tests, unrelated record, or other Lean
module edits. No scratch files. Luna alone owns the build/cache and central
state/Git paths.

## Lanes, resources and verification

1. **Constructive Lean proof — registered `lean_prover`, ≤3,000 seconds.**
   Own only the proof module and proof handoff above. Reuse the exact R229/R223
   operations and existing publication/generalization relations. Continue
   related proof stages inside this envelope; preserve failed elaboration and
   counterexample evidence in the one handoff.
2. **Native correspondence — registered `researcher`, read-only, ≤900 seconds.**
   Own only the owner handoff. Inspect the pinned owners for query-root
   computation, use/capture mapping and anchor sharing. Record how actual
   consumers match or differ from R230's computed roots/valuation. Preserve
   R229's known self-pair elision and representative-change differences. Do
   not edit Rust or run Rust/Cargo/tests. If no safe implementation exists,
   record `NO_SAFE_CODE_SLICE` with both inspected owners.
3. **Fresh independent review — `compiler_referee`, read-only, ≤600 seconds.**
   Review frozen proof and owner artifacts. Challenge history-derived closure,
   SCC eligibility, computed root coverage, shared-anchor valuation, both
   transport directions, all constructors and applications. Reject assumptions
   that smuggle in publication equivalence, source coverage or principal order.
4. **Implementation lane:** correspondence inspection only; no compiler change
   is authorized or justified by the current premises.

Aggregate active-work budget ≤4,800 seconds; zero Astra. One Lean verification
owner (Luna), one heavy process, one CPU and 1 GiB per process. Re-read pinned
toolchain/config and resolve Lean/Lake 4.35.0 before build. Build only
`YulangClosure.AbstractUpperPublicationFactorizationR230:olean`, then run the
focused bundled theorem/type/axiom checker on all authored declarations.

The existing cache baseline at admission is **132,786,132 bytes**. Aggregate
growth cap is **67,108,864 bytes**, giving an absolute ceiling of
**199,894,996 bytes**. The only newly authorized cache outputs are the R230
module's `.olean`, `.olean.hash`, `.ilean`, `.ilean.hash`, `.trace`, generated
IR `.c`, `.c.hash` and `setup.json`, each under the existing `.lake/build`.
These target-specific outputs were absent at admission. Stop before a build if
Lake requires an output outside this exact whitelist or the aggregate cap would
be exceeded. No default/full build, tests, Rust/Cargo, cleanup, or other cache
generation.

## Review, parent application and stop conditions

Freeze and hash all artifacts/dependencies before review. Luna adjudicates the
fresh review and applies any accepted theorem to the unchanged parents. Report
the exact first remaining premise and owner. The proof does not establish source
coverage, original inference soundness, principality, termination, guarded
readout, or native simulation. No production promotion follows.

Stop at a real counterexample, a missing transition/semantic premise, dependency
or lease drift, resource cap, user STOP, or assignment budget. A blocked proof
does not stop the independent read-only owner audit. Preserve unknown writers'
quarantined paths. At closeout update `current.json`, freeze one outcome with
hash, run the authorized agent-sprint static checker, and checkpoint only the
explicit coherent R230 paths after fresh independent review. Luna alone stages,
commits and performs non-forced pushes; do not include any pre-existing dirty or
untracked paths.
