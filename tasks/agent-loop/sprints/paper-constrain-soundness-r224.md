# Sprint R224 — paper-rule constraining soundness

Status: **ADMITTED** by Luna after confirming the dispatcher proposal against
the pinned paper and fixed Yulang Lean definitions. Branch/baseline:
`yulang3` / `7a4e25417a2794d3d19e9cb128060ad240d2b255`. User goal: establish
Yulang type-inference guarantees, with effect hygiene, by proving the abstract
Simple-sub model before its Rust correspondence.

## Original parents and measurable result

Keep the unchanged roots `InferenceSoundness`, `SourceScopedCoverage`,
`PrincipalCoverage`, and `InferenceTermination` in
`notes/theory/lean/YulangClosure/Contracts.lean:128–154`, with their original
quantifiers, supported source domain, shared scoped witness, Call/effect rules,
annotations and accepted semantics.

R224 targets the operational soundness lemma that is the core of the paper's
general soundness proof. A successful result is an endogenous Yulang
constraining relation and a checked theorem showing: from consistent input
bounds, every successful run preserves consistency and derives the specified
negative-to-positive coalesced inequality for the constrained terms. The
induction must account for the comparison cache, bound insertion before
propagation, and temporary inconsistency of precisely the cached variables.
Represent both Yulang kinds and all four Function ports, including both effect
ports. Inventory how extrusion, intrusion and publication affect the theorem's
state; do not silently omit them or claim a whole-run theorem if the relation
does not cover them.

This result removes the need to compile Fig. 12 output into `Graph.Guarded` for
this soundness argument, if checked against the approved equations. It does not
establish a source judgment, `sameScoped`, an original instance relation,
principality, termination, or Rust correspondence. Parent delta remains zero
unless an unchanged original root is actually discharged.

## Fixed authority and dependencies

- Local reference paper: `/home/momota1029/rust/simple-sub-reference-paper.pdf`,
  SHA-256 `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698`.
  Use §3.2.2 for constrain/cache/insertion order; §5.1.2 for delayed hypotheses
  and the explicit `μ α . α` case; §5.2 for the bounds execution notation; and
  §5.3.1 Lemma 2 for the exact successful-constraining soundness claim.
- Authoritative Yulang inference principles:
  `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, SHA-256
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Original roots: `notes/theory/lean/YulangClosure/Contracts.lean`, SHA-256
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
- Structural syntax: `SimpleSubConstraintSyntax.lean`, SHA-256
  `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`.
- Existing operations: `SimpleSubConstraintSoundness.lean`, SHA-256
  `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293`.
- Current abstract core: `AbstractSimpleSubCore.lean`, SHA-256
  `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c`.
- R223 checked prerequisite: `AbstractBoundCycleNormalizationR223.lean`, SHA-256
  `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee`.
- R223 independent review: SHA-256
  `13050f6b4babe6cb16741a5fa263ff1ea8240e560dd20ee935f21086c7c1e311`.
- R223 falsifier: SHA-256
  `e7a5d0e5ae8340020e9f7664e108fe1a74416a4da62307db2ac5595523fb7eed`.
- Context for actual source transitions: `SimpleSubLatticeCertificates.lean`,
  SHA-256 `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b`.

Rehash direct inputs before writing/building. Any change returns to Luna.
Do not define typing as satisfaction or infer accepted execution from a partial
CoreState record. Do not introduce assumed `LocalLaws`, arbitrary transition
constructors that make the theorem tautological, new axioms, or narrowed source
semantics. If the approved Yulang extensions do not fix a needed transition or
hypothesis-unlocking rule, freeze the exact first missing equation and its
governing owner as an honest blocked result.

## Lanes and exact leases

1. **Constraining proof — registered `lean_prover`, ≤ 4,200 seconds.** Own only:
   - `notes/theory/lean/YulangClosure/AbstractConstrainSoundnessR224.lean`
   - `tasks/agent-loop/inbox/abstract-constrain-soundness-r224-proof.md`

   Work through the exact paper relation, state/cache invariant, insertion and
   recursive cases, consistency preservation and coalesced inequality. Freeze
   a checked theorem or the first exact authority/equation blocker. Include
   theorem types, all axioms and the direct effect of the result on the parent.

2. **Rust-owner bridge investigation — registered `researcher`, read-only,
   ≤ 1,200 seconds.** Inspect `crates/yu-solver/src/candidate_scheme.rs` and
   `candidate_receiver.rs` against the approved abstract constraining,
   extrusion/intrusion and publication operations. Own only:
   - `tasks/agent-loop/inbox/abstract-constrain-r224-owner-bridge.md`

   Identify an actual correspondence or exact missing obligation. No Rust edit,
   build, Cargo, cache, or production promotion. If there is no safe code slice,
   record `NO_SAFE_CODE_SLICE` with owner-specific evidence.

3. **Independent review — fresh `compiler_referee`, ≤ 900 seconds, after the
   frozen proof and owner handoff.** Review the claim against the paper, its
   actual Lean definition and dependencies, non-vacuity, theorem applications,
   complete axiom audit, and any source correspondence asserted. The proof author
   and source investigator cannot certify their own output.

4. **Luna owns** exact dependency rechecks, the only Lean cache writes, focused
   checker and axiom audit, counterexample adjudication, current state, outcome,
   explicit-path Git staging, commit and non-forced push.

## Resource envelope and cache policy

The user explicitly authorized Lean cache generation. Use only the existing
pinned project `notes/theory/lean` and its existing `.lake/build`. Do not add a
worktree, environment, project copy, cache, target directory or scratch output.
Lean is pinned at 4.35.0. Only Luna may build, after the proof module freezes;
use one CPU, one process, the project's `-M1024`, and a 1 GiB process limit.
Build only `+YulangClosure.AbstractConstrainSoundnessR224:olean` and run the
focused bundled checker. No full/default build, Rust, Cargo or tests.

Aggregate `.lake` apparent growth cap: 64 MiB from the recorded R223 baseline
of 131,264,002 bytes. Stop before writing if any target/dependency output below
exists at intake, any unrelated output is required, or the cap would be
exceeded. No cache cleanup.

Permitted new cache paths:

```text
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractConstrainSoundnessR224.olean
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractConstrainSoundnessR224.olean.hash
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractConstrainSoundnessR224.ilean
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractConstrainSoundnessR224.ilean.hash
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractConstrainSoundnessR224.trace
notes/theory/lean/.lake/build/ir/YulangClosure/AbstractConstrainSoundnessR224.c
notes/theory/lean/.lake/build/ir/YulangClosure/AbstractConstrainSoundnessR224.c.hash
notes/theory/lean/.lake/build/ir/YulangClosure/AbstractConstrainSoundnessR224.setup.json
```

Budget: 7,200 seconds total (proof ≤4,200; source investigation ≤1,200; review
≤900), zero Astra. One verification owner, at most one heavy process, one CPU,
1 GiB process RAM. No budget reset or nested CLI.

## Success, stop and parent metrics

Proof success requires a constructive endogenous successful-run relation, the
cache-sensitive consistency invariant, and the exact successful constraining
inequality, checked in Lean with complete axiom audits and independent review.
It must include the two kinds and four Function ports and state how extrusion,
intrusion and publication are handled. If those operations are outside the
proved transition relation, the result stays a partial constraining lemma and
must identify its next integration premise.

The independent source lane is useful only if it establishes a concrete
correspondence or a sharper owner-local dependency; counts of inspected Rust
paths do not count as progress. No source or production gate closes from a
local theorem alone.

Report the original roots/packages as **0/4 and 0/5** unless an unchanged root
is actually discharged. Stop at the first missing approved transition,
equation, cache invariant, or authority owner. Consult the dispatcher at a
material authority/dependency change, a decisive counterexample, or closeout.
