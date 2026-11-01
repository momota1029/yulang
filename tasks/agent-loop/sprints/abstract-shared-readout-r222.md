# Sprint R222 — endogenous shared regular-graph readout

Status: **ADMITTED** by Luna after R221 closeout and exact dependency/lease
review. Branch/baseline: `yulang3` / `e85005089e6867de6612170d24bbb204a95c900b`.
User goal: prove Yulang's abstract Simple-sub inference guarantees first;
preserve the original source domain and all four parent roots.

## Original parents and this sprint's outcome

The unchanged parent roots are `YulangClosure.SourceProblem.InferenceSoundness`,
`SourceScopedCoverage`, `PrincipalCoverage`, and `InferenceTermination` in
`notes/theory/lean/YulangClosure/Contracts.lean:128–154`. No quantifier,
supported source, Call/effect rule, annotation meaning, or accepted inference
behavior is changed.

R221 closed at a reviewed original-source carrier obstruction with parent delta
0. Keep that finding intact. R222 takes the next abstract-algorithm dependency
from the dispatcher and constructs one regular graph and reference assignment
from the existing `AbstractCore.CoreState` bounds and representatives. The
measurable outcome is a checked, independently reviewed compiler for the
paper's shared recursive equations that establishes graph/reference validity
and the exact structural store interpretation on its stated input domain.
This removes the endogenous shared-readout construction as a prerequisite for
building a complete abstract solver. It does **not** by itself remove a premise
of an original source parent theorem; parent delta remains 0 absent an actual
unchanged-parent application.

## Fixed mathematical authority

Use the existing Simple-sub value/effect kinds, four Function ports and
polarity rules, recursive regular-graph interpretation, immutable source-Value
births/references, and occurrence-qualified intrusion/equality authority.
Read the original top-level principles and the exact coalescing equations in
the governing paper before construction. In particular, implement the paper's
Fig. 12 shared/unifying equation. R212's `coreCoalesce` adds the positive row
key to the negative seed's seen context; R212 review left this sharing step's
source correspondence open. R222 must either preserve Fig. 12 literally or
prove that exact sharing transformation equivalent for the complete recursive
equation system before using it. It cannot silently adopt a different equation.

R212's `CoreState` is a partial storage record, not an accepted solver state.
Build the readout from its actual bound tables, levels, and representatives.
The function may reject malformed or inconsistent finite inputs, but any
success predicate/domain must be defined from the input and compiler's
constructive checks. Do not assume `Store.Satisfied`, a source judgment, a
`LawfulStore`, a successful history, a graph/reference solution, or the desired
readout theorem. Do not define acceptance by the desired conclusion. Retain
upper-only bounds, bound-only cycles, mixed Value/Effect cycles, duplicate
representatives and all structural constructors in the specified input
domain. Any exclusion must be an independently justified invariant derivable
from the actual input/transition definitions; R212 has no complete transition
relation yet.

## Lanes and exact outputs

1. **Equation construction — registered `prover`, Sol/high, ≤900 seconds.**
   Own only:
   - `notes/theory/2026-11-02-abstract-shared-readout-r222.md`
   - `tasks/agent-loop/inbox/abstract-shared-readout-r222-proof.md`

   Freeze the finite equation system, exact graph/reference encoding, source
   equation correspondence, input domain, and theorem statements before Lean
   implementation. Include upper-only, recursive Function, bound-only cycle,
   mixed-polarity, four-port and Value/Effect cases. If a premise must be
   assumed, identify its owner and why the actual abstract algorithm supplies
   it; do not promote an assumed premise to a result.

2. **Lean implementation — registered `lean_prover`, ≤1500 seconds, after
   lane 1 freezes.** Own only:
   - `notes/theory/lean/YulangClosure/AbstractSharedReadoutR222.lean`
   - `tasks/agent-loop/inbox/abstract-shared-readout-r222-lean.md`

   Prove the compiler realization, graph/reference validity, and store
   interpretation for the exact constructive success/domain relation. Print
   complete theorem types and audit every delivered declaration. No `sorry`,
   `admit`, new axiom, proof bypass, or theorem whose hypotheses already assume
   the conclusion. This lane cannot edit R212's frozen core module.

3. **Independent falsifier — registered `researcher`, ≤600 seconds, after the
   equations and Lean module freeze.** Own only:
   - `tasks/agent-loop/inbox/abstract-shared-readout-r222-falsifier.md`

   Attack equation normalization, binder allocation, guard/validity, missing
   bounds, polarities, and reference identity. Include the R212 upper-only
   counterinterpretation and the Fig. 12 positive/negative recursive Function
   discriminator. A concrete valid input that loses an obligation is a
   counterexample; an unproved admission domain is an exact blocker.

4. **Fresh review — `compiler_referee`, ≤600 seconds, after all inputs freeze.
   Own only:
   - `tasks/agent-loop/inbox/abstract-shared-readout-r222-review.md`

   Review the exact source equations, input domain, non-vacuity, theorem types,
   complete axiom audit, falsifier adjudication, and whether the result closes
   the endogenous readout dependency identified in R212. Author and falsifier
   cannot review their own contribution.

5. **Luna integration and verification.** Luna owns the contract, current state,
   R222 outcome, existing Lean cache, adjudication, explicit-path staging,
   commit, and non-forced push. Rust remains `NO_SAFE_CODE_SLICE` under R219's
   source-owner audit; no Rust or runtime writes are authorized in R222.

## Frozen dependencies

- R212 core: `notes/theory/lean/YulangClosure/AbstractSimpleSubCore.lean`,
  SHA-256 `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c`.
- R212 cache/input manifest:
  `tasks/agent-loop/sprints/abstract-simple-sub-core-r212-artifacts.json`,
  SHA-256 `b162fbde8a83096f5bd2e5e9efe076ce07e7cfa8306e27ab551e46f1d359e1f2`.
- Coalescing source:
  `notes/theory/lean/YulangClosure/SimpleSubLatticeGrowingInference.lean`,
  SHA-256 `1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0`.
- Shared graph/lattice source:
  `notes/theory/lean/YulangClosure/SimpleSubLatticeInference.lean`,
  SHA-256 `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3`.
- Regular solution source:
  `notes/theory/lean/YulangClosure/SimpleSubRegularSolutions.lean`,
  SHA-256 `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29`.
- Structural syntax:
  `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean`,
  SHA-256 `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`.
- R221 obstruction:
  `notes/theory/2026-11-02-original-literal-readout-r221.md`, SHA-256
  `1d4f46b9e9d2375d31284957c4157906df9fd00477fc976d43204262dedcb805`.
- Authoritative L1 remains pinned:
  `notes/design/2026-11-02-literal-l1-adoption.md`, SHA-256
  `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8`.

Recheck each pin before dispatch/build. Any changed dependency returns to Luna
for adjudication; do not silently refresh the baseline.

## Existing-cache authorization and resource bounds

The user explicitly authorized generation of a Lean cache. Use only the current
pinned project `notes/theory/lean` and existing
`notes/theory/lean/.lake/build`; do not create a new environment, worktree,
project copy, cache, target tree, or scratch directory. Lean remains pinned at
4.35.0. Luna is the only cache writer, after the Lean module writer freezes.
Use one CPU and a 1 GiB process cap; build only
`+YulangClosure.AbstractSharedReadoutR222:olean` and run the focused bundled
checker on the frozen theorem declarations. No default/full build, Cargo, Rust,
or tests.

The cache write whitelist consists only of these paths, all initially absent;
stop if any is present at intake or if aggregate `.lake` apparent growth exceeds
64 MiB:

```text
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractSharedReadoutR222.olean
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractSharedReadoutR222.olean.hash
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractSharedReadoutR222.ilean
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractSharedReadoutR222.ilean.hash
notes/theory/lean/.lake/build/lib/lean/YulangClosure/AbstractSharedReadoutR222.trace
notes/theory/lean/.lake/build/ir/YulangClosure/AbstractSharedReadoutR222.c
notes/theory/lean/.lake/build/ir/YulangClosure/AbstractSharedReadoutR222.c.hash
notes/theory/lean/.lake/build/ir/YulangClosure/AbstractSharedReadoutR222.setup.json
```

No cache cleanup is authorized. If Lake needs any additional output path, stop
before writing and report it for primary adjudication.

Aggregate active assignment budget: ≤3600 seconds; no Astra; one heavy Lean
process; one verification/cache writer at a time. No budget reset, nested CLI,
background task, or unreported scratch output.

## Success and stop conditions

**Success** requires a frozen equation artifact, a checked Lean compiler and
validity/store theorem over a non-circular domain, independent falsifier and
review PASS, and an evidenced reduction of the R212 endogenous-readout
dependency. Report original roots and packages as **0/4 and 0/5** unless a
checked theorem is actually applied to an unchanged root. A small fixture or
diagnostic alone does not count as success.

Stop at the exact smallest recursive equation, Fig. 12 correspondence,
guardedness, or domain premise that cannot be derived from the fixed abstract
algorithm. Freeze a counterexample only if it satisfies the admitted input
conditions. Do not assert semantic underdetermination or request a semantic
choice unless the obstacle actually requires one.

Next dispatcher consultation: a decisive counterexample/obstruction, material
dependency/authority/lease/resource change, or R222 closeout.
