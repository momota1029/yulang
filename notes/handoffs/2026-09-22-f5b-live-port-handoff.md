# F5b live-variable port handoff — 2026-09-22

## Resume point

Branch `yulang3` is clean and pushed through `112193a7`
(`feat(solver): transfer Term arenas with batches`). The completed F5b
lifecycle substage is recorded in `notes/progress/daily/2026-09-22.md`.

The next active work is the remaining already-Authoritative F5b live-variable,
level, and batch-recipe translation structure. This is implementation under
the accepted F5 foundation, not a request for a new language decision.

## Governing authority

- `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`:
  §§5–6, 15–16, 22–23, 27, 30, 35–36.
- `notes/design/2026-09-22-f5b-closed-finalization-term-owner-draft.md`:
  completed lifecycle ownership boundary; do not reopen it.
- `tasks/current.md` is navigation only and points here for resumption.

## Confirmed completed boundary

- `yu-types` solely owns sealed closed-type finalization, closed storage, and
  terminal accounting. `yu-solver` maps the existing availability boundary and
  never publishes a partial `SolvedModule` on finalization failure.
- `Term` is opaque. A `ConstraintBatch` owns its immutable collected lineage;
  `ConstraintStore::from_batch` and `SolvedModule::solve` retain that exact
  lineage. Batch aliases share only the prefix and use separate sparse 256-slot
  solve-time pages.
- `ConstraintStore::new(Arc<HirModule>)` is intentionally gone. Do not restore
  it, rebrand/reconstruct Terms from HIR, add public Term constructors, or add
  public F5b page counters.

The lifecycle substage closed with M2 specification and performance review.
Focused verification: 65 `yu-solver` library tests, 7 doctests, formatting,
diff check, and warning-free workspace check. F5e's full physical resource
matrix and public counter certification remain deferred.

## Yulang2 structure to preserve

The local oracle inspection established the structural reference, rather than
a fixture-specific route:

- One analysis/inference session owns append-only live variable identity,
  levels, mutable bounds, inference nodes, diagnostics, and worklists for its
  whole lifetime.
- A fresh variable is registered in dense live tables at allocation. Its level
  is mutable; origin and non-generic state belong to the same session owner.
- Subtyping admits a canonical pair, then synchronously drains one iterative
  worklist. Bound insertion first extrudes reachable younger variables and
  replays the opposite exact bounds. It never materializes transitive variable
  pairs.
- Function nodes use the fixed field order: argument, argument effect, result
  effect, result. The negative shape is its polarity dual.
- Recoverable lowering/type errors remain diagnostics; registered definitions
  still complete their SCC lifecycle. Allocation/identity failure remains
  attempt-level and yields no partial analysis result.

Useful reference paths in the local Yulang2 material are
`crates/infer/src/{arena.rs,constraints/mod.rs,constraints/machine/{entry.rs,bounds.rs}}`,
`crates/poly/src/types.rs`, `crates/infer/src/analysis/{mod.rs,session/lifecycle.rs}`,
and `crates/infer/src/{scc.rs,instantiate.rs,generalize}`. The retained
`yulang-tir5` implementation at
`/home/momota1029/rust/yulang-private-old/crates/yulang-tir5/src/solve/` is
supporting local evidence for level registration, constraint replay, extrusion,
and instantiation; it is not a literal port target.

## Required Yulang3 adaptation

Yulang3 intentionally differs from Yulang2 in two places:

1. `ConstraintBatch` is already a frozen F0–F2 collection/SCC plan, so it
   retains source endpoint recipes and translates them exactly once when
   `InferenceSession` starts. A live variable is never a component/root/HIR
   identity.
2. The static dependency-sink-first `SccPlan` remains. Do not import Yulang2's
   dynamic SCC scheduler. A `DefinitionUse` recipe must retain its frozen
   consuming use-site level for later incoming instantiation.

Implement in this dependency order:

1. Add session-owned dense live value/effect IDs, levels, origin/non-generic
   metadata, exact rows, typed endpoints, and an iterative extrusion workspace.
2. Add crate-private live/Function Term construction in the consumed branch
   arena; a single semantic variable's positive/negative endpoints share its
   live-variable ordinal.
3. Replace collection-owned F4 row identities with immutable component/root/
   occurrence endpoint recipes and frozen use-site-level data.
4. Translate those recipes once in `InferenceSession::try_new`, allocating each
   collected component/root injectively at level one. Source IDs stay recipe
   keys, not live IDs.
5. Route F4 initial/internal/incoming facts through typed live endpoints;
   remove `occurrence_exact_bounds` as a semantic authority and derive the
   existing projections from live rows once at finish.
6. Port the total value/effect/Function transition table, direct adjacency,
   exact-bound replay, checked level lowering, fixed Function decomposition
   order, and local incompatibility diagnostics.
7. Keep F4 Bottom/Int finalization through a verified live root. Q/R closure,
   full scheme generalization, and fresh instantiation remain F5c.

## Non-negotiable invariants

- Preserve F4 fact IDs/order, causes, provenance, SCC order, component-wide
  draft/install/incoming ordering, recovery continuity, availability atomicity,
  integer/Name behavior, and compatibility projections.
- Preserve one synchronous empty-on-entry/return frontier and direct variable
  adjacency only.
- Preserve Term lineage/branch isolation and the batch-bound store lifecycle.
- F5a's source Lambda continues to produce zero source Function facts until
  F5d. Private F5b algebra witnesses may exercise the total table but must not
  alter that source invariant.
- Do not add `scheme_for`, public structured projections, detailed F5 counters,
  public resource families, F5e scale certification, or a second closed arena.
- Do not derive generalization eligibility from syntax in the solver. HIR must
  freeze the boundary recipe before session translation.

## Current source map and risk focus

- `crates/yu-solver/src/lib.rs`: `ConstraintBatch` collection/recipes,
  `VariableBounds`, `DirectBoundFrontier`, `InferenceSession`, F4 routing,
  generalization, and projection finish all currently live here.
- `crates/yu-solver/src/term.rs`: completed opaque Term lineage and the private
  branch allocator. Only test code currently constructs live Terms.
- `crates/yu-types/src/lib.rs`: closed polarized Function/finalization owner;
  do not move live mutable state here.
- `crates/yu-hir/src/module.rs`: owns `EvaluationClass::FetchValue`, parameters,
  Lambda, and name resolution. The solver needs a frozen recipe/API, not HIR
  inspection during generalization.

The highest-risk migration is removing the parallel F4
`occurrence_exact_bounds` authority without changing existing projections.
Also cover both extrusion directions, Var/Var minimum-level aging, Function
field order, duplicate-pair behavior, effect-component translation, checked
overflow, incompatible-pair non-mutation, and clone/page isolation after live
Term allocation begins.

## Recommended mode and closure

Treat the live semantic migration as M3: the language decision is already
approved, but the new mutable type-inference authority is type-soundness
critical. Use one writer, then the smallest independent semantic/specification/
performance review set justified by the implemented delta. Do not use a
fixture-first route or reopen an approved design absent a concrete
contradiction.

Start with focused `yu-solver` checks. Broaden only after the coherent live
translation candidate and its repair round close. Avoid F5e's 1k/2k/4k matrix
until its approved certification stage.
