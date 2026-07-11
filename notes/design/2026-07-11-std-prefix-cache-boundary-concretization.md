# Std-prefix cache boundary concretization

Date: 2026-07-11

Decision: Claude Sonnet 5 (2026-07-11 session). Investigation: Codex (gpt-5.6-sol).

User-approved in the 2026-07-11 session.

## Background

Commit `5d94a670` ("Normalize role fallback floor view") fixed a bug where the
generalization fallback used a different floor normalization from the solve
view. On the HTML reproduction, that reduced a warm run from 15.97 seconds to
9.93 seconds. The cold run remained 1.23 seconds, so the warm/cold inversion
improved from 12.1x to 8.1x but was not resolved.

`--runtime-phase-timings` localized the remaining cost: generalizing `proof`
spent 4.25 seconds in `resolve roles` alone. This is not artifact I/O overhead.
It is role work created by the semantic shape of the std-prefix cache boundary.

## Mechanism analysis

### 1. The artifact contains finalized poly structure, not live inference state

The std-prefix artifact is produced by running std as an independent, complete
inference unit. Body lowering, SCC quantification, role solving, and
`finalize_poly_role_impls` have already completed before the artifact is
written. The final role impl copy is visible in
`crates/infer/src/analysis/session/instantiate.rs:122-139`; compiled-unit
construction and its serialized surfaces are visible in
`crates/yulang/src/cache.rs:451-483`.

The artifact stores syntax, namespace, lowering, typed, runtime, external
runtime, and errors. Its typed/runtime representations are final poly-facing
surfaces (`crates/infer/src/compiled_typed.rs:19-52` and
`crates/infer/src/compiled_runtime.rs:14-34`). It does not serialize the live
`ConstraintMachine` bounds, alias edges, type birth levels, open SCC graph, or
the inference-time co-occurrence relationships among schemes, impl members,
and candidates.

Consequently, std does not store a suffix-specific concrete impl selection.
Predicates such as `YumarkRender` remain generic inside std. The concrete
document/children chain is newly constructed by the suffix role solver during
the warm compilation.

On import, `AnalysisSession::new` creates fresh infer, role, scheme, and SCC
state, then seeds only finalized poly surfaces
(`crates/infer/src/analysis/session/lifecycle.rs:3-45`). Existing schemes are
marked quantified, and finalized role candidates are freshened into the new
session (`lifecycle.rs:46-83`). This is an import of final structure, not a
continuation of the prefix inference run.

### 2. Cross-boundary uses change from `OpenUse` to `InstantiateUse`

In a cold whole-program run, a reference to an unquantified std definition is
an SCC edge. When it is open, the use variable is directly constrained against
the target root. The event contract distinguishes this `OpenUse` from
`InstantiateUse` in `crates/infer/src/scc.rs:345-380`, and the direct constraint
is installed by `constrain_open_use` in
`crates/infer/src/analysis/session/instantiate.rs:4-8`.

In a warm run, imported std definitions are already marked quantified
(`crates/infer/src/analysis/session/lifecycle.rs:41-59`). A use of such a target
immediately emits `InstantiateUse` instead of joining the open graph
(`crates/infer/src/scc.rs:146-178`). Instantiation freshens the serialized
quantifiers, clones explicit recursive bounds, the predicate, and role
predicates (`crates/infer/src/instantiate.rs:99-121` and `:469-483`), then adds
those cloned predicates to the new suffix session
(`crates/infer/src/analysis/session/instantiate.rs:183-253`). It cannot restore
the original constraint graph because that graph was never serialized.

This `OpenUse` versus `InstantiateUse` transition is the first semantic
divergence between cold and warm compilation.

### 3. The detached view enables concrete recursive role solving

Generalization repeatedly compacts the root, performs co-occurrence,
interval, and floor simplification, searches role candidates, injects
equalities from resolved candidates into the `ConstraintMachine`, recursively
handles prerequisites as solved or residual constraints, and compacts again.
The main loop and its `resolve roles` timing are in
`crates/infer/src/analysis/session/generalize.rs:42-235`.

The role solver attempts candidate matching only when every input yields a
single concrete type (`crates/infer/src/role_solve/mod.rs:538-575`). After a
candidate matches, its prerequisites are recursively rewritten and resolved;
only a unique candidate is accepted, while non-unique prerequisites remain
residual (`role_solve/mod.rs:409-467`).

In the warm detached/finalized view, the document input appears as a concrete
boundary, so the following recursive search fires:

```text
doc_leaf<children>
  -> prerequisite: YumarkRender<children>
  -> cons_cell<head, tail>
  -> prerequisites: YumarkRender<head>, YumarkRender<tail>
  -> ...
```

This concrete expansion is the direct source of the extra 4.25 seconds.

### 4. Cold compilation keeps the predicate abstract

In the cold graph, document type arguments retain open-use-derived bounds such
as `Bounds(Union(Var, Concrete), Var)`. That is not a single closed concrete
type, so it does not satisfy the candidate recursion trigger. The predicate
therefore remains an abstract residual instead of expanding into the concrete
document/children chain.

This difference is not caused by std recording a bad concrete choice. It is
caused by finalizing and detaching std before the suffix exists, then importing
only the finalized interface into a fresh graph.

### 5. Cache route code location

The CLI selects the std prefix as one coarse source-unit closure and either
reads or builds its compiled-unit artifact in
`crates/yulang/src/main.rs:2034-2057`. It then removes the prefix files and
compiles the suffix against that artifact in `main.rs:2162-2197`. The prefix
lowering entrypoint constructs a new session from the compiled poly surface
and lowers only the suffix (`crates/infer/src/lowering/body/mod.rs:632-723`).

## Relationship to cold/warm scheme non-equivalence

This is the same root cause as the previously established cold/warm scheme
non-equivalence. The cache boundary should preserve the invariant:

```text
cold whole-program generalization
  ≡ prefix finalize -> serialize/import -> suffix instantiate/generalize
```

The right-hand side currently discards the prefix live constraint topology.
That changes not only representation but also whether role resolution's
concrete-input trigger fires.

The cache equivalence canary in `crates/yulang/tests/cli.rs` establishes runtime
result equivalence for its fixture. It does not prove logical scheme
equivalence, principality, or equivalence under future additions to the impl
set. Those properties remain unproven.

## Design options

### Option 1: canonical cache interface

Introduce a cache-export self-containment invariant in generalization and
finalization. Every variable in a scheme must be closed either as a quantified
variable or through explicit recursive/boundary bounds. Role predicates and
impl prerequisites must be frozen in a principal form. Reflect that invariant
in `CompiledTypedSurface`, `CompiledRuntimeSurface`, and the artifact schema,
and use alpha-equivalence after import and instantiation as a test oracle.

- Soundness: best of the three options. Unconditional quantification of free
  variables is not sound; explicit boundary bounds are required.
- Performance: if the warm predicate returns to the cold abstract form, the
  4.25-second candidate recursion should disappear.
- Fit with the no-heavy-fixpoint policy: compatible if canonicalization is one
  compact transformation rather than a new iterative solver.
- Scope: large. It affects generalization, finalization, role candidates,
  compiled surfaces, cache format, and golden/equivalence tests.
- Main risk: a post-processing pass that merely deletes apparently unused role
  predicates would repeat the earlier pollution-style fixes rather than
  establish the required interface invariant.

### Option 2: cache an inference-boundary constraint surface

Serialize the prefix free-variable bounds, levels, alias/co-occurrence edges,
role prerequisites, and shared-variable mapping among schemes and candidates.
Batch-seed that summary into the fresh suffix session.

- Soundness: potentially the closest to cold compilation.
- Performance and cache value: the reachable closure can become large enough
  to erase the benefit of the cache.
- Proof burden: completeness of the summary is difficult to establish.
- Scope: largest. It reaches `ConstraintMachine` serialization, `TypeLevel`,
  SCC state, imports, role tables, and artifact schema.
- Main risk: reintroducing boundary variables, extra rigid variables, or
  shadow/protection mechanisms that the current inference core deliberately
  excludes.

### Option 3: conservatively fall back to cold compilation

Before using a cached prefix, structurally reject that warm route for the
current compilation unit if its used interface is not demonstrably
self-contained. The structural hazards are:

1. a non-quantified free variable remains without explicit bounds;
2. a role candidate prerequisite depends on a live-graph relationship;
3. a role-polymorphic interface does not close under import round-trip.

If any used interface has such a hazard, compile that entire unit through the
existing cold path. Do not add a third inference path.

- Soundness: most conservative; it delegates to the already trusted cold path.
- Performance: for the HTML reproduction, the entire cold run (1.23 seconds)
  is already faster than warm role solving alone (4.25 seconds).
- Fit with the no-heavy-fixpoint policy: compatible when implemented as one
  structural scan plus the existing dependency closure.
- Scope: medium at coarse std-prefix granularity.
- Main risks: the scan must not hard-code role names, std paths, or module
  names, and must not reject every interface merely because it contains a role
  predicate. Eligibility is per program so safe programs retain the warm
  path.

## Decision

1. Implement Option 3 now as the short-term mitigation.
2. Use coarse granularity: the std prefix is the fallback unit. If one used
   interface is unsafe, the whole program skips the warm std-prefix route and
   uses the existing cold compilation path. Per-module fallback is out of
   scope.
3. Keep Option 1, the canonical cache interface, as the future complete
   solution. It is explicitly out of scope for this slice.
4. Remove Option 2 from near-term consideration.

This decision was made by Claude Sonnet 5 in the 2026-07-11 session with the
user. The mechanism investigation and presentation of options were performed
by Codex (gpt-5.6-sol).

## Remaining work and risks

- Logical cold/warm scheme equivalence and principality remain unproven.
- Option 1 still needs an explicit boundary-bounds representation and an
  alpha-equivalence test oracle before implementation.
- Option 3 needs a structural, per-program eligibility scan. It must preserve
  the warm route for safe role-using programs such as the existing cache
  equivalence canary.
- Coarse fallback can give up useful prefix work when only one used interface
  is unsafe. Per-module fallback may be considered later, but is not part of
  this decision.
- Cache format changes must remain coordinated with any future canonical
  interface work.

Decision: Claude Sonnet 5 (2026-07-11 session). Investigation: Codex (gpt-5.6-sol).
