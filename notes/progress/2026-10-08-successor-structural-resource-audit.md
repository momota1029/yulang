# Successor structural resource audit

Date: 2026-10-08
Baseline: `c5e9f8b24668c971788ac4d222ad3a81ee497697`
Claim class: read-only structural characterization; no performance verdict,
semantic authority, or representation choice.

## Scope

This audit maps the current F5 inference pipeline's visible work units to the
resource obligations a successor implementation would need to account for.
It does not establish an end-to-end complexity bound: source-driven relation,
evidence, Generalize, and output sizes are not yet characterized. No production
code, limits, semantic behavior, or canonical obligation-DAG status changed.

The inspected path includes SCC planning in `crates/yu-solver/src/scc.rs`,
component execution and publication in `crates/yu-solver/src/lib.rs`, polarized
row expansion and memoization in `crates/yu-solver/src/f5c_generalization.rs`,
reentry/fixed-point handling there, closed-use routing and root observation in
`lib.rs`.

## Current work dimensions

- SCC planning has definition, use/arc, component, and identity-payload
  dimensions. Sorting contributes `O(U log U + Σ M_c log M_c)` for use/arc
  volume `U` and component member counts `M_c`; the complete planner cannot be
  described as linear in graph size without accounting for that work.
- Per-component execution copies component/member/use handles, routes internal
  uses, generalizes members, finalizes and installs all members, then routes
  incoming uses. The all-member publication barrier is visible in the current
  lifecycle.
- F5c polarized row expansion and memoization depend on row and edge
  incidences, active path/reentry, recursive-bound expansion, and the amount of
  cacheable versus uncacheable work. Root expansion bypasses some non-root memo
  reuse; a cache hit count alone does not show saved work.
- Reentry ownership, per-member scans, and fixed-point processing require
  tracking rounds `R`, candidate counts, and replayed bound volume `B_r`, as
  well as allocation/copy and repeated reachability costs. A finite graph by
  itself does not establish a linear or quadratic total-work bound.
- Normalization and materialization allocate predicate/bound representations
  and temporary union/intersection vectors. Recursive depth and output size
  matter in addition to shared graph-node count.
- Each incoming use builds fresh quantified/recursive rows and a substitution
  map, traverses bounds and predicates, and propagates constraints. Aggregate
  work therefore depends on binder count plus visited incidences per use.
- Root observation scans projection state; `root_value_for` returns `Unknown`
  for Function and is not evidence of a complete Function export.
- A candidate packing bound of `O(N + E + P)` is conditional on already
  supplied source judgments and indexes; `P` includes identity, binder,
  primitive, and evidence payload bytes. It does not bound deriving or
  validating those judgments.

## Successor envelope to measure or prove

The relevant inventory includes graph nodes and ordered edges; cycles; members
and export events; selected views and capture overlaps; binder ancestry,
dependencies, eligible and fixed identities; descriptor and admission data;
evidence/certificate DAGs; internal and incoming uses and their identities;
SCC size/depth, active path and staging; query count, work, observations and
serialized bytes; retained, overlay and materialized bytes; rollback journal
and coexistence peak; and invalidation/dependency volume.

Independent of the pending Generalize export-root decision, any successor must
account for original incidence, scope, fixed-capture sharing, fresh-use
isolation, internal sharing, publication visibility, output size, and failure
behavior. The actual export graph/root, legal transformations, proof/query
workload, export duplication, and per-use materialization depend on that
decision.

## Unresolved resource risks and evidence needed

No source-scale-to-relation/evidence/Generalize/view/output model is available.
Repeated-use materialization, failure/lifetime/coexistence behavior, and
transactional publication remain uncharacterized. Existing F5 memo,
uncacheable replay, index, and fixed-point costs need separate counters or
structural bounds.

Before a successor resource gate can close, obtain a source-to-artifact census
for nodes, edges, binders, evidence, views, uses, and output; prove termination
and a work bound for the approved envelope; count fixed-point rounds, replay,
and materialization separately from memo hits; and cover shared captures,
large SCCs, repeated fresh uses, deep nesting, output expansion, and failure.

No benchmark samples, benchmark processes, RSS/allocation tracing, or failure
experiments were run. Static inspection did not resolve a timing-dependent
decision, so no timing experiment was justified. There is no performance
verdict and no representation selected by this audit.

## Next action

Continue source/contract work on the required type-inference and F5 replacement
gates. Keep the Generalize export-root-dependent work behind the pending user
decision recorded in `questions/2026-10-08-successor-generalize-root-policy/`;
continue independent work on source-scale census and publication/failure
invariants. Revisit resource bounds when those source and export artifacts are
concrete enough to count.
