# HIR ConstraintBatch first slice

Status: Authoritative; construction complete (2026-09-20)

Approved by: user, 2026-09-20.

The user approved the refinements below.

## Scope and ownership

This record resolves the first-slice questions in
`2026-09-18-hir-type-attachment-open-questions.md`. `yu-hir` owns immutable
HIR and dense opaque `HirExprId`; `yu-types` owns `CanonicalType::Int`; new
`yu-solver` owns immutable collection. `yu-hir` and `yu-types` remain
independent upstream siblings; only `yu-solver -> {yu-hir, yu-types}` is added.
This narrowly supersedes the contested HIR/types edge for this gate; graph
checking rejects either sibling edge and allows the solver fan-in.

`HirExprId` is deterministic only within its exact immutable `HirModule`
artifact. It has no range, cross-revision, serialization, or cache identity.
Every `ResolvedExpr` variant receives one ID in HIR source/preorder order.
`HirItem::Error` has no ID; assignment occurs in the existing construction pass
with checked exhaustion. `DefId` uses shared immutable payload so its clone is
O(1), without an interner, cache, map, or index.

## Products

`ResolvedExpr::{Integer,Name,Error}` each stores `HirExprId` and exposes
`id()`. `CanonicalType` contains only `Int`.

`yu-solver` exposes an immutable `ConstraintBatch` retaining the exact input
`Arc<HirModule>` and ordered constraints. It reads no CST/source, mutates no
HIR, creates no diagnostics, and performs no solve.

Each constraint is one normalized equality of `TypeTerm::{Expression(HirExprId),
Definition(DefId), Canonical(CanonicalType)}` with origin
`ConstraintOrigin::{Expression(HirExprId), Definition(DefId)}`.

The batch is an ordered append-only occurrence sequence, not a canonical fact
set: equal normalized terms may repeat with distinct origins. Definition/value
has Definition origin; literal/name equality has Expression origin. There is no
deduplication or sorting.

## Collection

Traverse module items once in source order. For a collectable binding value,
emit `Definition(binding) = Expression(value)` first. Emit
`Expression(integer) = Canonical(Int)` for integers and
`Expression(resolved-name) = Definition(target)` for resolved names.

Errors, unresolved/ambiguous names, `HirItem::Error`, and their owning binding
value edges emit zero constraints. Later independent valid items continue.
For `my x = 1; my y = x`, emit exactly definition/value, integer, definition/
value, resolved-name equalities in that order.

Direct-root Integer/resolved Name expressions emit their intrinsic equality;
direct-root Error/unresolved/ambiguous expressions emit none. Collection uses
only the expression variant/resolution, not module-global errors: a duplicate
definition with a valid value still collects. An omitted binding value emits
neither its definition/value nor intrinsic edge. The batch moves its input Arc
and grows one Vec amortized during the sole traversal; no pre-count or reserve
pass is used.

## Deferrals

No solve, type variables, `Unknown`, arena/interning, generalization, schemes,
effects, composites, annotations, operators, applications, imports,
diagnostics, serialization, or incremental reuse enters this gate.

## Construction and verification

The HIR assigns dense IDs during construction; `yu-types` exposes canonical
`Int`; `yu-solver` collects the approved immutable ordered batch. Focused HIR,
types, solver, and graph tests plus workspace check pass with zero benchmarks.
