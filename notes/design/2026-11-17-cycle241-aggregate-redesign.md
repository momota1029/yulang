# Cycle241 aggregate redesign

Status: Draft implementation decision within I47; not a change to language semantics.
Date: 2026-11-17. Written before any cycle241 Lean implementation.
Scope: compare rebase and semantic version keys, select a representation and make its
small independent proof obligations explicit. Neither old false Acc theorem is resumed.

## Inputs and existing obstruction

I47 (integration1c675172) accepts240 and explicitly permits design-first selection.
I44's append-only endpoint-addressed allocation creates unbounded source identities.
I45 preserves existing syntactic point descriptors but permits fresh nonpoint work.
The closed239/240 counterexamples show that these facts do not yield termination.

## A: stable owner-local rebase

An owner is (demand identity, declaration identity). Give it stable aggregate cells;
store the current definition block in a replaceable table, not an append-only conjunction
of every historical definition. Retain public source constraints separately. Keep actual
binder and child-center identity distinct from aggregate cells.

Critical correction: a fresh name is not automatically semantically private. In240 an
aggregate is promoted into base.source and read by a descriptor. Children, schema Fits,
ordinary aliases and cached packets can also read it. Moreover current journal Models
requires every historical plan.Holds. Deleting a definition in ordinary alone cannot
remove its old semantic constraint, and equality of total-assignment Models is false.

Required split:
- cross and selfChecks may constrain original endpoints; do not delete them as private.
- pure merge definitions can be replaced only with a proof of non-escape or a complete
  invalidation/reconstruction of all their consumers.
- Fits/schema/output obligations remain live source/actual constraints. A cache is not
  valid merely because its owner key stayed unchanged.

Independent declarative target: for every assignment to original source plus live actual
centers, existence of a private extension satisfying the current definition block is
exactly the retained public constraint. The extension may change private values only.
For every replacement satisfying this target, source projections are equal (or refine
when an independently justified public fact is added), and live outputs are preserved.
This is NOT equality of old and new total assignment predicates and NOT equivalence to
known-broken historical packet conjunctions. A successor boundary will need an explicit
source-projection vocabulary/transport; no old fixed-assignment StepModels theorem may
be silently reused.

### Termination skeleton

Stable cells bound names only for a fixed finite set of owners. They do not bound steps:
a finite store can oscillate. Use finite, monotone observation facts and a finite dirty
owner set. A genuine new fact strictly increases the fact set; recomputation without a
new fact removes a dirty owner and cannot re-enqueue work. Lexicographic rank:
(number of absent facts, number of dirty owners). An update caused by a new fact may
reset dirty work, but decreases the first coordinate. Equal recomputation is a no-op,
not an operational transition. Fairness is not used to prove Acc of the resulting steps.

Unproved producers, to be kept separate from the conditional scheduler theorem:
1. Finite observation/owner universe from checked finite source, constructor/declaration
   traversal and actual ground subterm descent, including recursive candidate rejection.
2. Every actual operation adds a fact or drains dirty work; no unchanged reinstall cycle.
3. Consumer invalidation/rebuild and source-projection dictionary/output preservation.
These are obligations, not assumptions disguised as the requested global Acc result.

## B: semantic quotient version keys

Names may be identified only under equivalence valid for every relevant current model,
not one chosen witness. Type equivalence and row equality must be distinguished, and
all capture consumers/actual binders must respect the quotient. A quotient relation
changing as the model set narrows also requires old-key reconciliation.

This would merge239/240's equivalent Foo endpoints while distinguishing230's real
refinement. But a finite original source does not by itself prove finitely many semantic
intervals or generated owners. Existing ground-mass lemmas bound suitable actual child
values, not arbitrary interval/version equivalence classes. A new finite-universe and
congruence theorem is necessary. Equality decision/implementation is also not supplied
by a semantic equivalence proposition. Simply quotienting one chosen model is unsound.

## Regression expectations (targets, not achieved claims)

-199: the source conflict remains rejected; no dropping public contradiction atoms.
-202: default37 remains selected with its output evidence.
-204: joined/default37 remains selected with the same output witness requirements.
-206: preserve removal of the bottom countermodel by default/output equalities;
  actual/head/effect equality constraints are retained.
-218: preserve rejection from unequal actual child values (Int/Bool) under sharing.
  Distinguish old rejected children and newly generated pending children; do not claim
  that every218 child should be selected. Nonempty-model evidence must remain meaningful.
-230: stale private aggregate definition is replaced, not conjoined with old O/W data;
  actual W witness remains valid and the dictionary must be selected, not rejected.
-239: point renaming cannot manufacture new cells; unchanged recomputation is not a step.
-240: nonpoint references do not manufacture new owners/cells; self-dependent rebase must
  be normalized or rejected as a recomputation request without adding a semantic rejection.
The old counterexamples remain valid theorems about old boundaries. New global outcomes
require new executable source paths, not renaming old proofs or asserting expected status.

## Selection and initial implementation boundary

Choose A. Stable definitions plus explicit ownership/projection expose obligations at
local, checkable boundaries; B currently combines semantic equality, quotient evolution
and finite-class completeness without a producer. A is a design choice authorized byI47,
not a claim that the complete boundary already works.

Retain I45's point-source protection for external/source descriptors. Private aggregate
cells are derived cache state, not freely retargetable public descriptors. Whether an
existing promoted cell can be reconstructed into this separation must be proved before
transport; do not remove the I45 guard on old objects or change accepted programs.

First implement only: owner-block replacement algebra; private extension/projection
preservation with explicit supports; a finite fact/dirty-work progress calculus with a
proved rank. Connect actual merge atoms in a source-stable, non-escaping fragment.
Do not label these helpers a complete operational boundary. If actual ownership/ground
closure cannot be produced, report the precise missing bridge and retain this as partial.
