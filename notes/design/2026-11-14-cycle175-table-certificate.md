# Cycle175: shared height table certificate

Status: verified scoped implementation equivalence; not a new language rule.

## Objective and invariant

Replace exponential repeated unfolding of the height tree with a bottom-up
finite table. `heightTable registry fuel` stores `(role,height)` pairs for every
entry in `roleNodes registry`. Duplicate names have the same stored value.
`lookup` returns the first pair or zero. Every child of every real declared
role is in `roleNodes`, so the induction invariant is exact equality with
`computedHeight registry fuel role` for every listed role. No DAG hypothesis
is needed for this invariant or for `checkTable_eq`, including fuel zero.

The existing all-edge check uses a single shared table. `certifyTable` chooses
exactly the existing uniform fuel. `certifyTable_eq` is an equality of Bool
values for every finite Registry, not merely soundness in one direction.
Consequently it preserves complete recognition of the role-DAG fragment,
source/where reorder invariance, the positive wrap regression and the negative
same-role recursion regression. A false certificate remains fragment failure,
not source-language rejection. General Paterson recursion is outside this
certificate exactly as before.

## Static work and scope

Let N be the roleNodes length (with duplicates), D declarations, E total
requirements and F fuel. There are F rounds; each round visits N entries,
scans declarations to obtain child lists, and uses a linear table lookup for
each edge. It does not recursively branch into subtrees when an incoming
edge duplicates another edge. This is polynomial table work, with list lookup
and repeated child-list construction remaining obvious optimization limits.
No constant-time lookup or global compiler performance claim is made.

## Verification

Lean 4.35.0, `-j1 --trust=0`. Exact new source compiled successfully and an
independent imported small audit checked 10 named theorems. Only propext,
Classical.choice, Quot.sound occur. The private fold lemma is also included
in the transitive dependencies. Existing 174 cache is reused, not rebuilt;
no full repository build/CI was run. Root/audit imports are for parent to add.
Initial imported audit and benchmark failed because Lean chose the first
`Yulang` directory rather than merging two LEAN_PATH directories. Creating an
isolated symlink dependency library fixed this; no existing library changed.

## Bounded performance check

Decision: determine whether table sharing materially improves duplicated-edge
height search and makes the former size20 smoke case terminate within a
60-second cap. This is a synthetic registry and is NOT asserted Checked.

`BenchTable175.lean` performs one warmup and three paired samples at length12
with two duplicate edges per declaration, in the same Lean process. Timings
include the printed result, using monotonic nanoseconds. It then runs only the
candidate at length20; this is a scoped termination/performance smoke test,
not a paired speedup estimate for size20. No baseline20 timeout is rerun.

Three paired measured samples (milliseconds):
- baseline: 145.359, 146.631, 163.893; median146.631, range145.359–163.893.
- table: 9.498, 10.920, 9.336; median9.498, range9.336–10.920.
- Candidate-only size20:43.744ms, accepted=true.

All paired results are true and source equivalence is proved independently.
The observed median reduction is approximately15.4x for this one synthetic
size/configuration; not a general speedup factor. Two benchmark invocations
(one initial import failure, one successful run), under one minute total,
below the repository 8-process/10-minute ordinary budget.
