# Cycle 103: named ordinary constraints enter mixed closure

Status: Draft implementation contract, 2026-11-10.

## Partial target

Compute both the extra source-name allocation and the original ordinary State
from a finite list of named scalar/variable subtype constraints. Connect the
existing structural associated program and actual mixed closure to an independent
source-name constraint interpretation and inductive derived facts.

Input: existing structural Program p and a finite list of pairs of terms
(base b or already scope-resolved source name a). Extra names are extracted from
both endpoints and deduplicated before allocation. Every named constraint is lowered to every matching pair of
allocated endpoints. The result therefore contains one-way bounds, reciprocal
edges and scalar seed pairs without a caller-supplied slot map or State proof.
Repeated names share type values; effect components are not identified.

Independent judgment: initial scalar facts require both named subtype bounds;
transfer requires both named variable edges; associated steps use the original
structural occurrence and existing declaration relation. Ordinary models require
each original named inequality under one Nat-to-Common.Ty valuation.

Target: for every p, input, well-formed env and associated registry, the computed
state after mixed closure is solver-consistent iff there exists one source type
valuation satisfying the original named inequalities and all derived facts.
Also prove exact generated scalar evidence and exact per-valuation output models.
No consistency, successful solve, fuel, slot map, extra-name list or State is
supplied as an assumption.

## Boundaries and authority

Spec 6.3 makes associated output names ordinary variables and permits constraints
before receiver selection. Existing scalar ordinary atoms supply interpretation;
this adapter does not infer constraints from full expressions or parser ASTs.
Scope identity and structural Program remain input. General Form lowering,
dynamic children, final four-way classification, K2 and dictionaries remain open.
B4 still has all five bridge packages open. This is a bridge-1 partial target.
The existing audit x-oracle X13–X16 and C3-PARENT are supporting source examples,
not validation of this allocation algorithm. No new Yulang2 run is claimed.

## Review boundaries

The independent Derives judgment is direct paired scalar evidence plus reciprocal
original edges and associated steps, not general ordinary entailment. For example
int <= a, a <= c, c <= int forces both variables to int in all ordinary models,
but has no direct seed pair, so associated resolution need not run. Ordinary
consistency is not successful resolution of all occurrences: unsupported or
unseeded requests may produce no equation. The implementation enumerates endpoint
pairs and offers no performance bound beyond the existing finite closure.

A read-only independent reviewer found no blocking mathematical mismatch and
recommended making these inherited limits explicit. No new semantics was chosen.

## Executable boundary and representation repair

The first implementation allocated one extra slot per name occurrence. Its
22-slot positive chain evidence passed, but an ordinary consistency check timed
out at 180 seconds. Extra-name deduplication removes redundant slots while keeping
all original inequalities and the same independently proved source meaning.
The example now has 11 slots. This is a representation repair, not a weakened
expected result or a language rule. Same-name structural slots remain distinct
and continue to share type values only. Large-input complexity is still unbounded
by this report; this is not a scalability proof.
