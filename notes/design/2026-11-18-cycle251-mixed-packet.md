# Cycle251: mixed-time packet compiler

Status: Draft representation, following I47(a), retaining I45.

Objective: compile every field of a supplied actual Plan into finite materialized
syntax with two explicitly different reads. Historical raw context, projection
origins, input demand and cross/self-check constraints read the old snapshot.
Capture bounds, binders, emitted equations and child demands read a current
interpretation. Within a head schema, origins/tests read old while variable
requirements and actual binders read current. Do not use the legacy merge
constraints: the persistent stable definition block separately supplies the new
aggregate equations.

First define an independent declarative MixedHolds(plan, old, current) from the
existing source judgments, without mentioning the new compiler. Then for all
Plan, two CompTerm mappings and one physical assignment prove compiled.Holds iff
MixedHolds at their readbacks. This is representation correctness, not yet a
source acceptance or Step theorem. Origin existential witnesses stay tied to the
old read, while binder targets are values of the current read.

The later concrete adapter must construct current mapping from actual captures
and the chosen stable handle. A caller-supplied arbitrary map is not that adapter.
Prove coverage, key consistency and separation from current output/binder names;
non-singleton legacy capture identifiers need translation to stable lo/hi terms,
while singleton endpoints already read the old snapshot. Native child/output
identities and default positional input centers need separate accounting.

Stop at the exact verified boundary rather than claim a new source scheduler.
Changing live request generation, source eligibility→Permitted, owner/term bounds,
Acc and language regressions remain separate. No semantic decision is made by
introducing this compiler relation. I47(a) was selected in prior design; I47(b)
semantic canonical keys still lacks a finite source quotient construction.
