# Cycle65: finite source owners for actual where expansion

Status: Draft. Scope: B4 source boundary and generated work, not final resolution.

## Partial goal and source evidence

For every positive return of the actual finite interval candidate wrapper, compute
an ordered finite owner for every generated where endpoint occurrence and connect
it to the existing canonical graph allocator. No owner, source-equality premise,
model-existence premise, or chosen interval centre is supplied by the caller.

The parent table is the names occurring in the original lower/upper Form syntax.
The child table concatenates the actual generated endpoint names in child order,
including duplicate children and duplicate occurrences. These are ambient endpoint
names, never declaration-local binder spellings. This construction does not decide
whether different ambient names should alias via a separate source registry.

Read work/dots-audit x-oracle X13-X16 and C3-PARENT/C3-PARENT-NEG before changing
Lean. They support shared-source/where provenance, not arbitrary finite model or
closure completeness. Reuse the existing spec 6.3 and capture boundaries.

## Data, executable and independent relation

`locate table names` traverses the actual names and uses the existing executable
first-occurrence lookup. It returns finite parent slots, or fails for an absent
name. Its independent acceptance condition is name inclusion, not success itself.
Cycle64 `returned_sources` discharges this condition for the actual generated list.

For all finite tables/names, `locate` succeeds iff every name occurs in the table.
For all returned owners, mapping original source names over them recovers the exact
input list (including order and multiplicity); every owner is canonical.
For every actual candidate return, its child table therefore has computable owners.
For every child occurrence, canonical allocation equals retaining that old owner,
and arbitrary graph inspection after allocation equals the retained old snapshot.
No graph consistency, scalar knowledge, child success, or model is assumed.

## Remaining boundary

The graph is an explicit arbitrary input. Allocation preserves it, rather than
proving its semantic adequacy for the ordinary state. Compound endpoints are not
allocated as new unknown source variables. Child-local capture/source registration,
associated feedback, repeated-binder reconciliation, recursive finite work closure,
and saturation still need bridges. All five B4 main bridges remain open.
