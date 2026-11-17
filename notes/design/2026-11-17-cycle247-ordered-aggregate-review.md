# Cycle247: ordered actual blocks and aggregate scope

## Algorithm and invariant

`GeneralPresenceOrderedBlock247.solve` evaluates the head RHS in the current
assignment, writes only that target's type value, and solves the tail. SafeOrder
requires: no typed self-read in the head, no later entry with the same target,
no later target in the head RHS's typed reads, and the same property recursively
for the tail. Thus later RHSs may depend on earlier targets, but not conversely.
The order is provider-before-consumer. Every row coordinate is retained, so a
private name in an arrow row does not count as a forbidden type dependency.

The conditions suffice: the head RHS value is unchanged by every write, its
stored target value survives all tail writes, and the induction hypothesis
satisfies the tail under the updated assignment. Subtyping reflexivity alone
then turns the resulting value equalities into the two actual tyLe atoms per
entry. No monotonicity, antisymmetry, constructor congruence or assumed model
existence is needed. The implementation has been checked with strict Lean.

This order condition is sufficient, not necessary. Cyclic guarded blocks from
246/247 can have regular models while failing SafeOrder; duplicate equivalent
entries can also be harmless but fail its distinct-target condition. Failure
must not become source-language rejection. No sorting or duplicate-removal
algorithm, or permutation-invariance theorem for such preprocessing, is
included in this result.

## Exact connection to existing merge syntax

`GeneralNominalAllocation.lean` defines lower at lines148–152 by bottom for an
empty interval list, a lower-endpoint var for a singleton, and union of a lower
endpoint var with the remaining lower term. Upper at lines154–158 similarly
uses top, upper-endpoint var, and inter. These are actual Presence TyTerm Nat
terms with unguarded references, so they fit OrderedBlock directly, unlike
GuardedLayer246's payload-guarded reference positions.

`GeneralNominalRebaseDefinitions241.entries` builds stable lo/hi target pairs
with those real lower/upper RHSs when an input name has other than one occurrence.
Its existing `supported` theorem places RHS sources in a supplied endpoint pool;
`entries_fresh` excludes targets from a protected pool. If those supplied pool
conditions hold and the resulting target list has no duplicates, SafeOrder
holds in any list order. For dependencies on earlier installed definitions,
SafeOrder instead requires an actual topological order. The ordering provider
and target uniqueness still have to be built and checked; this note does not
infer them from declaration/input-name notation.

In particular, a rebase may reuse private targets already present in endpoint
support. The initial-install freshness argument then does not automatically
apply. The actual journal, source cache, alias/control metadata and cross-owner
support relationships are not represented by the ordered list alone. This new
lemma constructs models for a meaningful unguarded acyclic fragment; it does
not establish the I47 successor SourceBoundary, arbitrary cyclic aggregate
solvability, or termination of repeated refreshes.
