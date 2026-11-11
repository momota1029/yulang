# Cycle106: source evidence and recursive diagnostic forests

Status: Draft. Date: 2026-11-11. Scope: existing finite rigid Roles core and checked mixed source.

## Target and specification

Replace the loss of failure detail at the cycle105 Boolean observation with a
computed diagnostic forest. A source obligation retains every scalar evidence
attempt. Encodable attempts retain the complete uniquely selected dependency
tree, including missing/overlapping child nodes. Unsupported encoding and absent
receiver evidence remain explicit. No failure is promoted to a new language
classification. Spec6.2/6.3 supplies caller-visible heads, overlap before where,
Paterson decrease and delayed finalization. This is a diagnostic snapshot after
the existing finite closure, not general source saturation.

## Data, independent judgment, execution and theorem types

1. A rigid Tree stores its original goal, all matching declaration identities,
   and, only for a unique head, one child tree per instantiated where condition.
   Leaves distinguish zero heads and multiple heads. The executable overlap list preserves Roles.candidates order, which removes
   repeated equal Impl values; distinct declaration keys stay distinct. The
   independent Represents judgment specifies overlap membership and Nodup only,
   not overlap-list order. Sibling order/multiplicity are retained literally.
2. Represents impls goal tree is inductive. Its local premises use independent
   Matches and uniqueness; child goals are list-wise equal, with exact length/order; each child is represented.
   It does not call a tree builder or the resolver.
3. diagnose impls wf goal recurses on argsSize goal.args. Paterson derives every
   recursive decrease; no caller fuel, trace, successful resolution or finite
   work table is accepted. All child goals are generated from actual declarations.
4. For every impls, wf : WellFormed impls, and rigid goal g, diagnose_represents
   proves the independent recursive judgment. status agreement proves its
   compatibility projection equals Roles.resolve impls wf g, without deleting
   the tree. Success iff is independent Derives and absence of ReachesOverlap.
5. For every arbitrary child address path and target, diagnose_follow_exact
   relates lookup to the independent declaration-index Path, with equality of
   the entire reached subtree. run_path_exact lifts this to arbitrary source
   clauses and computed scalar evidence through the actual mixed closure.
6. For arbitrary checked mixed src, env, roles, wf and awf, run returns one row
   for every source clause, and every computed scalar attempt carries a complete
   rigid diagnostic. Its Boolean projection equals cycle105 run, and success iff
   ValidSource / Models / AllDischarged has no caller heads, State, fuel or success.

## Boundaries and what remains

The rigid core's compatibility status prioritizes ambiguity over missing; it is
not chosen as the final source language classification. Parent with missing child
stays a parent tree containing that child. General Form, new source allocation
from dynamic where, parser/declaration lowering, and source dictionary observation
remain outside this statement. Structural templates still accept only scoped
placeholder zero and int/str payload encoding. Ground templates still need the
explicit receiver evidence required by cycle105. Existing questions about source
identity remain open. All five global B4 bridge packages remain unfinished.
