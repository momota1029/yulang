# Cycle159 capture multiplicity: semantic, not source-ID equality

Target: V5 evidenceNode, allocation sub-obligation after semantic reinspection.
The existing capture allocator uses literal bounds for one occurrence and fresh
merge bounds for multiple occurrences. We do not alter it. For arbitrary states,
registries, declarations, model and nonempty occurrence lists with the same
membership (multiplicity and ordering may differ), prove equality of the sets of
actual values fitting the computed capture, under each side's actual merge atoms.
Specialize to duplicate-to-singleton collapse; prove the source pair can change.
This is not a universal reobserve theorem: actual reobserve may also narrow the
bounds. Inspection provenance and current merge installation remain separate.

Companion workers develop semantic inspection transport and a nonvacuous nested
projection example. No new semantics, Step or classifier definition is introduced.

## Exact implemented bridge
`SemanticSchemaTransport.Footprint` replaces literal capture endpoint IDs by
semantic endpoint equivalence. Its origin coverage and schema membership remain
explicit; it is not a complete current-request existence theorem.
`SemanticCollapseAllocation` derives semantic equality of point-valued leaf
endpoints from actual old ProjectionModels, then transports the actual allocation
from two occurrences to one. Only old propagation and current base Models are
needed for new propagation. `SemanticCollapseSchema` composes this with schema
replay for a fixed schema whose input variables are the retained binder. Output
variables are unrestricted. This is suitable for unchanged root output requests;
newly emitted child targets are NOT identified by this theorem.

## Terminal full-branch closure
`GeneralDictionarySemanticCollapseBranch.branch` derives the current full
`BranchModels` from the historical branch and current raw source model. It
requires a terminal declaration, exactly one input binder, point leaf intervals,
and a generated root schema whose nonoutput variables use that binder. The
old outer descriptor interval may be nonpoint. It does not assume current
private merges or current materialization. The theorem itself takes a `Shape`
over a `Revision`, not a `Certified` or operational `Step`; the separate concrete
fixture supplies a certified improving reachable revision. Prepared/selection,
installation, emitted children, and general reobserve preservation remain open.
