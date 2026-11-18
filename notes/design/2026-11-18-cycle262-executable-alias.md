# Cycle262: executable exact alias requests

Status: Draft representation/proof design,2026-11-18. No language semantics change.

The previous cycle proved fixed-snapshot request coverage from actual source sites,
but request selection still used noncomputable propositional Alias. The actual Alias
is the reflexive/symmetric/transitive closure of a finite list of Nat identity edges,
not semantic type equivalence. This cycle removes that particular computational gap.

## Contract

For every actual saturation state and every root/query identity, a terminating Bool
classifier equals true iff the existing Alias proposition. Original ordered site
filter and flatMap are retained, so the new requests list must be literally equal
to GeneralNominalCenteredHeadOutputs.requests, including duplicates and order.

The baseline implementation may enumerate all finite cuts of the vertex universe
(root,query,all edge endpoints). The query is reachable iff every edge-closed cut
containing root contains query. The finite subset enumeration terminates by structural
recursion on the finite vertex list. Soundness/completeness use edge closure induction
and the reachable cut respectively. This is exponential and intended as a verified
reference, not a performant compiler. A later BFS refinement must prove equivalence.

## Integration obligations

1. Executable classifier iff Alias with no external closure/correctness hypothesis.
2. Executable requests = current noncomputable requests; arbitrary snapshots/root.
3. Transport the cycle261 fixed-snapshot coverage and finite rebase driver to the new
   selection without weakening its ClassEffects meaning or changing fixed-Plan scope.
4. Regression: disconnected identities, reverse edge, transitive path through a
   non-site vertex; original request order and duplicates retained.

The source-wide finite pool across arbitrary installations and dynamic Plan/capture
transport remain separate. Completion and satisfiability must not be conflated.
Yulang2 is not invoked for an internal graph algorithm; existing source alias semantics
are the reference. Entire repo build is prohibited for this worker; focused modules
and independent standalone axiom/usage audits will be run.

## Verified refinement and source-wide pool

The cut baseline has now been refined to a finite frontier search. It starts with
visited=[root] and remaining=all alias-edge endpoints. Each progressing recursion
filters every newly adjacent endpoint out of remaining, strictly decreasing its
length (duplicates are removed together). An edge-closure invariant plus actual
Alias induction proves exact component membership. The implementation computes one
component per root before filtering the original sites; request order/multiplicity
remain unchanged. No semantic type-equivalence decision is substituted for Alias.

The actual child allocation has a stronger finite-pool result than the prior
Absorbed-only preservation lemma: child output targets are either named output
purpose2 ports or equation-specific purpose5 ports. Existing source-formation,
Paterson lineage and finite owner port results enumerate all such targets for every
reachable installation. With the registry's finite output-name menu and initial
root targets, their Cartesian product covers every raw site output throughout the
actual mixed-source trace, without Absorbed. Refresh/merge/equate/reobserve preserve
sites, enqueue is impossible for an already Generated root in these source paths,
and install appends only covered child outputs.

That source-wide pool feeds the *new* finite rebase Step. A supplied observer may
select different source snapshots at different rebase states, provided each is
reachable from the same source Initial. Requests are executable, and every step's
ClassEffects refers to its actual selected snapshot/root. A proof-only DynamicTrace
retains each snapshot/root at its precise intermediate state and yields one history
for all assignments simultaneously. The fixed Plan supplies fact meaning throughout.

This does not construct the observer from rebase state, show it simulates old Step,
or show all meaningful source observations are scheduled. Its reachability premise
is explicit. Source Initial gives existence of a finite candidate pool; extracting
it as a user-facing compiler artifact is separate. Ready, Frame, packet validity,
model existence, arbitrary dynamic Plan/capture transport and full EvidenceNode remain
unproved here. Quiescence is for the supplied new observer, not all old language actions.
