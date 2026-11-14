# Independent semantic review: cycle176 observation transport

Reviewed ViewFootprint176, CenteredFootprint176, CenteredRevision176,
HeadFootprintRegression176 and the checkpoint report at 23:48 UTC. Read-only;
no source changes, no new builds, no cache writes.

## Scope/report issues to keep explicit

1. RecordedFootprints / Agrees are finite syntactic predicates, but no executable
boolean checker or checker-correctness/complexity theorem is supplied here.
The bounded quantifiers are effectively finite: registry/packets are lists,
argument lookup and nominal descriptor lookup have unique successful results,
and recursion decreases query size. Describing this as a finite syntactic
condition is accurate; claiming an implemented, tested finite checker is not.

2. Revision176 is narrower than an arbitrary descriptor replacement. Existing
Revision fixes carrier, normalized view, constructors/interpretation and the
None/Some descriptor domain. It also requires Certified (raw model restriction
and exact ordinary-journal model equivalence) and Improves (strict descriptor
point progress). FootprintAt then preserves descriptors on queried slots.
Refines is absent, but these other assumptions are not absent.

3. Refresh and Revision retain inherited SEMANTIC certification. The new guard
is not Instance/Evidence/report equality; that does not mean the overall
transition has no semantic premises. Use 'no new semantic evidence guard', not
'unconditional executable refresh' or 'no semantic premises'.

4. HeadFootprintRegression176 gives nonempty ordinary models, a changed view,
a finished scalar query and preserved report outside the old nominal-only
fragment. As its own comment says, it is not a known-progress centered Refresh
witness. The new generic actual-trace theorem is not accompanied here by an
inhabited nonempty-journal footprint Refresh/Revision example. Do not combine
these separate claims into such a concrete execution claim.

## Checks that passed the source review

- HeadObservation fixes shape catalogue and finite source carrier explicitly.
  Scalar guard checks only lower head because scalar inspection reads that head;
  node guard checks both endpoint structural heads and recurses into zipped
  children; nominal guard follows uniquely looked-up old descriptor arguments.
  Variable leaves require no view equality. Guard is conservative, not minimal.
- Refines preserves existing nominal descriptors in ViewFootprint176. Opacity
  certificates prevent a scalar old head from simultaneously acquiring a
  nominal descriptor while its head remains fixed. No report preservation is
  assumed in the new recursive guard.
- instance_refinement consumes the SAME model in old Instance and new state
  Models; branch transport uses computed report equality and explicit target
  validity. Context metadata and child order are retained via existing transport.
- CenteredFootprint/Revision derive current-recorded invariants from empty
  journal, not from an input semantic invariant in their public initial theorem.
  For arbitrary-start helper lemmas the supplied RecordedCurrent is explicit.
- Revision_instance uses certificate.exact on final ordinary model and carries
  unchanged center ledger components; it does not substitute another model.
- Whole Evidence needs a syntactic RecordedTree. It derives child Evidence
  recursively, but does not prove that all selected Local outcomes produce
  trees. No general G EvidenceNode follows and report correctly leaves it open.
