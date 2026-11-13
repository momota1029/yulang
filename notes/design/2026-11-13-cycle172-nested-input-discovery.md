# Cycle172: actual nested input discovery

Status: scoped proof design. General V5 remains open.

Data: a finite unary nominal query spine ending in a nominal leaf whose
ordered arguments are singleton variable queries. This is syntax only, not a
source descriptor witness or semantic Evidence.

Goal: for every state, names, syntax spine, physical root slot and origin,
Finished actual inspection together with point descriptor arguments yields an
actual `GeneralNominalSpineFacts.Spine` with exactly the original query.
The final theorem restricts only the lower-slot descriptors actually visited by
this input inspection to point arguments (`PointInspection`); unrelated
descriptors may be arbitrary. This is a representation restriction, not a
language rule. Existing depth-one
leaf extraction allows arbitrary interval arguments; no earlier result is
weakened. All other restrictions remain explicit (linear names for later
input certificate construction, terminal declaration, actual root location).

This closes the arbitrary-depth descriptor-discovery subproblem only. It does
not derive output request physical identities, handle nonpoint wrappers or
branching/repeated-binder heads, or prove general Reachable/Stable Coverage.
Astra's Step/Stable/Generated definitions are not changed.

## Verified result

`GeneralDictionary172CoverageInput.inspected_spine` recurses over syntax only,
extracting each actual descriptor, exact arity and physical child from Finished.
`input_exists` constructs the terminal Input; `checked_uniform_evidence`
composes it with the actual executable request checker. Its conclusion uses
one explicit payload before the model quantifier. Registry visibility, checked
declaration, terminality, role, injective names, root query and location,
RootDefined, actual Finished, PointInspection, checker success and Metadata all
remain explicit. It is a soundness/auxiliary fragment, not general completeness.

The example uses the prior inhabited `GeneralNominalProvenanceSource.state`,
two nested nominal queries, and physical root slot zero. Finished and the
point-report checker are computed with kernel reduction. A stored Spine is not
supplied. The older nonpoint outer pair (0,3) is not asserted covered.

## General evidence gap (read-only review)

- Shared Stable says there is no enabled generated At step. It is not a
  constructor-specific descriptor or physical-output-location certificate.
- A recorded Node still needs `Relocates`, comparing historical packet reports
  and schemas with current descriptors. SourceFormed supplies journal model
  facts, not a demonstrated preservation theorem for arbitrary descriptor
  refresh. Ordinary extension preservation is narrower.
- A terminal named Node still needs its input fragment and observation of all
  emitted output requests. InitialSource/Linked alone does not provide physical
  output slots: the existing reserved-output regression proves this.
- Consequently general Reachable/Stable-to-Coverage is not proved by merely
  combining the existing constructor theorems. The next meaningful obligation
  is actual inspection/refresh completeness for the eligible chosen packet,
  with source identity retained; then recursively close its chosen children.

No change to Step, Stable, Generated, the guards, or the V5 boundary was made.
The 8/14 remaining V5 count does not change. Yulang2: this is structural
certificate extraction from existing Lean inspection; no new runtime oracle
was run and no equivalence to all Yulang2 executions is claimed.
