# Cycle196: descriptor-changing reinspection transport

Scope: WF/V6 dictionary evidence; no replacement of supervisor transition rules.
Replace only a nominal state's normalized view and nominal-descriptor function,
retaining the source slots, constructor table, allocation seed and ordinary atoms.
A structural reinspection certificate compares actual report fields after replacement.
It assumes no semantic Evidence, dictionary, branch truth, Frame or solver result.
The new state model and old branch together should imply the rechecked branch.
Then arbitrary finite source dictionaries retain the exact same payload in the same
assignment. Actual WF refresh is connected only when its target is this replacement
and the relevant reports agree. General refresh production remains open: a refresh
can change an inspected report, so model equivalence alone does not suffice.

## Module guide and hypotheses

- `GeneralNominalViewTransport196`: `View` carries a checked normalized view and
  opaque, catalogue-valid nominal descriptors, while `replace` preserves all other
  fields. `Rechecked` compares the *actual* recursive inspection report; it does
  not assume branch truth. `branch_transport` derives the new branch from the old
  branch, reinspection, and the chosen final model's actual new-state validity.
  `instance_transport` preserves the visible declaration, checked schema, bounds,
  request readiness, child list and metadata. `evidence_transport` inducts over
  every source dictionary node and retains the identical tree/readback payload.
- `GeneralNominalViewRefresh196`: transport is connected to the existing WF
  `refresh` and `GeneralNominalCenteredSteps.Refresh` certificate. The universal
  form obtains the old-state model from that actual certificate. Current
  `Reusable` plans yield source instances in the new context, not new Frames.
- `GeneralNominalVariableView196`: for variable-only computed query shapes,
  structural induction over query/bounds lists proves reinspection agreement for
  arbitrary checked descriptor/view replacement. This discharges `Rechecks` for
  variable-only registries and is not an assumption of report equality.
- `GeneralNominalViewExample196`: insertion of a real list descriptor at slot 0
  from an empty nominal table. Both old and new contexts share the explicit
  example model. The variable query really reinspects identically for all bounds,
  including the nonempty example. The transformation provably is not an ordinary
  context extension. The descriptor is not read by this variable-only query.

## Explicit remaining boundary

The example is a context transformation, not a constructed executable refresh:
no all-model refresh certificate is claimed for descriptor insertion. The
universal WF theorem requires that certificate and report agreement. Arbitrary
nominal/node query refreshes can change reports and are not covered. Bounds and
source/constructor/allocation skeletons are fixed. No theorem regenerates a
current Frame from a historical Frame, proves a general stable-source producer,
or closes I32/V6 for unrestricted actual traces. The cycle195 completion
obstruction remains. These results are a descriptor-changing source-evidence
transport layer, not a replacement success predicate or a completeness claim.

## Audit entry points

`lean/Audit/Cycle196Transport.lean` prints axioms for all 24 public theorems;
`Cycle196PublicTypes.lean` exposes every theorem's full type; and
`Cycle196KernelGate.lean` checks every declaration originating in the four new
modules against only `propext`, `Classical.choice`, `Quot.sound`. Run with
`lake env lean --trust=0 -DwarningAsError=true`. Focused build only, no full
repository build or GitHub CI claim. Frozen `Audit.lean` and README are untouched.
