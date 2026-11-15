# Cycle196 follow-up: executable descriptor-changing refresh

The first cycle196 example intentionally supplied no all-model refresh certificate.
This distinct follow-up uses the existing `GeneralNominalRefreshFork` example,
whose ordinary source equation aliases source 0 to source 1. Source 1 already
carries the nominal descriptor. Hence the new descriptor at source 0 is sound in
**every** old source model, not just in the displayed inhabited assignment.

`GeneralNominalExecutableView196` lifts that existing refinement and exactness
proof into the unchanged `GeneralNominalCenteredSteps.Refresh` certificate for
an actual head-step state. `actual_step` proves the exact WF boundary Step,
including generated root, supported source, unknown-before and known-after.
`same_models` proves all-model equivalence and `inhabited` gives the explicit
existing assignment before and after. `descriptor_changed` records the insertion.
Both the precise and wider parameter choices are covered.

`preserve_variable_evidence` combines this executable descriptor change with the
new variable-query reinspection theorem and complete source-tree transport. Its
inputs are variable-only computed query shape, a specific old-state model, and
old source evidence. Its output is the identical payload at the same model after
the actual Step. It does not assume report equality or a semantic transport law.

This is not a claim of Initial, Reachable or Stable for an arbitrary registry;
actual Step and model inhabitation are the established execution facts. Nor does
it manufacture an old dictionary from nothing: source evidence is the object
being transported. General nominal-query refresh and current-Frame regeneration
remain outside this result. The Step does not depend on registry membership,
but the evidence-preservation theorem retains its precise registry conditions.

Audit: `lean/Audit/Cycle196Executable.lean` prints all six theorem types/axioms
and checks every declaration from imported cycle196 modules against only
`propext`, `Classical.choice`, `Quot.sound`, under trust0/warning-as-error.
Focused target: `Yulang.GeneralNominalExecutableView196`; no full build or CI.
