import Yulang.GeneralDeclarativeI65I74RecordEndpointsChannels422

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
open GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (mask)
open GeneralDeclarativeOpaqueNames328 (kept extend unchanged left_value right_value)
open GeneralDeclarativeFootprint321 (preserves_models stateNames)
open GeneralDeclarativeRecordChannel330 (project)

/-- Model-local names for the actual required projection and mask do
not need an ordinary literal row at the root. Both values can be
given two genuinely fresh names for *each* fitting model, preserving
all old ordinary constraints and designated target addresses.
This still changes arbitrary unused coordinates of the assignment;
it is not a derivation in the fixed SourceHead, and it does not
author or add any equation or choose a lexical source verdict. -/
theorem fresh_projection_names_exist_without_required_optional_agreement422 {p}
    (r : Read p) (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment) :
    ∃ (w : ProjectedRecordChannels r m) (next : Assignment),
      Models p.state.core.current.ordinary next ∧
      (∀ n ∈ kept p.state.core.current.ordinary r.arg.center r.protected, next n = m.assignment n) ∧
      (next r.fieldNames.center).1 = w.required ∧
      (next r.freshTail).1 = mask [r.low.label] (m.assignment r.arg.center).1 := by
  obtain ⟨observations⟩ := same_model_endpoints_support_both_projected_channels422 r m fit
  let current := p.state.core.current.ordinary
  let residue := mask [r.low.label] (m.assignment r.arg.center).1
  let next := extend current r.arg.center r.protected m.assignment observations.required residue
  have old : ∀ n ∈ kept current r.arg.center r.protected, next n = m.assignment n :=
    fun _ preserved => unchanged m.assignment observations.required residue preserved
  have fixed : ∀ n ∈ stateNames current, next n = m.assignment n :=
    fun _ included => old _ (List.mem_append_left _ included)
  exact ⟨observations,next,(preserves_models current fixed).mpr fit,old,
    left_value ..,right_value ..⟩

end Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
