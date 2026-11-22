import Yulang.GeneralDeclarativeStoppedRetarget341
import Yulang.GeneralWhereVersionCurrentCert317
import Yulang.GeneralDictionaryDefaultObserved209

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeVersionedRetarget342
open GeneralNominalCenters (Plan)
open GeneralNominalRefinements (Refines)
open GeneralRebaseRetarget275 (retarget Observed)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalVersionedPlans231 (HeadModels)
open GeneralNominalCommonBridge (Assignment)

section
variable {roles : Roles.RoleDecls} {after : GeneralNominalCandidates.Context}
variable (old : Plan roles) (ref : Refines old.packet.context.state after.state)
variable (interp : after.interpretation = old.packet.context.interpretation) (seen : Observed old)

include interp seen in
theorem same : Same (retarget old ref) old := by
  refine ⟨rfl,rfl,rfl,ref.seed,ref.constructors,interp,?_⟩
  rw [GeneralRebaseRetarget275.report old ref interp seen]
  exact GeneralDictionaryDefaultObserved209.erase_report ref _

include interp seen in
theorem head (m : Assignment) (fresh : GeneralNominalState.Models after.state m)
    (oldModel : HeadModels old.packet m) : HeadModels (retarget old ref).packet m := by
  obtain ⟨_,facts⟩ := (GeneralNominalVersionedPlans231.private_models_iff _ m).mp oldModel.1
  exact ⟨(GeneralNominalVersionedPlans231.private_models_iff _ m).mpr ⟨fresh,
      (GeneralRebaseRetarget275.ordinary old ref interp seen m).mpr facts⟩,
    (GeneralRebaseRetarget275.projection old ref interp seen m).mpr oldModel.2⟩

include interp seen in
/-- Only versioned where rows are transported. A stored old effective
choice is not promoted to a current unversioned packet. -/
theorem holds (m : Assignment) (fresh : GeneralNominalState.Models after.state m)
    (prior : Holds old m) : Holds (retarget old ref) m := by
  have view := same old ref interp seen
  have schema := GeneralWhereVersionRecompile317.schema_eq view
  have variables := GeneralRebaseRetarget275.variables_eq old ref interp seen m
  refine ⟨head old ref interp seen m fresh prior.head,prior.input,?_,?_,schema.symm ▸ prior.materialized,?_,?_⟩
  · intro name needs
    rw [GeneralRebaseRetarget275.capture old ref interp seen,GeneralRebaseRetarget275.binder old ref interp seen]
    exact prior.captures name needs
  · rw [GeneralRebaseRetarget275.head_schema old ref interp]
    exact (GeneralRebaseRetarget275.schema_holds old ref interp seen _ m).mpr prior.headSchema
  · rw [schema,variables]
    exact prior.rows
  · intro clause belongs sig
    have priorChild := prior.childSemantics clause belongs sig
    rw [GeneralWhereVersionCurrentCert317.child_site_eq view clause sig,
      GeneralRebaseNonleafRetarget276.child_schema_eq old ref interp seen clause sig,variables]
    exact priorChild

end
end Yulang.GeneralDeclarativeVersionedRetarget342
