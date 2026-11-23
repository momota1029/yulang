import Yulang.GeneralDeclarativeWitnessSelectedSourceMeaning363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 79000
set_option maxHeartbeats 100000000
namespace Yulang.GeneralDeclarativeWitnessActualCrossOwnerDictionary363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessSelectedNonpointChild363 (Complete close actual)
open GeneralDeclarativeWitnessSelectedSourceMeaning363 (Local Meaning rootQuery actual_ordered_classification)
open GeneralDeclarativeWitnessOrderedDictionary363 (Evidence)
open GeneralDeclarativeWitnessCrossOwnerModel362 (stage model fits_current)
open GeneralDeclarativeWitnessNonpointPortModel362 (exact exact_model_iff)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted NativeViews)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)

def checked {contra x} (s : @Complete contra x) : Bool :=
  actual s && exact s.child.world.ordinary (stage contra)

theorem checked_exact_body_in_both_variances (contra : Bool) :
    ((run contra).bind fun x => (close x).map checked).getD false = true := by cases contra <;> decide +kernel

theorem actual_dictionary_read_for_each_fitting_model (contra : Bool) :
    ∃ (x : Ordered contra) (s : Complete x), run contra = some x ∧ close x = some s ∧
      Classify (Local s) rootQuery (.selected (.node 97 [.node 98 []])) ∧
      (∀ u,Fits s.child.world (model contra u) (interpreted s.child.world.board (model contra u))) ∧
      ∀ (m : Assignment) (v : NativeViews),Fits s.child.world m v →
        Evidence (Meaning s m v) rootQuery (.node 97 [.node 98 []]) := by
  have stage := checked_exact_body_in_both_variances contra
  cases began : run contra with
  | none => rw [began] at stage; cases stage
  | some x =>
    rw [began] at stage
    change ((close x).map checked).getD false = true at stage
    cases result : close x with
    | none => rw [result] at stage; cases stage
    | some s =>
      rw [result] at stage
      have claims := Bool.and_eq_true_iff.mp (show checked s = true from stage)
      have ids := of_decide_eq_true claims.1
      have clean : Classify (Local s) rootQuery (.selected (.node 97 [.node 98 []])) := by
        have direct := actual_ordered_classification s
        rw [ids.1,ids.2.1] at direct
        exact direct
      refine ⟨x,s,rfl,result,clean,?_,?_⟩
      · intro u
        exact ⟨(exact_model_iff claims.2 _).mpr (fits_current contra u),fun _ => rfl⟩
      · intro m v fit
        exact GeneralDeclarativeWitnessSelectedSourceMeaning363.every_actual_selected_dictionary_same_model s began m v fit clean

end Yulang.GeneralDeclarativeWitnessActualCrossOwnerDictionary363
