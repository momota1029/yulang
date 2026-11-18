import Yulang.GeneralNominalActiveMergeExample249
import Yulang.GeneralNominalActivePropagationModels249
/-! The active-pool extension has real witnesses; fresh cross constraints are
also necessary. These are allocation primitive examples, not source traces. -/
namespace Yulang.GeneralNominalActiveCrossExample249
open GeneralDeclarations GeneralNominalAllocation
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalActiveMergeExample249
open CommonNominalFullCarrier

def constant : Assignment := fun _ => (.emptyRecord,Common.rowEmpty)

theorem constant_compatible : Compatible freshBindings constant := by
 intro first _ last _ _
 exact subtype_refl _

theorem second_exists (registry : Registry) :
 ∃ extended, GeneralNominalState.Models (propagate (first registry) registry 0 declaration freshBindings) extended := by
 obtain ⟨extended,valid,_,_,_⟩ := second_model registry constant constant_compatible
 exact ⟨extended,valid⟩

def boundary : Assignment := fun name =>
 (if name = 0 then model.exactEmpty else .emptyRecord,Common.rowEmpty)

theorem old_cross : Compatible oldBindings boundary := by
 intro first one last two _
 have a : first = (7,(0,1)) := by simpa [oldBindings] using one
 have b : last = (7,(0,1)) := by simpa [oldBindings] using two
 subst first; subst last
 exact exactEmpty_below_width

theorem first_model (registry : Registry) : GeneralNominalState.Models (first registry) boundary := by
 apply (propagate_models initial registry 0 declaration oldBindings boundary).mpr
 refine ⟨initial_models boundary,old_cross,?_⟩
 intro atom member; cases member

theorem new_cross_impossible : ¬ Compatible freshBindings boundary := by
 intro cross
 have bad := cross (7,(1,0)) (by simp [freshBindings]) (7,(1,0)) (by simp [freshBindings]) rfl
 exact width_not_below_exactEmpty bad

theorem public_second_impossible (registry : Registry) :
 ¬ ∃ assignment,
   GeneralNominalState.Models (propagate (first registry) registry 0 declaration freshBindings) assignment ∧
   GeneralNominalActivePropagationModels249.PublicAgrees [0,1] assignment boundary := by
 rintro ⟨assignment,valid,agree⟩
 have cross := ((propagate_models (first registry) registry 0 declaration freshBindings assignment).mp valid).2.1
 have bad := cross (7,(1,0)) (by simp [freshBindings]) (7,(1,0)) (by simp [freshBindings]) rfl
 change Subtype (assignment 1).1 (assignment 0).1 at bad
 rw [agree 1 (by simp),agree 0 (by simp)] at bad
 exact width_not_below_exactEmpty bad
end Yulang.GeneralNominalActiveCrossExample249
