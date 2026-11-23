import Yulang.GeneralDeclarativeWitnessTwoSourcedEndpoints358
import Yulang.CommonRoleAssociatedObstructions

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecordWindowFixture358
open GeneralDeclarativeWitnessTwoSourcedEndpoints358 (Window Read check lowerRow upperRow left right independently_sourced)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (record Ty Equivalent Subtype subtype_refl common_union_is_join)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

def window : Window := ⟨7,⟨60,61,62⟩,1,2,0,0⟩
def authored : Source := ⟨[lowerRow window,upperRow window]⟩
def current : State := ⟨⟨[left window,right window],[]⟩,authored.authored⟩

theorem actual_two_source_heads : check authored current window = true := by decide +kernel

theorem center_has_no_equation : ∀ row ∈ current.equations,row.left ≠ window.argument.center := by
  intro row member
  simp only [current,authored,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> decide

theorem current_constraints_are_not_origins : check ⟨[]⟩ current window = false := by decide +kernel

def payload : Ty := .union (.base .int) (.base .bool)

def currentModel (tail : Ty) : Assignment := fun k =>
  (if k = 0 then tail else if k = 1 then .base .int else if k = 2 then payload else
    if k = 62 then record 7 payload tail else record 7 (.base .int) tail,Common.rowEmpty)

theorem integer_to_payload : Subtype (.base .int) payload :=
  ((common_union_is_join _ _ _).mp (subtype_refl payload)).1

theorem strict_original_payload_bounds : ¬ Subtype payload (.base .int) := by
  intro wrong
  have sub := ((common_union_is_join (.base .int) (.base .bool) (.base .int)).mp wrong).2
  have impossible := (CommonNominalFullModelMap.subtype_exact (.base .bool) (.base .int)).mp sub
  have not := (CommonRigidHeadInspection.base_iff .bool .int).mp impossible
  cases not

theorem model_fits (tail : Ty) : Models current (currentModel tail) := by
  refine ⟨⟨?_,fun _ empty => False.elim (List.not_mem_nil empty)⟩,?_⟩
  · intro atom member
    simp only [current,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact subtype_refl _
    · exact CommonNominalFullCarrier.common_record_mono 7 integer_to_payload (subtype_refl tail)
  · intro eq member
    simp only [current,authored,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact eqv_refl _

theorem actual_record_window_without_center_read (tail : Ty) :
    Read authored current window ∧ Models current (currentModel tail) ∧
      Subtype ((currentModel tail) window.lowField).1 ((currentModel tail) window.highField).1 ∧
      ¬ Subtype ((currentModel tail) window.highField).1 ((currentModel tail) window.lowField).1 := by
  have written := (GeneralDeclarativeWitnessTwoSourcedEndpoints358.check_exact).mp actual_two_source_heads
  have fit := model_fits tail
  exact ⟨written,fit,(independently_sourced written (currentModel tail) fit).2.2.2.2,
    strict_original_payload_bounds⟩

end Yulang.GeneralDeclarativeWitnessRecordWindowFixture358
