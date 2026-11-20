import Yulang.GeneralRebaseRowParentPacket287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseRowParentOutput287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231 (Outputs Holds variables emittedSchema)
open GeneralNominalCenteredHeadMatSchemas (Schema Equation)
open CommonNominalFullCarrier

theorem outputs_exact (choice : Bool) (m : Assignment) :
    Outputs (plan choice) m ↔ Equivalent (m 2).1 (F (F (m 0).1)) := by
  unfold Outputs
  rw [emitted]
  constructor
  · intro all
    have h := all _ (List.mem_cons_self ..)
    change Equivalent (m 2).1 (F (F (variables (plan choice) m .actual 0))) at h
    rwa [variables_same] at h
  · intro out eq member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · change Equivalent (m 2).1 (F (F (variables (plan choice) m .actual 0)))
      rwa [variables_same]
    · change Equivalent (m 0).1 (variables (plan choice) m .lower 0)
      rw [variables_same]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · change Equivalent (m 0).1 (variables (plan choice) m .upper 0)
      rw [variables_same]
      exact ⟨subtype_refl _,subtype_refl _⟩

theorem concrete_outputs (choice : Bool) (row : Common.Row) : Outputs (plan choice) (model row) :=
  (outputs_exact choice _).mpr ⟨subtype_refl _,subtype_refl _⟩

def replaceOutput (m : Assignment) : Assignment :=
  fun id => (if id = 2 then F (F (m 0).1) else (m id).1,(m id).2)

theorem completion_rows (a : Assignment) (n : Nat) : (replaceOutput a n).2 = (a n).2 := rfl

theorem completion_types (a : Assignment) (n : Nat) (notOutput : n ≠ 2) :
    (replaceOutput a n).1 = (a n).1 := by
  exact ite_eq_right notOutput

theorem completed_outputs (choice : Bool) (a : Assignment) :
    Outputs (plan choice) (replaceOutput a) := by
  apply (outputs_exact choice _).mpr
  change Equivalent (F (F (a 0).1)) (F (F (a 0).1))
  exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralRebaseRowParentOutput287
