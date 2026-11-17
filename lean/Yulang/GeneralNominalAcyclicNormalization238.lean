import Yulang.GeneralNominalAcyclicEquations237
import Yulang.GeneralNominalAssignmentCongruence238
set_option backward.isDefEq.respectTransparency false
/-! Normalizing an already satisfied descending equation ledger preserves every
type up to full nominal equivalence and every row literally. -/
namespace Yulang.GeneralNominalAcyclicNormalization238
open GeneralNominalFiniteEquationRealization236 (Entry)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalAcyclicEquations237
open GeneralNominalAssignmentCongruence238 (Same)
open CommonNominalFullCarrier
variable (entries : List Entry) (base : Assignment)

theorem preserves (coherent : Coherent entries) (descending : Descending entries)
 (valid : ∀ entry ∈ entries, PresenceNormalForm.All model base
   (GeneralNominalAllocation.equations entry.1 entry.2)) :
 Same (solution entries base) base := by
 intro n
 refine ⟨?_,rfl⟩
 induction n using Nat.strongRecOn with
 | ind n ih =>
   classical
   by_cases present : ∃ entry ∈ entries, entry.1 = n
   · obtain ⟨entry,member,rfl⟩ := present
     have equation := GeneralNominalAcyclicEquations237.equation entries base coherent descending entry member
     let intermediate : Assignment := fun m => if m < entry.1 then solution entries base m else base m
     have aligned : Same intermediate base := by
       intro m
       dsimp [intermediate]
       split
       · rename_i below; exact ⟨ih m below,rfl⟩
       · exact ⟨⟨subtype_refl _,subtype_refl _⟩,rfl⟩
     have restricted : entry.2.eval model (solution entries base) = entry.2.eval model intermediate := by
       apply GeneralNominalCenteredModelExtension.type_eval_same
       intro m used
       simp only [intermediate,descending entry member m used,ite_true]
     have evaluated := GeneralNominalAssignmentCongruence238.type_eval aligned entry.2
     have original := (GeneralNominalCaptureMerges.equations_exact base entry.1 entry.2).mp (valid entry member)
     rw [equation,restricted]
     exact ⟨subtype_trans evaluated.1 original.2,subtype_trans original.1 evaluated.2⟩
   · have absent : ∀ entry ∈ entries, entry.1 ≠ n := by
       intro entry member equal; exact present ⟨entry,member,equal⟩
     rw [outside entries base absent]
     exact ⟨subtype_refl _,subtype_refl _⟩

theorem ordinary_iff (coherent : Coherent entries) (descending : Descending entries)
 (valid : ∀ entry ∈ entries, PresenceNormalForm.All model base
   (GeneralNominalAllocation.equations entry.1 entry.2)) (atoms : List (PresenceNormalForm.Atom Nat)) :
 PresenceNormalForm.All model (solution entries base) atoms ↔ PresenceNormalForm.All model base atoms :=
 GeneralNominalAssignmentCongruence238.all_iff (preserves entries base coherent descending valid) atoms
end Yulang.GeneralNominalAcyclicNormalization238
