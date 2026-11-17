import Yulang.GeneralNominalRebaseInline241
import Yulang.GeneralNominalAssignmentCongruence238
set_option backward.isDefEq.respectTransparency false
/-! Reconstructed proof producer. Freshly verified against restored Inline241. -/
namespace Yulang.GeneralNominalRebaseInlineModels241
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open CommonNominalFullCarrier
variable (entries : List Entry)
 (coherent : ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2)
 (model : Assignment)
 (valid : ∀ entry ∈ entries, PresenceNormalForm.All CommonNominalFullCarrier.model model
   (GeneralNominalAllocation.equations entry.1 entry.2))
include coherent valid
theorem patch_same : GeneralNominalAssignmentCongruence238.Same (patch entries model) model := by
 classical
 intro name
 refine ⟨?_,row entries name⟩
 by_cases found : ∃ entry ∈ entries, entry.1 = name
 · obtain ⟨entry,member,rfl⟩ := found
   rw [value entries coherent entry member]
   have equal := (GeneralNominalCaptureMerges.equations_exact model entry.1 entry.2).mp (valid entry member)
   exact ⟨equal.2,equal.1⟩
 · rw [outside entries (fun entry member equal => found ⟨entry,member,equal⟩)]
   exact ⟨subtype_refl _,subtype_refl _⟩
theorem atom_iff (atom : PresenceNormalForm.Atom Nat) :
 (GeneralNominalRebaseInline241.atomSubst (GeneralNominalRebaseInline241.substitution entries) atom).Holds
   CommonNominalFullCarrier.model model ↔ atom.Holds CommonNominalFullCarrier.model model :=
 (GeneralNominalRebaseInline241.atom_inline coherent atom model).trans
   (GeneralNominalAssignmentCongruence238.atom_iff (patch_same entries coherent model valid) atom)

theorem all_iff (atoms : List (PresenceNormalForm.Atom Nat)) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model
   (atoms.map (GeneralNominalRebaseInline241.atomSubst (GeneralNominalRebaseInline241.substitution entries))) ↔
 PresenceNormalForm.All CommonNominalFullCarrier.model model atoms :=
 (GeneralNominalRebaseInline241.all_inline coherent atoms model).trans
   (GeneralNominalAssignmentCongruence238.all_iff (patch_same entries coherent model valid) atoms)
end Yulang.GeneralNominalRebaseInlineModels241
