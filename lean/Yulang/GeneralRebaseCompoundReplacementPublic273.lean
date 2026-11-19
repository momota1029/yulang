import Yulang.GeneralRebaseCompoundReplacementFrame273

set_option maxRecDepth 24000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralRebaseCompoundReplacementPublic273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundPointModel238 (extended)
open GeneralDictionaryCompoundObstruction238 (oldPlan currentPlan)
open GeneralRebaseCompoundReplacement273 (patch lower shape)
open GeneralRebaseCompoundReplacementFrame273 (Meaning canonical_valid fixed_of_meaning meaning_row_free meaning_equivalent)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseCompoundRowsMeaning273 (Public)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

noncomputable def updateTypes (boundary : Assignment) : Assignment :=
 fun id => (if id ≤ 4 then (boundary id).1 else (patch extended id).1,(patch extended id).2)

theorem update_same (boundary : Assignment) (fixed : Fixed boundary) :
 GeneralNominalAssignmentCongruence238.Same (patch extended) (updateTypes boundary) := by
 intro id
 refine ⟨?_,rfl⟩
 by_cases publicSlot : id ≤ 4
 · simp only [updateTypes,publicSlot,ite_true]
   have canonical := fixed_of_meaning _ canonical_valid id publicSlot
   have other := fixed id publicSlot
   exact equivalent_trans canonical ⟨other.2,other.1⟩
 · simp only [updateTypes,publicSlot,ite_false]
   exact ⟨subtype_refl _,subtype_refl _⟩

noncomputable def complete (boundary : Assignment) : Assignment :=
 fun id => ((updateTypes boundary id).1,(boundary id).2)

theorem agrees (boundary : Assignment) : Agrees (complete boundary) boundary := by
 refine ⟨?_,fun _ => rfl⟩
 intro id publicSlot
 simp [complete,updateTypes,publicSlot]

theorem completed (boundary : Assignment) (fixed : Fixed boundary) : Meaning (complete boundary) := by
 have prior := (meaning_equivalent (update_same boundary fixed)).mp canonical_valid
 have same : GeneralRebaseRowIrrelevance273.SameTypes (updateTypes boundary) (complete boundary) := fun _ => rfl
 exact (meaning_row_free same).mp prior

theorem public_exact (boundary : Assignment) :
 (∃ replacement, Agrees replacement boundary ∧ Meaning replacement) ↔ Fixed boundary := by
 constructor
 · rintro ⟨m,agree,valid⟩ id bounded
   rw [← agree.1 id bounded]
   exact fixed_of_meaning m valid id bounded
 · intro fixed
   exact ⟨complete boundary,agrees boundary,completed boundary fixed⟩

theorem same_public (boundary : Assignment) :
 (∃ replacement, Agrees replacement boundary ∧ Meaning replacement) ↔ Public point boundary :=
 (public_exact boundary).trans
  ((GeneralRebaseCompoundRows273.public_exact boundary).symm.trans
    (exists_congr (fun m => and_congr Iff.rfl (GeneralDictionaryCompoundPoint238.models_iff m).symm)))

theorem no_common_same_assignment (m : Assignment) (historical : Models point m) : ¬ Meaning m :=
 fun replace => GeneralDictionaryCompoundObstruction238.no_current_packet m historical replace.1

theorem both_witnesses (boundary : Assignment) (fixed : Fixed boundary) :
 ∃ historical replacement, Agrees historical boundary ∧ Agrees replacement boundary ∧
 Models point historical ∧ Meaning replacement ∧ historical ≠ replacement := by
 obtain ⟨h,hSame,old⟩ := (same_public boundary).mp ((public_exact boundary).mpr fixed)
 refine ⟨h,complete boundary,hSame,agrees boundary,old,completed boundary fixed,?_⟩
 intro merge
 exact no_common_same_assignment h old (merge ▸ completed boundary fixed)

end Yulang.GeneralRebaseCompoundReplacementPublic273
