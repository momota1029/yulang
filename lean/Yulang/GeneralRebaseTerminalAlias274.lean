import Yulang.GeneralRebaseTerminalTypePool274

set_option maxRecDepth 20000
set_option maxHeartbeats 6700000
namespace Yulang.GeneralRebaseTerminalAlias274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryOptionalInstall229 (actual)
open GeneralDictionaryVersionedSecondRaw233 (oldLo oldHi newLo newHi raw_old raw_new)
open GeneralRebaseTerminalTypePool274 (pool covered actual_width)

def widthKeys : List Nat := [actual,oldHi,newLo,newHi]

def sourceId (id : Nat) : Nat :=
 if id = oldLo then 4 else if id ∈ widthKeys then 2 else id

theorem old_lo : sourceId oldLo = 4 := rfl
theorem old_hi : sourceId oldHi = 2 := rfl
theorem new_lo : sourceId newLo = 2 := rfl
theorem new_hi : sourceId newHi = 2 := rfl
theorem center : sourceId actual = 2 := rfl

theorem width_private : widthKeys.all (fun n => 4 < n) = true := by decide +kernel
theorem old_private : 4 < oldLo := by decide +kernel

theorem public_id (n : Nat) (small : n ≤ 4) : sourceId n = n := by
 have notOld : n ≠ oldLo := by have big := old_private; omega
 have notWidth : n ∉ widthKeys := by
   intro mem
   have big : 4 < n := of_decide_eq_true (List.all_eq_true.mp width_private n mem)
   omega
 simp [sourceId,notOld,notWidth]

theorem bounded (id : Nat) (used : id ∈ pool) : sourceId id ≤ 4 := by
 simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at used
 rcases used with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 all_goals decide +kernel

theorem exact_value (m : Assignment) (valid : Models installed m) (id : Nat) :
 Equivalent (m id).1 (m (sourceId id)).1 := by
 have old := raw_old valid.1.1
 have fresh := raw_new valid.1.1
 by_cases a : id = oldLo
 · subst id
   rw [old_lo]
   exact old.1
 · by_cases b : id ∈ widthKeys
   · have source : sourceId id = 2 := by simp [sourceId,a,b]
     rw [source]
     simp only [widthKeys,List.mem_cons,List.not_mem_nil,or_false] at b
     rcases b with rfl | rfl | rfl | rfl
     · exact actual_width m valid
     · exact old.2
     · exact fresh.1
     · exact fresh.2
   · simp only [sourceId,a,b,ite_false]
     exact ⟨subtype_refl _,subtype_refl _⟩

def normalize (m : Assignment) : Assignment := fun id => ((m (sourceId id)).1,(m id).2)

theorem normalize_equivalent (m : Assignment) (valid : Models installed m) :
 GeneralNominalAssignmentCongruence238.Same m (normalize m) :=
 fun id => ⟨exact_value m valid id,rfl⟩

theorem normalize_valid (m : Assignment) (valid : Models installed m) : Models installed (normalize m) :=
 (GeneralNominalVersionedSourceCongruence238.models_iff (normalize_equivalent m valid)
   installed GeneralRebaseTerminalPublic274.final_legacy_empty).mp valid

theorem no_expand_public (boundary : Assignment) (id : Nat) (publicSlot : id ≤ 4) :
 normalize boundary id = boundary id := by simp [normalize,public_id id publicSlot]

theorem rerun (id : Nat) : sourceId (sourceId id) = sourceId id := by
 by_cases first : id = oldLo
 · rw [first,old_lo]
   exact public_id 4 (by decide)
 · by_cases rest : id ∈ widthKeys
   · have fixed : sourceId id = 2 := by simp [sourceId,first,rest]
     rw [fixed]; exact public_id 2 (by decide)
   · have fixed : sourceId id = id := by simp [sourceId,first,rest]
     rw [fixed,fixed]

theorem idempotent (m : Assignment) : normalize (normalize m) = normalize m := by
 funext id
 apply Prod.ext
 · change (m (sourceId (sourceId id))).1 = _
   rw [rerun]; rfl
 · rfl

end Yulang.GeneralRebaseTerminalAlias274
