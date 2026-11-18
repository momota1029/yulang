import Yulang.GeneralNominalPersistentOwner250
import Yulang.GeneralPresenceCommonLaws245
namespace Yulang.GeneralPresenceSnapshotGrowth251
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceUsedSupport245 (typedReads)
open CommonNominalFullCarrier

def tree : Nat → TyTerm Nat
 | 0 => .var 0
 | n+1 => .union (tree n) (tree n)

def height : TyTerm Nat → Nat
 | .union first last => 1 + max (height first) (height last)
 | _ => 0

def definitions (n : Nat) : List (Entry Nat) := [(2,tree n)]
def raw : List (Entry Nat) := [(2,.union (.var 2) (.var 2))]

theorem height_tree (n : Nat) : height (tree n) = n := by
 induction n with
 | zero => rfl
 | succ n ih => simp [tree,height,ih,Nat.add_comm]

theorem next_different (n : Nat) : tree (n+1) ≠ tree n := by
 intro equal
 have contradiction := congrArg height equal
 rw [height_tree,height_tree] at contradiction
 omega

theorem reads_zero (n : Nat) (name : Nat) (member : name ∈ typedReads (tree n)) : name = 0 := by
 induction n with
 | zero => simpa [tree,typedReads] using member
 | succ n ih =>
   simp only [tree,typedReads,List.mem_append] at member
   exact member.elim ih ih

theorem safe (n : Nat) : SafeOrder (definitions n) := by
 refine ⟨?_,by simp,by simp,True.intro⟩
 intro member
 have impossible := reads_zero n 2 member
 omega

theorem refresh (n : Nat) : GeneralPresencePersistentSnapshot250.refresh (definitions n) raw = definitions (n+1) := rfl

theorem fixed_target (n : Nat) : (definitions n).map Prod.fst = [2] := rfl

theorem no_uniform_height_bound : ¬ ∃ bound, ∀ n, height (tree n) ≤ bound := by
 rintro ⟨bound,holds⟩
 have impossible := holds (bound+1)
 rw [height_tree] at impossible
 omega

theorem union_self (value : Ty) : Equivalent (.union value value) value := by
 constructor
 · exact (common_union_is_join value value value).mpr ⟨subtype_refl _,subtype_refl _⟩
 · exact ((common_union_is_join value value (.union value value)).mp (subtype_refl _)).1

theorem same_value (n : Nat) (assignment : GeneralNominalCommonBridge.Assignment) :
 Equivalent ((tree n).eval model assignment) (assignment 0).1 := by
 induction n with
 | zero => exact ⟨subtype_refl _,subtype_refl _⟩
 | succ n ih =>
   have duplicate := union_self ((tree n).eval model assignment)
   exact ⟨subtype_trans duplicate.1 ih.1,subtype_trans ih.2 duplicate.2⟩
end Yulang.GeneralPresenceSnapshotGrowth251
