import Yulang.GeneralPresenceRankedTable245
/-! A finite auxiliary check-closure regression. This does not refute a
language theorem: the table is not asserted reachable from source programs. -/
namespace Yulang.GeneralPresenceCheckClosureLimit245
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244 GeneralPresenceOwnerTable244
open GeneralPresenceOwnerOwnership244 GeneralPresenceRankedTable245

def triangle : State Nat Nat where
 base := []
 owners := [0,1,2]
 entries := fun owner => if owner = 0 then [(2,.var 4)] else if owner = 1 then [(3,.var 2)] else [(4,.var 3)]

def fresh : List (Entry Nat) := [(2,.bottom)]
def after : State Nat Nat := rebase triangle 0 fresh

theorem before_checks : triangle.owners.all (GeneralPresenceUsedTable245.check triangle) = true := by decide

theorem before_external : ExternalState triangle := by
 intro owner member
 simp only [triangle,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl <;> simp [triangle,External,CrossRead,Avoid,GeneralPresenceSubstitutionSupport244.typeSources]

theorem before_coherent : CoherentState triangle := by
 intro owner member
 simp only [triangle,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl <;> simp [triangle,Coherent]

theorem before_disjoint : DisjointState triangle := by
 intro first firstMem last lastMem different
 simp only [triangle,List.mem_cons,List.not_mem_nil,or_false] at firstMem lastMem
 rcases firstMem with rfl | rfl | rfl <;>
 rcases lastMem with rfl | rfl | rfl <;> first | contradiction | simp [triangle,DisjointTargets]

theorem fresh_external : External fresh := by simp [fresh,External,CrossRead,Avoid,GeneralPresenceSubstitutionSupport244.typeSources]

theorem fresh_within : TargetsWithin fresh (triangle.entries 0) := by
 intro entry member
 simp only [fresh,List.mem_singleton] at member
 subst entry
 exact ⟨(2,.var 4),by simp [triangle],rfl⟩

theorem after_external : ExternalState after := by
 exact GeneralPresenceUsedTable245.checked_external triangle 0 fresh (by decide) fresh_external

theorem after_owner_one : after.entries 1 = [(3,.var 4)] := rfl

theorem after_owner_two : after.entries 2 = [(4,.var 3)] := rfl

theorem next_check_fails : GeneralPresenceUsedTable245.check after 1 = false := by decide

/-- The sufficient rank certificate correctly excludes this cyclic table. -/
theorem no_rank (rank : Nat → Nat) : ¬ RankedState rank triangle := by
 intro ranked
 have a : rank 4 < rank 2 := ranked 0 (by simp [triangle]) (2,.var 4) (by simp [triangle]) 4 (by simp [GeneralPresenceSubstitutionSupport244.typeSources])
 have b : rank 2 < rank 3 := ranked 1 (by simp [triangle]) (3,.var 2) (by simp [triangle]) 2 (by simp [GeneralPresenceSubstitutionSupport244.typeSources])
 have c : rank 3 < rank 4 := ranked 2 (by simp [triangle]) (4,.var 3) (by simp [triangle]) 3 (by simp [GeneralPresenceSubstitutionSupport244.typeSources])
 exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_trans a b) c)
end Yulang.GeneralPresenceCheckClosureLimit245
