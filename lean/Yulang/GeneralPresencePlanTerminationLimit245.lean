import Yulang.GeneralPresenceRebasePlan245
/-! Safe alone is not a progress rule. This cycle belongs to the permissive
representation interface below, not to actual source/solver transitions.
No language nontermination or operational reachability claim is made. -/
namespace Yulang.GeneralPresencePlanTerminationLimit245
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244 GeneralPresenceOwnerTable244
open GeneralPresenceOwnerOwnership244 GeneralPresenceRebasePlan245

def single (term : TyTerm Nat) : State Nat Nat where
 base := []
 owners := [0]
 entries := fun owner => if owner = 0 then [(2,term)] else []

def sharedNames (name : Nat) : Prop := name ≠ 2

def replace (term : TyTerm Nat) : Edit Nat Nat := ⟨0,[(2,term)]⟩

theorem single_rebase (old fresh : TyTerm Nat) :
 rebase (single old) 0 [(2,fresh)] = single fresh := by
 unfold rebase single
 congr 1
 funext other
 by_cases same : other = 0 <;> simp [same,transform]

theorem safe_replace (old fresh : TyTerm Nat)
 (oldClosed : GeneralPresenceSubstitutionSupport244.typeSources old = [])
 (freshClosed : GeneralPresenceSubstitutionSupport244.typeSources fresh = []) :
 Safe sharedNames (single old) (replace fresh) := by
 constructor
 · simp [single,replace]
 · intro other member different
   have same : other = 0 := by simpa [single] using member
   exact False.elim (different same)
 · simp [single,replace,External,CrossRead,Avoid,oldClosed]
 · simp [single,replace,Coherent]
 · simp [replace,External,CrossRead,Avoid,freshClosed]
 · simp [replace,Coherent]
 · intro entry member
   have same : entry = (2,fresh) := by simpa [replace] using member
   subst entry
   exact ⟨(2,old),by simp [single,replace],rfl⟩
 · intro name shared entry member
   have same : entry = (2,old) := by simpa [single,replace] using member
   subst entry
   exact Ne.symm shared

def Step (before after : State Nat Nat) : Prop :=
 ∃ edit, Safe sharedNames before edit ∧ after = rebase before edit.owner edit.fresh

theorem bottom_to_top : Step (single .bottom) (single .top) :=
 ⟨replace .top,safe_replace .bottom .top rfl rfl,(single_rebase .bottom .top).symm⟩

theorem top_to_bottom : Step (single .top) (single .bottom) :=
 ⟨replace .bottom,safe_replace .top .bottom rfl rfl,(single_rebase .top .bottom).symm⟩

/-- A scheduler must add genuine progress to this permissive certificate. -/
theorem safe_not_accessible : ¬ Acc (fun after before => Step before after) (single .bottom) := by
 have excludes (state : State Nat Nat) (access : Acc (fun after before => Step before after) state) :
   state = single .bottom ∨ state = single .top → False := by
   induction access with
   | intro state _ ih =>
     intro cases
     rcases cases with rfl | rfl
     · exact ih (single .top) bottom_to_top (Or.inr rfl)
     · exact ih (single .bottom) top_to_bottom (Or.inl rfl)
 intro access
 exact excludes _ access (Or.inl rfl)
def grow : Nat → TyTerm Nat
 | 0 => .bottom
 | n+1 => .pair (grow n) (grow n)

def pairDepth : TyTerm Nat → Nat
 | .pair first last => max (pairDepth first) (pairDepth last) + 1
 | _ => 0

theorem grow_closed (n : Nat) : GeneralPresenceSubstitutionSupport244.typeSources (grow n) = [] := by
 induction n <;> simp_all [grow,GeneralPresenceSubstitutionSupport244.typeSources]

theorem grow_depth (n : Nat) : pairDepth (grow n) = n := by
 induction n <;> simp_all [grow,pairDepth]

theorem grow_injective : Function.Injective grow := by
 intro first last equal
 have depths := congrArg pairDepth equal
 simpa only [grow_depth] using depths

theorem arbitrary_growth_safe (old next : Nat) :
 Safe sharedNames (single (grow old)) (replace (grow next)) :=
 safe_replace _ _ (grow_closed old) (grow_closed next)

/-- A single owner and a single unchanged private identity permit arbitrary
syntax depth under Safe. A finite payload argument needs additional facts. -/
theorem unbounded_private_depth (bound : Nat) :
 ∃ term, Safe sharedNames (single .bottom) (replace term) ∧ bound < pairDepth term := by
 exact ⟨grow (bound+1),safe_replace _ _ rfl (grow_closed _),by rw [grow_depth]; exact Nat.lt_succ_self bound⟩
end Yulang.GeneralPresencePlanTerminationLimit245
