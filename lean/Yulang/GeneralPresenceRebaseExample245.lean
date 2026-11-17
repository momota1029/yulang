import Yulang.GeneralPresenceRebasePlan245
namespace Yulang.GeneralPresenceRebaseExample245
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244 GeneralPresenceOwnerTable244
open GeneralPresenceOwnerOwnership244 GeneralPresenceRebasePlan245

def initial : State Nat Nat where
 base := [.tyLe (.var 3) (.pair (.var 0) (.var 1))]
 owners := [0,1]
 entries := fun owner => if owner = 0 then [(2,.var 0)] else [(3,.pair (.var 2) (.var 1))]

def sharedNames (name : Nat) : Prop := name = 0 ∨ name = 1

def first : Edit Nat Nat := ⟨0,[(2,.var 1)]⟩
def second : Edit Nat Nat := ⟨1,[(3,.top)]⟩
def middle : State Nat Nat := rebase initial first.owner first.fresh

theorem first_safe : Safe sharedNames initial first := by
 constructor
 · simp [first,initial]
 · intro other member different
   have diff : other ≠ 0 := different
   have same : other = 1 := by simpa [initial,diff] using member
   subst other
   simp [initial,first,DisjointTargets]
 · simp [initial,first,External,CrossRead,Avoid,GeneralPresenceSubstitutionSupport244.typeSources]
 · simp [initial,first,Coherent]
 · simp [first,External,CrossRead,Avoid,GeneralPresenceSubstitutionSupport244.typeSources]
 · simp [first,Coherent]
 · intro entry member
   simp only [first,List.mem_singleton] at member
   subst entry
   exact ⟨(2,.var 0),by simp [initial,first],rfl⟩
 · intro name shared entry member
   have same : entry = (2,.var 0) := by simpa [initial,first] using member
   subst entry
   rcases shared with rfl | rfl <;> decide

theorem middle_entries : middle.entries 1 = [(3,.pair (.var 0) (.var 1))] := rfl

theorem second_safe : Safe sharedNames middle second := by
 constructor
 · simp [middle,rebase,initial,second]
 · intro other member different
   have diff : other ≠ 1 := different
   have same : other = 0 := by simpa [middle,rebase,initial,diff] using member
   subst other
   simp [middle,first,second,rebase,initial,transform,substitution,lookup,TyTerm.subst,DisjointTargets]
 · rw [show second.owner = 1 from rfl,middle_entries]
   simp [External,CrossRead,Avoid,GeneralPresenceSubstitutionSupport244.typeSources]
 · rw [show second.owner = 1 from rfl,middle_entries]
   simp [Coherent]
 · simp [second,External,CrossRead,Avoid,GeneralPresenceSubstitutionSupport244.typeSources]
 · simp [second,Coherent]
 · intro entry member
   simp only [second,List.mem_singleton] at member
   subst entry
   exact ⟨(3,.pair (.var 0) (.var 1)),by rw [show second.owner = 1 from rfl,middle_entries]; simp,rfl⟩
 · intro name shared entry member
   rw [show second.owner = 1 from rfl,middle_entries] at member
   have same : entry = (3,.pair (.var 0) (.var 1)) := by simpa using member
   subst entry
   rcases shared with rfl | rfl <;> decide

theorem safe_plan : SafePlan sharedNames initial [first,second] :=
 .cons initial first [second] first_safe (.cons middle second [] second_safe (.nil _))

theorem result_base : (run initial [first,second]).base =
 [.tyLe (.pair (.var 0) (.var 1)) (.pair (.var 0) (.var 1))] := rfl

theorem result_zero : (run initial [first,second]).entries 0 = [(2,.var 1)] := rfl

theorem result_one : (run initial [first,second]).entries 1 = [(3,.top)] := rfl

/-- Arbitrary public value and row assignments are preserved by this checked
plan, including when its private definitions change meaning. -/
theorem concrete_public_exact (boundary : Nat → Comp CommonNominalFullCarrier.model) :
 Projected CommonNominalFullCarrier.model sharedNames boundary initial ↔
 Projected CommonNominalFullCarrier.model sharedNames boundary (run initial [first,second]) :=
 common_plan_exact sharedNames boundary initial [first,second] safe_plan
end Yulang.GeneralPresenceRebaseExample245
