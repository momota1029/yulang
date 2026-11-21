import Yulang.GeneralDeclarativeLowerKnown321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSupportExample321
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeOrigins321 (Origin Supported restriction from_source from_completed pending_only ordinary_despite_pending)
open GeneralDeclarativeLowerKnown321 (Tag Ready Delayed Knows knows_row)

def first : Equation := ⟨10,.primitive (.scalar .int) []⟩
def second : Equation := ⟨20,.primitive (.scalar .int) []⟩
def stableUpper : Equation := ⟨22,.primitive (.scalar .int) []⟩
def state : State := ⟨⟨[],[]⟩,[first,second,stableUpper]⟩
def demand : Demand := ⟨0,[⟨10,11,12⟩,⟨20,21,22⟩],[]⟩

def provenance (sourceAlso : Prop) (eqn : Equation) (origin : Origin) : Prop :=
  (eqn = first ∧ origin = .source) ∨ (eqn = stableUpper ∧ origin = .source) ∨
  (eqn = second ∧ (origin = .output 7 ∨ sourceAlso ∧ origin = .source))

def origins (sourceAlso : Prop) (completed : Nat → Prop) : Supported state completed :=
  ⟨provenance sourceAlso,by
    intro row _ reason
    rcases reason with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> simp [state]⟩

theorem second_ordinary (completed : Nat → Prop) : Entails state second :=
  ordinary_despite_pending (origins False completed) (.inr (.inr ⟨rfl,.inl rfl⟩))

theorem alternate_origins (completed : Nat → Prop) (effective : completed 7 ∨ True) :
    Ready (origins True completed) demand := by
  intro arg h
  change arg ∈ demand.arguments at h
  simp only [demand,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl
  · exact ⟨.primitive (.scalar .int) 0, knows_row
      (from_source (origins True completed) (.inl ⟨rfl,rfl⟩)) rfl⟩
  · refine ⟨.primitive (.scalar .int) 0,knows_row (code := second.right) ?_ rfl⟩
    rcases effective with settled|independent
    · exact from_completed (origins True completed) (.inr (.inr ⟨rfl,.inl rfl⟩)) settled
    · exact from_source (origins True completed) (.inr (.inr ⟨rfl,.inr ⟨independent,rfl⟩⟩))

theorem completed_restarts (completed : Nat → Prop) (settled : completed 7) :
    Ready (origins False completed) demand := by
  intro arg h
  simp only [demand,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl
  · exact ⟨.primitive (.scalar .int) 0,knows_row
      (from_source (origins False completed) (.inl ⟨rfl,rfl⟩)) rfl⟩
  · exact ⟨.primitive (.scalar .int) 0,knows_row
      (from_completed (origins False completed) (.inr (.inr ⟨rfl,.inl rfl⟩)) settled) rfl⟩


open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeBounds319 (Bound)

theorem only_reflexive_bound (completed : Nat → Prop) (sourceAlso : Prop)
    (bound : Bound (restriction (origins sourceAlso completed)).normal a b) : a = b := by
  induction bound with
  | interval present => cases present
  | constraint present => cases present
  | refl => rfl
  | trans _ _ i j => exact i.trans j

theorem no_variable_equations {completed : Nat → Prop} {backup : Prop}
    (present : (⟨a,.variable b⟩ : Equation) ∈ (restriction (origins backup completed)).equations) :
    False := by
  have found := (origins backup completed).ordinary
    ((GeneralDeclarativeOrigins321.backed_iff (origins backup completed) _).mp present).choose_spec.1
  change (⟨a,.variable b⟩ : Equation) ∈ [first,second,stableUpper] at found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with bad|bad|bad <;> cases bad

theorem only_reflexive_alias (completed : Nat → Prop) (sourceAlso : Prop)
    (link : Alias (restriction (origins sourceAlso completed)) a b) : a = b := by
  induction link with
  | bounds lo _ => exact only_reflexive_bound completed sourceAlso lo
  | forward h => exact False.elim (no_variable_equations h)
  | backward h => exact False.elim (no_variable_equations h)
  | trans _ _ i j => exact i.trans j

theorem unfinished_blocks_second (completed : Nat → Prop) (pending : ¬completed 7) :
    Delayed (origins False completed) demand := by
  refine ⟨⟨20,21,22⟩,List.mem_cons_of_mem _ List.mem_cons_self,?_⟩
  intro tag known
  obtain ⟨row,found,alias,_⟩ := known
  have left : 20 = row.left := only_reflexive_alias completed False alias
  obtain ⟨origin,originates,ready⟩ :=
    (GeneralDeclarativeOrigins321.backed_iff (origins False completed) row).mp found
  rcases originates with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,how⟩
  · cases left
  · cases left
  · rcases how with rfl|⟨impossible,_⟩
    · cases ready with
      | completed finished => exact pending finished
    · exact impossible
end Yulang.GeneralDeclarativeSupportExample321
