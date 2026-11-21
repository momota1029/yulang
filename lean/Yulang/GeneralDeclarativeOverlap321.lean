import Yulang.GeneralDeclarativePriority321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOverlap321
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Origin Supported restriction pending_only from_source)
open GeneralDeclarativeLowerKnown321 (Ready Delayed knows_row)
open GeneralDeclarativeGraphRows321 (pending_nominal_self_cycle)
open GeneralDeclarativeK2Alias321 (cycle_in_alias_graph)
open GeneralDeclarativePriority321 (RootRecurs)

def self : Equation := ⟨0,.nominal 0 [.variable 0]⟩
def state : State := ⟨⟨[],[]⟩,[self]⟩
def input : Demand := ⟨1,[⟨0,0,0⟩],[]⟩

def support (independent : Prop) : Supported state (fun _ => False) :=
  ⟨fun row origin => row = self ∧ (origin = .output 1 ∨ independent ∧ origin = .source),
    fun h => h.1.symm ▸ List.mem_cons_self⟩

theorem recurrence_retained : RootRecurs state input := by
  refine ⟨⟨0,0,0⟩,List.mem_cons_self,cycle_in_alias_graph ?_⟩
  exact pending_nominal_self_cycle (support False) 1 ⟨rfl,.inl rfl⟩

theorem no_independent_head : Delayed (support False) input := by
  refine ⟨⟨0,0,0⟩,List.mem_cons_self,?_⟩
  intro tag known
  obtain ⟨row,found,_,_⟩ := known
  have raw := (support False).ordinary
    ((GeneralDeclarativeOrigins321.backed_iff _ _).mp found).choose_spec.1
  change row ∈ [self] at raw
  cases List.mem_singleton.mp raw
  apply pending_only (support False) self ?_ found
  intro o reason
  rcases reason.2 with h|⟨bad,_⟩
  · exact ⟨1,h,fun impossible => impossible⟩
  · exact False.elim bad

theorem independent_head : Ready (support True) input := by
  intro arg offered
  cases List.mem_singleton.mp offered
  exact ⟨_,knows_row (from_source (support True) (row := self) ⟨rfl,.inr ⟨trivial,rfl⟩⟩) rfl⟩

/-- Delayed expansion and a genuine root cycle in the ordinary graph can
coexist. The ordinary equation and its names are identical. -/
theorem overlap : Delayed (support False) input ∧ RootRecurs state input ∧ Ready (support True) input :=
  ⟨no_independent_head,recurrence_retained,independent_head⟩

end Yulang.GeneralDeclarativeOverlap321
