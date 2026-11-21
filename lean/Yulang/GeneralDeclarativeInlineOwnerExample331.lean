import Yulang.GeneralDeclarativeInlineSingleOwner331
import Yulang.GeneralDeclarativeInlineTwoOwners331
import Yulang.GeneralDeclarativeInlinePending331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineOwnerExample331
open GeneralDeclarativeInlineTwoOwners331 (aliasRow recordRow table payload terminal pattern uses model ordinary_satisfies)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_completed backed_iff)
open GeneralDeclarativeLowerKnown321 (Knows)
open GeneralDeclarativeInlineSingleOwner331 (Native only certify exact_backing expansion_after_owner)
open GeneralDeclarativeInlineGround331 (sourcesOnly)
open GeneralDeclarativeInlinePending331 (no_source_only not_from_unknown)
open GeneralDeclarativeInlineLineage331 (carries)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineMaterial331 (named ordinary protect)
open GeneralDeclarativeInlineAllocation331 (jobs)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeGrowth327 (facts)
open GeneralDeclarativeNewNames321 (old_plus_extra)

abbrev keep := [5,6]
abbrev stage := named table (point 0) keep uses
abbrev childRow : Equation := ⟨7,payload⟩

def original (done : Nat → Prop) : Supported table done :=
  ⟨fun e o => e ∈ [aliasRow,recordRow] ∧ o = .output 22,fun h => h.1⟩

theorem stored {done : Nat → Prop} (row : Equation) (old : row ∈ [aliasRow,recordRow]) :
    row ∈ (restriction (only (original done) 22)).equations :=
  from_completed _ ⟨old,rfl⟩ rfl

theorem raw_view (done : Nat → Prop) :
    Read (restriction (only (original done) 22)) .actual (.variable 0) pattern uses :=
  .record (raw := [(7,payload)]) (terminal := terminal) (keys := [7]) (selected := [(7,payload)])
    (.name (.inline (.forward (stored aliasRow List.mem_cons_self)) .width
      (stored recordRow (List.mem_cons_of_mem _ List.mem_cons_self))))
    (by decide) (by decide) rfl (.cons .capture .nil) .binder .capture

theorem exact_path (done : Nat → Prop) :
    Native (original done) 22 (point 0) keep uses childRow := by
  refine ⟨List.mem_cons_self,pattern,raw_view done,?_⟩
  intro synthetic
  have path := carries synthetic ⟨0,.actual,payload⟩ List.mem_cons_self
  have empty := no_source_only (p := original done) (fun row h => by cases h.2)
  cases not_from_unknown empty path 0 rfl

theorem literals_staged : ordinary table (point 0) keep uses ⊆ stage.equations :=
  fun _ used => List.mem_append_right _ used

def current (done : Nat → Prop) :=
  certify (original done) (facts table _) 22 (point 0) keep uses literals_staged

theorem real_gate (done : Nat → Prop) :
    childRow ∈ (restriction (current done)).equations ↔ done 22 := by
  constructor
  · intro stored
    rcases (exact_backing (facts table _) literals_staged 22).mp stored with old|new
    · obtain ⟨o,proof,_⟩ := (backed_iff _ _).mp old
      rcases List.mem_cons.mp proof.1 with h|rest
      · cases congrArg Equation.left h
      · cases congrArg Equation.left (List.mem_singleton.mp rest)
    · exact new.2
  · intro yes
    exact (exact_backing (facts table _) literals_staged 22).mpr (.inr ⟨exact_path done,yes⟩)

theorem child_after (done : Nat → Prop) (whenDone : done 22) :
    Knows (restriction (current done)) 7 (.primitive .pair 2) :=
  expansion_after_owner (facts table _) literals_staged (exact_path done) whenDone rfl

theorem ordinary_unchanged_by_phase : ∃ m, Models stage m :=
  ⟨_,(old_plus_extra table (protect (point 0) keep uses) (jobs uses) model ordinary_satisfies).1⟩

end Yulang.GeneralDeclarativeInlineOwnerExample331
