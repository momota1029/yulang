import Yulang.GeneralDeclarativeAliasStatus327
import Yulang.GeneralDeclarativeRelationalCheck327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAliasChecker327
open GeneralDeclarativeAliasAuthority327
open GeneralDeclarativeAliasStatus327
open GeneralDeclarativeRelationalCheck327 (Flags Observes Verifies check)
open GeneralDeclarativeProjectedFrame326 (Generated)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeLowerKnown321 (Ready ready_iff_not_delayed)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open CommonRoleOutermostResolver (Frontier)

def observed (allowed : Bool) : Flags := ⟨allowed,false,fun _ => true,fun _ => false⟩

def emits (_ : Nat) (kids : List Demand) : Bool := kids.isEmpty

theorem exact_observation (done : Nat → Prop) (n : Nat)
    (status : allowed = true ↔ Ready (support done) (run n)) :
    Observes state reg interp (support done) (tests done) (run n) (observed allowed) := by
  refine ⟨status,?_,?_,?_⟩
  · exact ⟨(fun h => by cases h),fun rec => False.elim (acyclic done _ rec)⟩
  · intro d there _
    cases List.mem_singleton.mp there
    exact ⟨fun _ => probe n done,fun _ => rfl⟩
  · intro d there _
    cases List.mem_singleton.mp there
    exact ⟨(fun h => by cases h),fun no => False.elim (no (probe n done))⟩

theorem emits_exact (done : Nat → Prop) (n : Nat) (writtenHere : written n ∈ rows) :
    Verifies state reg interp (support done) (tests done) (run n)
      (Generated state reg interp (support done)) emits := by
  intro _ _ _ impl unique kids
  cases List.mem_singleton.mp unique.1.1.1
  unfold emits
  constructor
  · intro h
    cases kids with
    | nil => exact ⟨fun _ => GeneralDeclarativeExampleSource320.point n,place,source_frame n done writtenHere,rfl⟩
    | cons _ _ => cases h
  · rintro ⟨_,_,_,rfl⟩
    rfl

theorem checked_before : ∀ frontier,
    check reg b (observed false) emits frontier = true ↔ branch emptyDone b frontier := by
  intro frontier
  apply GeneralDeclarativeRelationalCheck327.at_exact checked
  · apply exact_observation
    exact ⟨(fun h => by cases h),fun ready => False.elim ((ready_iff_not_delayed _ _).mp ready not_before)⟩
  · exact emits_exact _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem checked_after : ∀ frontier,
    check reg b (observed true) emits frontier = true ↔ branch realDone b frontier := by
  intro frontier
  apply GeneralDeclarativeRelationalCheck327.at_exact checked
  · exact exact_observation _ _ ⟨fun _ => authorized_later,fun _ => rfl⟩
  · exact emits_exact _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

end Yulang.GeneralDeclarativeAliasChecker327
