import Yulang.GeneralDeclarativeVersionedPaired342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeVersionedRootGuard342
open GeneralWherePhysicalCurrentPick319 (sourceRoot)
open GeneralWherePhysicalCommit319 (final)
open GeneralWhereVersionInstall317 (Models)
open GeneralDeclarativeVersionedRootRead342 (publicRow raw_root)
open GeneralDeclarativeVersionedTree342 (root_requests)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported Backed backed_iff restriction)
open GeneralDeclarativeLowerKnown321 (knows_row)
open GeneralDeclarativeTaggedElection340 (Ready)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralStoppedOrdinarySite335 (demand)
open GeneralNominalCommonBridge (Assignment)

abbrev observedRoot : State := ⟨⟨[],[]⟩,[publicRow]⟩
noncomputable abbrev actualDemand := GeneralDeclarativeStoppedPaired341.activeDemand final.mixed sourceRoot

theorem original_arguments :
    actualDemand.arguments = [⟨0,0,0⟩] := rfl

theorem original_targets :
    actualDemand.outputs = [⟨0,4⟩] := root_requests

theorem every_model (m : Assignment) (fit : Models final m) :
    GeneralDeclarativeHead320.Models observedRoot m := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro _ h
    cases h
  · intro _ h
    cases h
  · intro row one
    cases List.mem_singleton.mp one
    exact raw_root m fit

/-- On the exact single-row ordinary view of the current physical
root, readiness is equivalent to independent support of the actual
nominal row. Its truth in every model is not itself support. This only
characterizes this projection slice: a fuller view may supply evidence
along a different supported path. -/
theorem ready_iff {done : Nat → Prop} (p : Supported observedRoot done) :
    Ready p actualDemand ↔ Backed p publicRow := by
  constructor
  · intro ready
    obtain ready | ready := ready ⟨0,0,0⟩ (original_arguments.symm ▸ List.mem_singleton_self _)
    · obtain ⟨_,row,present,_,_⟩ := ready
      obtain ⟨o,h,available⟩ := (backed_iff p row).mp present
      exact List.mem_singleton.mp (p.ordinary h) ▸ show Backed p row from ⟨o,h,available⟩
    · obtain ⟨_,_,_,⟨name,_,present⟩,_⟩ := ready
      obtain ⟨o,h,available⟩ := (backed_iff p _).mp present
      exact List.mem_singleton.mp (p.ordinary h) ▸ show Backed p _ from ⟨o,h,available⟩
  · intro supported a present
    rw [original_arguments] at present
    cases List.mem_singleton.mp present
    exact .inl ⟨_,knows_row ((backed_iff p publicRow).mpr supported) rfl⟩

theorem selected_needs_origin {done : Nat → Prop} (p : Supported observedRoot done)
    (success : Rule p sidecar r i waiting actualDemand (.selected impl kids)) :
    Backed p publicRow := by
  cases success with
  | whole selected => exact (ready_iff p).mp selected.elected.ready

end Yulang.GeneralDeclarativeVersionedRootGuard342
