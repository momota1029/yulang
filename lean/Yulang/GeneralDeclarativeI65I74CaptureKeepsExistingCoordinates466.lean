import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466WrittenBinderCoordinates
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeI65 (Origin Alias)
open GeneralDeclarativeI65.I72.PreparedDeclarations463
open GeneralDeclarativeI65.I72.Checker408 (Problem)
open GeneralDeclarativeInlineMaterial331 (ordinary protect old_names_protected)
open GeneralDeclarativeFootprint321 (stateNames)
open OrdinaryOccurrenceStamp466

/-- Existing physical and logical address columns only. This is not a
full reachability or new allocation policy, and does not issue any row. -/
def existingNativeCoordinates (s : GeneralDeclarativeI65.State) : List Nat :=
  (s.origins.map Origin.slot) ++ s.routes.flatMap (fun r => [r.logical,r.physical])

theorem an_actual_legacy_allocation_respects_every_explicit_kept_name
    {s : State} {done : Nat → Prop} {old : Supported s done}
    {idx : Sources (restriction old)} {c interp a kept p job r}
    (executed : ExactOldCaptureExecution idx c interp a kept p job r) :
    ∀ name ∈ stateNames s ++ kept, name ≠ r.target := by
  obtain ⟨code,uses,_,_,_,allocated,_,_⟩ := executed
  obtain ⟨_,_,atRaw⟩ := successful_ordinal_reads_original_capture_and_allocated_row
    s a kept uses allocated
  have actual := List.mem_of_getElem? atRaw
  intro name reserved same
  have booked : name ∈ stateNames s ++ protect a kept uses := by
    rcases List.mem_append.mp reserved with old|guarded
    · exact List.mem_append_left _ old
    · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ guarded))
  exact old_names_protected actual booked same.symm

theorem an_actual_ready_capture_avoids_all_supplied_placement_addresses
    (p : Problem) (tab : CheckedTable p.state.core.current)
    {done : Nat → Prop} {old : Supported (C466WrittenBinderCoordinates.ordinary p) done}
    (idx : Sources (restriction old)) (addr : HeadAddress) (keep : List Nat) (job : Nat)
    (r : CheckedCaptureHead p tab)
    (ok : readCaptureFromReadyHead p tab idx addr keep job = some r)
    (specified : existingNativeCoordinates p.state.core ⊆ keep) :
    (∀ o ∈ p.state.core.origins, o.slot ≠ r.allocated.target) ∧
    ∀ route ∈ p.state.core.routes,
      route.logical ≠ r.allocated.target ∧ route.physical ≠ r.allocated.target := by
  have info := (previous_compiler_receipt_requires_the_actual_request_and_prechecked_head ..).mp ok
  have kept := an_actual_legacy_allocation_respects_every_explicit_kept_name info.2.2
  constructor
  · intro o original
    exact kept o.slot (List.mem_append_right _ (specified
      (List.mem_append_left _ (List.mem_map.mpr ⟨o,original,rfl⟩))))
  · intro route stored
    have access (name) (one : name ∈ [route.logical,route.physical]) :
        name ≠ r.allocated.target :=
      kept name (List.mem_append_right _ (specified
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨route,stored,one⟩))))
    exact ⟨access _ List.mem_cons_self,access _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

end Yulang.C466WrittenBinderCoordinates
