import Yulang.GeneralDeferredLadderControlBridge304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderControlCover304
open GeneralDeferredLadderControl304 (Control view)
open GeneralDeferredLadderControlBridge304 (executable_exact)
open GeneralDeferredLadderClosed304 (classification)
open GeneralDeferredLadderExact302 (RawStep)
open GeneralDeferredLadderRelay304 (refPhase refState initial)
open GeneralDeferredLadderControl304 (view_ref view_relay)
open GeneralObservedLadderBudget301 (Counted)
open GeneralObservedLadderRefresh301 (before)
open GeneralNominalVersionedJournal232 (State)
open GeneralDeclarationExamples (roles)

def allStates (n : Nat) : List Control :=
  ((List.range (n+2)).map fun k => ⟨k,false⟩) ++ ((List.range (n+2)).map fun k => ⟨k,true⟩)

theorem all_count (n : Nat) : (allStates n).length = 2*(n+2) := by
  simp [allStates]
  omega

theorem all_nodup (n : Nat) : (allStates n).Nodup := by
  have one (tag : Bool) :
      ((List.range (n+2)).map (fun k => (⟨k,tag⟩ : Control))).Nodup :=
    List.Pairwise.map _ (fun i j different same => different (congrArg Control.index same)) List.nodup_range
  apply List.nodup_append.mpr
  refine ⟨one false,one true,?_⟩
  intro a ma b mb same
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ma
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp mb
  cases congrArg Control.seen same

theorem all_exact (n : Nat) (c : Control) : c ∈ allStates n ↔ c.index ≤ n+1 := by
  constructor
  · intro listed
    unfold allStates at listed
    rcases List.mem_append.mp listed with h|h <;>
      obtain ⟨k,hit,rfl⟩ := List.mem_map.mp h <;>
      change k ≤ n+1 <;>
      have high := List.mem_range.mp hit <;> omega
  · obtain ⟨k,tag⟩ := c
    intro high
    have hit : k ∈ List.range (n+2) := List.mem_range.mpr (by simpa using Nat.lt_succ_of_le high)
    cases tag
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨k,hit,rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨k,hit,rfl⟩)

theorem every_control_realized (n : Nat) (c : Control) :
    c ∈ allStates n ↔ ∃ (length : Nat) (s : State roles), Counted length (before n) s ∧ view n s = c := by
  constructor
  · intro listed
    obtain ⟨k,tag⟩ := c
    have cap : k ≤ n+1 := (all_exact ..).mp listed
    have nav := GeneralDeferredLadderOutcomes302.counted_before
      (GeneralDeferredLadderTrace302.prefix_exists n k cap)
    cases tag
    · exact ⟨k,refState n k cap,nav,view_ref n k cap⟩
    · let p := refPhase n k cap
      exact ⟨k+1,_,.tail nav (GeneralDeferredLadderRefresh302.actual p),
        view_relay (initial n k cap (GeneralDeferredLadderRefresh302.promotedContext p)
          (GeneralDeferredLadderRefresh302.certificate p) (GeneralDeferredLadderRefresh302.strict p))⟩
  · rintro ⟨length,s,path,rfl⟩
    apply (all_exact ..).mpr
    rcases classification n path with ⟨cap,rfl⟩ | ⟨_,cap,⟨rel⟩,_⟩
    · rw [view_ref]
      exact cap
    · rw [view_relay rel]
      exact cap

/-- Two distinct raw states with the same control view have the same
set of control successors, on all reachable representatives. -/
theorem quotient_successors (n : Nat) {i j : Nat} {s t : State roles}
    (a : Counted i (before n) s) (b : Counted j (before n) t)
    (same : view n s = view n t) (c : Control) :
    (∃ x, RawStep s x ∧ view n x = c) ↔ (∃ y, RawStep t y ∧ view n y = c) := by
  rw [← executable_exact n a c,← executable_exact n b c,same]

end Yulang.GeneralDeferredLadderControlCover304
