import Yulang.GeneralDeferredLadderControl304

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralDeferredLadderControlBridge304
open GeneralDeferredLadderAdvance302 (phase_step)
open GeneralDeferredLadderExact302 (RawStep only_step)
open GeneralDeferredLadderRelay304 (Relay refPhase refState initial step_exists step_unique)
open GeneralDeferredLadderRelayAdvance304 (advance)
open GeneralDeferredLadderRelayCount304 (halted_at_index)
open GeneralDeferredLadderClosed304 (classification)
open GeneralDeferredLadderControl304
open GeneralObservedLadderBudget301 (Counted)
open GeneralObservedLadderRefresh301 (before)
open GeneralNominalVersionedJournal232 (State)
open GeneralDeclarationExamples (roles)

theorem projects (n : Nat) {length s t} (path : Counted length (before n) s)
    (next : RawStep s t) : Edge n (view n s) (view n t) := by
  rcases classification n path with ⟨cap,rfl⟩ | ⟨k,cap,⟨rel⟩,_⟩
  · rw [view_ref]
    rcases only_step n length cap t next with ⟨hi,rfl⟩ | ⟨target,cert,known,rfl⟩
    · rw [view_ref]
      exact .install false hi
    · rw [view_relay (initial n length cap target cert known)]
      exact .observe cap
  · rw [view_relay rel]
    by_cases hi : k ≤ n
    · have same := (step_unique rel hi t).mp next
      subst t
      rw [view_relay (advance rel hi)]
      exact .install true hi
    · exact False.elim (halted_at_index (by omega) rel t next)

theorem lifts (n : Nat) {length s} (path : Counted length (before n) s)
    {d : Control} (edge : Edge n (view n s) d) :
    ∃ t : State roles, RawStep s t ∧ view n t = d := by
  rcases classification n path with ⟨cap,rfl⟩ | ⟨k,cap,⟨rel⟩,_⟩
  · rw [view_ref] at edge
    cases edge with
    | install _ hi => exact ⟨_,phase_step n length hi,view_ref ..⟩
    | observe cap =>
      let p := refPhase n length cap
      exact ⟨_,GeneralDeferredLadderRefresh302.actual p,
        view_relay (initial n length cap (GeneralDeferredLadderRefresh302.promotedContext p)
          (GeneralDeferredLadderRefresh302.certificate p) (GeneralDeferredLadderRefresh302.strict p))⟩
  · rw [view_relay rel] at edge
    cases edge with
    | install _ hi => exact ⟨_,step_exists rel hi,view_relay (advance rel hi)⟩

/-- The finite list enumerates precisely the images of raw successors,
not the raw successors themselves. -/
theorem executable_exact (n : Nat) {length s} (path : Counted length (before n) s) (d : Control) :
    d ∈ successors n (view n s) ↔ ∃ t, RawStep s t ∧ view n t = d := by
  constructor
  · intro listed
    exact lifts n path ((successors_exact ..).mp listed)
  · rintro ⟨t,next,rfl⟩
    exact (successors_exact ..).mpr (projects n path next)

theorem executable_halt (n : Nat) {length s} (path : Counted length (before n) s) :
    successors n (view n s) = [] ↔ ∀ next, ¬ RawStep s next := by
  constructor
  · intro empty t next
    have listed := (executable_exact n path (view n t)).mpr ⟨t,next,rfl⟩
    rw [empty] at listed
    cases listed
  · intro halted
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d found
    obtain ⟨t,next,_⟩ := (executable_exact n path d).mp found
    exact halted t next

theorem rank_exact (n : Nat) {length s} (path : Counted length (before n) s) :
    length + remaining n (view n s) = n+2 := by
  rcases classification n path with ⟨cap,rfl⟩ | ⟨k,cap,⟨rel⟩,eq⟩
  · rw [view_ref]
    simp [remaining]
    omega
  · rw [view_relay rel]
    simp [remaining]
    omega

end Yulang.GeneralDeferredLadderControlBridge304
