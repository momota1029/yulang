import Yulang.GeneralDeclarativeWitnessOrigins350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Origin Backed restriction)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach support visible_iff origin visible)

def onlyAuthoredLabel478 (row : Equation) : Table := ⟨[row],[],[]⟩
def onlyPendingLabel478 (row : Equation) (owner : Nat) : Table := ⟨[],[(row,owner)],[]⟩

theorem existing_raw_membership_allows_both_supplied_provenance_tables478
    (s : State) (row : Equation) (owner : Nat) (oldRow : row ∈ s.equations) :
    ∃ (source : Attached s (onlyAuthoredLabel478 row)) (pending : Attached s (onlyPendingLabel478 row owner)),
      attach s (onlyAuthoredLabel478 row) = some source ∧
      attach s (onlyPendingLabel478 row owner) = some pending ∧
      row ∈ (restriction (support source)).equations ∧
      row ∉ (restriction (support pending)).equations := by
  have ok : decide (row ∈ s.equations) = true := decide_eq_true oldRow
  let src : Attached s (onlyAuthoredLabel478 row) := by
    constructor
    · intro e member
      change e ∈ [row] at member
      obtain rfl := List.mem_singleton.mp member
      exact oldRow
    · intro _ absent
      cases absent
  let waiting : Attached s (onlyPendingLabel478 row owner) := by
    constructor
    · intro _ absent
      cases absent
    · intro e member
      change e ∈ [(row,owner)] at member
      obtain rfl := List.mem_singleton.mp member
      exact oldRow
  refine ⟨src,waiting,?_,?_,?_,?_⟩
  · simp [attach,onlyAuthoredLabel478,ok,src]
  · simp [attach,onlyPendingLabel478,ok,waiting]
  · exact (visible_iff src row).mpr (by simp [visible,onlyAuthoredLabel478])
  · intro bad
    have seen := (visible_iff waiting row).mp bad
    simp [visible,onlyPendingLabel478] at seen

/-- Membership checks do not have enough data to authenticate which of
two literal input-event interpretations is real. This theorem says only
that the old attachment interface regards both as consistent raw subsets. -/
theorem no_state_and_row_only_bit_recovers_both_backing_labels478
    (decoder : State → Equation → Bool)
    (s : State) (row : Equation) (owner : Nat)
    (oldRow : row ∈ s.equations)
    (always : ∀ (t : Table) (valid : Attached s t), attach s t = some valid →
      (decoder s row = true ↔ row ∈ (restriction (support valid)).equations)) :
    False := by
  obtain ⟨source,pending,runsSource,runsPending,known,unknown⟩ :=
    existing_raw_membership_allows_both_supplied_provenance_tables478 s row owner oldRow
  exact unknown ((always _ _ runsPending).mp ((always _ _ runsSource).mpr known))


end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
