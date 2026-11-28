import Yulang.GeneralDeclarativeI65I74BoundedCandidateGeometry486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open ObservationAlternatives473 (Positions graphOf oldPosition)
open QuotientObservation471 (ReturnsUpToEquality)
open LiteralVisits473 (GuardedObservationInput Checkpoint readCheck independent_checkpoint_reifies_the_exact_site_and_sign)

/-- Logical finite evidence only. Existence does not compute unsupported
positions or supply an executable evidence producer. -/
theorem every_original_finite_position_table_has_a_complete_optional_checked_palette486
    {n : Nat} (s : GeneralDeclarativeI65.State) (pos : Positions n) (rel : List (Fin n × Fin n)) :
    ∃ finite : Vector (Option (Checkpoint n)) n,
      CompletePalette486 s pos rel (fun i => finite.get i) := by
  classical
  have derivation (i : Fin n) (guard : GuardedObservationInput s pos rel i) :
      ∃ ck : Checkpoint n, ck.which = i ∧
      ∃ bit, readCheck s pos rel (oldPosition pos i) ck = some bit := by
    by_cases cycle : ReturnsUpToEquality (graphOf s pos) i
    · obtain ⟨wire,atPoint,result⟩ :=
        independent_checkpoint_reifies_the_exact_site_and_sign guard true (by simp [cycle])
      exact ⟨wire,atPoint,true,result⟩
    · obtain ⟨wire,atPoint,result⟩ :=
        independent_checkpoint_reifies_the_exact_site_and_sign guard false (by simp [cycle])
      exact ⟨wire,atPoint,false,result⟩
  have allSlots (i : Fin n) : ∃ stored : Option (Checkpoint n),
      GuardedObservationInput s pos rel i →
      ∃ ck, stored = some ck ∧ ck.which = i ∧
        ∃ bit, readCheck s pos rel (oldPosition pos i) ck = some bit := by
    by_cases guard : GuardedObservationInput s pos rel i
    · obtain ⟨ck,loc,bits⟩ := derivation i guard
      exact ⟨some ck,fun _ => ⟨ck,rfl,loc,bits⟩⟩
    · exact ⟨none,fun impossible => False.elim (guard impossible)⟩
  let lookup (i : Fin n) : Option (Checkpoint n) := Classical.choose (allSlots i)
  refine ⟨Vector.ofFn lookup,?_⟩
  have exact : (fun i => (Vector.ofFn lookup).get i) = lookup := by
    funext i
    change (Vector.ofFn lookup)[i.val]'i.isLt = lookup i
    simp only [Vector.getElem_ofFn]
  rw [exact]
  intro i guard
  obtain ⟨ck,picked,loc,bit,ran⟩ := Classical.choose_spec (allSlots i) guard
  have saved : lookup i = some ck := picked
  exact ⟨bit,by simp [oldObservedSign486,saved,loc,ran,Option.bind]⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
