import Yulang.GeneralMixedCompoundTailFan307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
namespace Yulang.GeneralMixedCompoundHalfView307
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundBase239 (extendedBase extendedView lo hi source viewHeads)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot extendedContext)
open GeneralCanonicalObservations (Observation Recorded)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known)
open GeneralNormalizedObservation (Head)

abbrev heads (i : Fin 7) : Head GeneralDictionaryCompoundBase239.viewShapes 7 :=
  if i = 6 then .deferred .unresolved else viewHeads i

abbrev view : GeneralNormalizedObservation.Snapshot extendedBase where
  kinds := extendedView.kinds
  shapes := extendedView.shapes
  shapes_injective := extendedView.shapes_injective
  canonical := extendedView.canonical
  heads := heads
  checked := by
    intro i term saved
    by_cases cutoff : i = 6
    · simp [heads,cutoff,Head.term,GeneralNormalizedObservation.Deferred.term] at saved
    · exact extendedView.checked i term (by simpa only [heads,ite_eq_right cutoff] using saved)

noncomputable abbrev snap : GeneralNominalState.State where
  base := extendedSnapshot.base
  view := view
  constructors := extendedSnapshot.constructors
  nominals := extendedSnapshot.nominals
  catalogue := extendedSnapshot.catalogue
  bodies_opaque := by
    intro i d valid
    have opaqueHead := extendedSnapshot.bodies_opaque i d valid
    by_cases cutoff : i = 6
    · simp [view,heads,cutoff]
    · simpa only [view,heads,ite_eq_right cutoff] using opaqueHead
  allocated := extendedSnapshot.allocated
  reserved := extendedSnapshot.reserved
  ordinary := extendedSnapshot.ordinary
  seed := extendedSnapshot.seed

noncomputable abbrev context : GeneralNominalCandidates.Context :=
  ⟨snap,extendedContext.interpretation⟩

noncomputable abbrev half := refresh point context

theorem observed_back (fact : Observation) (found : Recorded snap fact) :
    Recorded extendedSnapshot fact := by
  cases found with
  | scalar i n saved =>
    by_cases cutoff : i = 6
    · simp [heads,cutoff] at saved
    · exact Recorded.scalar (snapshot := extendedSnapshot) i n
        (by simpa only [heads,ite_eq_right cutoff] using saved)
  | structural i k children saved =>
    by_cases cutoff : i = 6
    · simp [heads,cutoff] at saved
    · exact Recorded.structural (snapshot := extendedSnapshot) i k children
        (by simpa only [heads,ite_eq_right cutoff] using saved)
  | nominal i d saved => exact Recorded.nominal (snapshot := extendedSnapshot) i d saved

theorem same_slot {n : Nat} (found : source i = n) (notHi : n ≠ hi) : i ≠ 6 := by
  intro eq; subst i
  exact notHi found.symm

theorem old_known {n : Nat} (found : Known extendedSnapshot n) (notHi : n ≠ hi) :
    Known snap n := by
  obtain ⟨i,eq,head|nominal⟩ := found
  · refine ⟨i,eq,Or.inl ?_⟩
    change (heads i).node ≠ .unresolved
    rwa [show heads i = viewHeads i from ite_eq_right (same_slot eq notHi)]
  · exact ⟨i,eq,Or.inr nominal⟩

theorem forward_known {n : Nat} (found : Known snap n) : Known extendedSnapshot n := by
  obtain ⟨i,eq,head|nominal⟩ := found
  · refine ⟨i,eq,Or.inl ?_⟩
    change (heads i).node ≠ .unresolved at head
    by_cases cutoff : i = 6
    · exact False.elim (head (by rw [show heads i = .deferred .unresolved from ite_eq_left cutoff]; rfl))
    · rwa [show heads i = viewHeads i from ite_eq_right cutoff] at head
  · exact ⟨i,eq,Or.inr nominal⟩

theorem lo_known : Known snap lo :=
  old_known GeneralDictionaryCompoundRefreshStep239.lower_known (by decide +kernel)

theorem hi_unknown : ¬ Known snap hi := by
  rintro ⟨i,eq,h|⟨d,recorded⟩⟩
  · have cut : i = (6 : Fin 7) := GeneralDictionaryCompoundBase239.source_injective eq
    subst i; exact h rfl
  · have cut : i = (6 : Fin 7) := GeneralDictionaryCompoundBase239.source_injective eq
    subst i; cases recorded

theorem hi_known : Known extendedSnapshot hi := ⟨6,rfl,Or.inl (by decide +kernel)⟩

end Yulang.GeneralMixedCompoundHalfView307
