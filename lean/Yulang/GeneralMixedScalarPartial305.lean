import Yulang.GeneralMixedRawSchedule305

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 15500000
namespace Yulang.GeneralMixedScalarPartial305
open GeneralDictionaryOutputDepth252 (snapshot registry root roles)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthScalar285 (old target new_zero new_one from_source present previously_unknown)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalState (Known)
open GeneralNominalRefinements (Refines)
open GeneralMixedReindexOutputFixture305 (wide widened coordinates)
open GeneralRebaseDepthPathRank285 (ActualPath)

noncomputable def partialView (seen : Fin 2) : GeneralNormalizedObservation.Snapshot old.state.base where
  kinds := old.state.view.kinds
  shapes := old.state.view.shapes
  shapes_injective := old.state.view.shapes_injective
  canonical := old.state.view.canonical
  heads := fun slot => if slot.val = seen.val then target.state.view.heads slot else old.state.view.heads slot
  checked := by
    intro slot term recorded
    change (if slot.val = seen.val then target.state.view.heads slot else old.state.view.heads slot).term = some term at recorded
    split at recorded
    · exact target.state.view.checked slot term recorded
    · exact old.state.view.checked slot term recorded

noncomputable def partialState (seen : Fin 2) : GeneralNominalState.State :=
  { old.state with
    view := partialView seen
    bodies_opaque := by
      intro slot d observed
      change (if slot.val = seen.val then target.state.view.heads slot else old.state.view.heads slot) = _
      split
      · exact target.state.bodies_opaque slot d observed
      · exact old.state.bodies_opaque slot d observed }

noncomputable def partialContext (seen : Fin 2) : GeneralNominalCandidates.Context :=
  { old with state := partialState seen }

theorem still_known (seen : Fin 2) (n : Nat) : Known old.state n → Known (partialState seen) n := by
  rintro ⟨slot,source,headed|nom⟩
  · change snapshot.view.graph slot ≠ .unresolved at headed
    exact (headed rfl).elim
  · exact ⟨slot,source,Or.inr nom⟩

theorem original_slot (seen : Fin 2) (slot : Fin 4) (unseen : slot.val ≠ seen.val) :
    (partialState seen).view.graph slot = old.state.view.graph slot := by
  unfold GeneralNormalizedObservation.Snapshot.graph
  change (if slot.val = seen.val then target.state.view.heads slot else old.state.view.heads slot).node = _
  rw [ite_eq_right unseen]

theorem promoted_slot (seen : Fin 2) (slot : Fin 4) (seenEq : slot.val = seen.val) :
    (partialState seen).view.graph slot = target.state.view.graph slot := by
  unfold GeneralNormalizedObservation.Snapshot.graph
  change (if slot.val = seen.val then target.state.view.heads slot else old.state.view.heads slot).node = _
  rw [ite_eq_left seenEq]

theorem seen_known (seen : Fin 2) : Known (partialState seen) seen.val := by
  let slot : Fin 4 := ⟨seen.val,Nat.lt_trans seen.isLt (by decide)⟩
  refine ⟨slot,rfl,Or.inl ?_⟩
  rw [promoted_slot seen slot rfl]
  have small : seen.val = 0 ∨ seen.val = 1 := by omega
  rcases small with zero|one
  · have q : slot = 0 := Fin.ext zero
    rw [q]
    exact (show target.state.view.graph (0 : Fin 4) ≠ .unresolved from by decide +kernel)
  · have q : slot = 1 := Fin.ext one
    rw [q]
    exact (show target.state.view.graph (1 : Fin 4) ≠ .unresolved from by decide +kernel)

theorem unseen_unknown (seen unseen : Fin 2) (different : seen ≠ unseen) :
    ¬ Known (partialState seen) unseen.val := by
  rintro ⟨slot,source,headed|nom⟩
  · have loc : slot.val = unseen.val := source
    have other : slot.val ≠ seen.val := fun h => different (Fin.ext (h.symm.trans loc))
    rw [original_slot seen slot other] at headed
    exact headed rfl
  · exact previously_unknown unseen.val (Nat.le_of_lt_succ unseen.isLt) ⟨slot,source,Or.inr nom⟩

theorem after_known (seen : Fin 2) (n : Nat) : Known (partialState seen) n → Known target.state n := by
  rintro ⟨slot,source,headed|nom⟩
  · by_cases same : slot.val = seen.val
    · exact ⟨slot,source,Or.inl ((promoted_slot seen slot same) ▸ headed)⟩
    · rw [original_slot seen slot same] at headed
      exact (headed rfl).elim
  · exact ⟨slot,source,Or.inr nom⟩

theorem full_known (seen : Fin 2) : Known target.state seen.val := by
  have small : seen.val = 0 ∨ seen.val = 1 := by omega
  rcases small with zero|one
  · rw [zero]
    exact new_zero
  · rw [one]
    exact new_one

end Yulang.GeneralMixedScalarPartial305
