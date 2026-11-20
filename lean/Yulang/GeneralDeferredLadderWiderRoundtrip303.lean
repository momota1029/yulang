import Yulang.GeneralDeferredLadderWiderRefresh303

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderWiderRoundtrip303
open GeneralDeferredLadderWiderView303
open GeneralNominalRefinements (Refines)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalCandidates (Context)
open GeneralCanonicalObservations (Recorded)
open GeneralNominalVersionedJournal232 (State)

theorem recorded_iff (s : GeneralNominalState.State) (none : s.view.kinds = 0) (observation) :
    Recorded (wider s none) observation ↔ Recorded s observation := by
  refine ⟨recorded s none observation,?_⟩
  intro exactObs
  cases exactObs with
  | scalar slot scalar same =>
    apply GeneralCanonicalObservations.Recorded.scalar (snapshot := wider s none)
    change widenedHead none (s.view.heads slot) = .scalar scalar
    rw [same]
    rfl
  | structural slot kind kids same => exact Fin.elim0 (none ▸ kind)
  | nominal slot desc found => exact Recorded.nominal (snapshot := wider s none) slot desc found

def narrow_refines (s : GeneralNominalState.State) (none : s.view.kinds = 0) :
    Refines (wider s none) s := by
  let reference := GeneralNominalRefinements.refl s
  exact ⟨reference.base,reference.heads,reference.nominals,reference.ordinary,
    fun a known => (known_iff s none a).mp known,reference.reserved,reference.allocated,
    reference.seed,reference.constructors⟩

theorem refinement_both (s : GeneralNominalState.State) (none : s.view.kinds = 0) :
    Nonempty (Refines s (wider s none)) ∧ Nonempty (Refines (wider s none) s) :=
  ⟨⟨widen_refines (GeneralNominalRefinements.refl s) none⟩,⟨narrow_refines s none⟩⟩

end Yulang.GeneralDeferredLadderWiderRoundtrip303
