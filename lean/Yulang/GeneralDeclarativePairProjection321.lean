import Yulang.GeneralDeclarativePairCut321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePairProjection321
open CommonNominalFullCarrier (Ty Equivalent pair common_pair_iff)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm)
open GeneralDeclarativePairCut321 (pairCode)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralNominalCommonBridge (Assignment)

/-- Given a real actual pair equation, repeated capture is exactly equivalence
of its actual coordinate names. The criterion is not equality of lower or
upper projections. -/
theorem diagonal_exact (a b : Ty) :
    (∃ x, Equivalent (pair a b) (pair x x)) ↔ Equivalent a b := by
  constructor
  · rintro ⟨x,one,two⟩
    have out := (common_pair_iff ..).mp one
    have inside := (common_pair_iff ..).mp two
    exact ⟨CommonNominalFullCarrier.subtype_trans out.1 inside.2,
      CommonNominalFullCarrier.subtype_trans out.2 inside.1⟩
  · intro same
    exact ⟨a,(common_pair_iff ..).mpr ⟨(eqv_refl _).1,same.2⟩,
      (common_pair_iff ..).mpr ⟨(eqv_refl _).1,same.1⟩⟩

theorem projection_exact {s : State}
    (actual : Entails s ⟨root,pairCode first second⟩) (m : Assignment) (valid : Models s m) :
    (∃ x, Equivalent (m root).1 (pair x x)) ↔ Equivalent (m first).1 (m second).1 := by
  have modelHead := actual m valid
  change Equivalent (m root).1 (pair (m first).1 (m second).1) at modelHead
  constructor
  · rintro ⟨x,both⟩
    exact (diagonal_exact ..).mp ⟨x,eqv_trans (eqv_symm modelHead) both⟩
  · intro same
    obtain ⟨x,both⟩ := (diagonal_exact ..).mpr same
    exact ⟨x,eqv_trans modelHead both⟩

theorem chosen_projection {s : State}
    (actual : Entails s ⟨root,pairCode first second⟩)
    (same : Entails s ⟨second,.variable first⟩) :
    Entails s ⟨root,pairCode first first⟩ := by
  intro m valid
  have projected := actual m valid
  change Equivalent (m root).1 (pair (m first).1 (m second).1) at projected
  have other := same m valid
  change Equivalent (m second).1 (m first).1 at other
  exact eqv_trans projected ⟨(common_pair_iff ..).mpr ⟨(eqv_refl _).1,other.1⟩,
    (common_pair_iff ..).mpr ⟨(eqv_refl _).2,other.2⟩⟩

end Yulang.GeneralDeclarativePairProjection321
