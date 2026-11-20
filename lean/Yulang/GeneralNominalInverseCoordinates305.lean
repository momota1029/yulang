import Yulang.GeneralNominalReportContext305

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalInverseCoordinates305
open GeneralNominalState (State)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalReportCoordinates305 (Coordinates HeadData observed nominalRead nominalMove)
open GeneralNominalReportContext305 (EquivalentContexts)
open GeneralNominalReportSourceTransport (moveBounds)
open GeneralNominalInspection (Bounds)
variable {a b : State} {old next : Context}

theorem head_inverse (f : α → β) (g : β → α) (left : ∀ x, g (f x) = x) (x : HeadData α) :
    (x.move f).move g = x := by
  cases x <;> simp only [HeadData.move,List.map_map,Function.comp_def,left,List.map_id']

theorem bounds_inverse (f : Fin a.base.slots → Fin b.base.slots) (g : Fin b.base.slots → Fin a.base.slots)
    (left : ∀ x, g (f x) = x) (x : Bounds a) :
    moveBounds g (moveBounds f x) = x := by
  simp [moveBounds,left]

theorem nominal_inverse (f : Fin a.base.slots → Fin b.base.slots)
    (g : Fin b.base.slots → Fin a.base.slots) (left : ∀ x, g (f x) = x)
    (entry : Option (Nat × Option (List (Bounds a)))) :
    nominalMove g (nominalMove f entry) = entry := by
  cases entry with
  | none => rfl
  | some pair =>
    obtain ⟨key,args⟩ := pair
    cases args
    · rfl
    · simp only [nominalMove,Option.map_some,List.map_map,Function.comp_def,bounds_inverse f g left,List.map_id']

theorem right_inverse (iso : EquivalentContexts old next) (i : Fin next.state.base.slots) :
    iso.geometry.slot (iso.backward.base.embed i) = i := by
  apply next.state.base.source_injective
  exact (iso.geometry.source_eq _).trans (iso.backward.base.source i)

theorem left_inverse (iso : EquivalentContexts old next) (i : Fin old.state.base.slots) :
    iso.backward.base.embed (iso.geometry.slot i) = i := by
  apply old.state.base.source_injective
  exact (iso.backward.base.source _).trans (iso.geometry.source_eq i)

def reverse (iso : EquivalentContexts old next) : EquivalentContexts next old := by
  refine ⟨iso.backward,iso.forward,⟨iso.backward.base.embed,iso.backward.base.source,?_,?_⟩,
    iso.interpretation.symm⟩
  · intro j
    have orig := iso.geometry.normalized (iso.backward.base.embed j)
    rw [right_inverse iso] at orig
    have same := congrArg (HeadData.move iso.backward.base.embed) orig
    rw [head_inverse _ _ (left_inverse iso)] at same
    exact same.symm
  · intro j
    have orig := iso.geometry.nominal (iso.backward.base.embed j)
    rw [right_inverse iso] at orig
    have same := congrArg (nominalMove iso.backward.base.embed) orig
    rw [nominal_inverse _ _ (left_inverse iso)] at same
    exact same.symm

end Yulang.GeneralNominalInverseCoordinates305
