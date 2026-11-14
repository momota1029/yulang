import Yulang.GeneralNominalCenteredSourceRefreshWitness

/-! A source-only observation of the independent Int slot. It exposes no
new relation between the unknown pair children and that independent slot. -/
namespace Yulang.GeneralNominalCenteredSourceUnsettledRefreshControl
open GeneralNominalCenteredSourceRefreshWitness
open Core.PresenceGeneration (TyTerm)

abbrev intView : GeneralNormalizedObservation.Snapshot base where
  kinds := view.kinds
  shapes := view.shapes
  shapes_injective := view.shapes_injective
  canonical := view.canonical
  heads := fun slot => if slot = 3 then .scalar .int else view.heads slot
  checked := by
    intro slot term recorded
    by_cases three : slot = 3
    · subst slot
      have equal : (.base .int : TyTerm (Fin 4)) = term := by
        simpa [GeneralNormalizedObservation.Head.term] using recorded
      subst term
      exact .ordinary (by decide +kernel) (by decide +kernel)
    · have old : (view.heads slot).term = some term := by simpa only [three,ite_false] using recorded
      exact view.checked slot term old

abbrev sourceInt : GeneralNominalState.State := {source with view := intView, bodies_opaque := by intro slot descriptor recorded; cases recorded}

theorem source_models (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models sourceInt model ↔ GeneralNominalState.Models source model := Iff.rfl

theorem int_head : GeneralNominalSupport.Head sourceInt 3 (.scalar .int)
    (.normalized base 3 (.base .int)) := .scalar (snapshot := sourceInt) 3 .int rfl

theorem int_sound (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source model) :
    (GeneralCanonicalObservations.Observation.normalized base 3 (.base .int)).Holds model :=
  GeneralCanonicalObservations.recorded_sound sourceInt model ((source_models model).mpr valid)
    (GeneralNominalSupport.head_recorded int_head)

end Yulang.GeneralNominalCenteredSourceUnsettledRefreshControl
