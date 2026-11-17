import Yulang.GeneralDictionaryMixedGround218Refresh235
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedGround218PointRefresh235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Stability (model_no_scalar)
open CommonNominalFullCarrier
open GeneralDictionaryGroundCopy218Install (model)
theorem unknown_shape (allocated reserved atoms) (unknown : ¬ GeneralNominalState.Known (GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved atoms) identity) :
    (model identity).1 = .bottom ∨ (model identity).1 = .top ∨
      ∃ scalar, (model identity).1 = variant 0 (.base scalar) ∧
        ∀ source, ¬ Equivalent (model source).1 (.base scalar) := by
  by_cases a : identity = GeneralNominalCenters.fresh 7 0 0 8 0 0
  · exact Or.inr (Or.inr ⟨.int,by simp only [GeneralDictionaryGroundCopy218Install.model,ite_eq_left a]; rfl,fun source => model_no_scalar source .int⟩)
  by_cases b : identity = GeneralNominalCenters.fresh 7 0 0 8 1 0
  · exact Or.inr (Or.inr ⟨.bool,by simp only [GeneralDictionaryGroundCopy218Install.model,ite_eq_right a,ite_eq_left b]; rfl,fun source => model_no_scalar source .bool⟩)
  have value : (model identity).1 = sourceValue identity := by simp [GeneralDictionaryGroundCopy218Install.model,a,b]
  have two : identity ≠ 2 := by
    rintro rfl
    exact unknown ⟨(2 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩
  have three : identity ≠ 3 := by
    rintro rfl
    exact unknown ⟨(3 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩
  have six : identity ≠ 6 := by
    rintro rfl
    exact unknown ⟨(6 : Fin 8),rfl,Or.inr ⟨exactCopy,rfl⟩⟩
  have seven : identity ≠ 7 := by
    rintro rfl
    exact unknown ⟨(7 : Fin 8),rfl,Or.inr ⟨exactCopy,rfl⟩⟩
  rcases identity with _ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | identity)))))))
  · exact Or.inl value
  · exact Or.inr (Or.inl value)
  · exact False.elim (two rfl)
  · exact False.elim (three rfl)
  · exact Or.inr (Or.inr ⟨.int,value,fun source => model_no_scalar source .int⟩)
  · exact Or.inr (Or.inr ⟨.bool,value,fun source => model_no_scalar source .bool⟩)
  · exact False.elim (six rfl)
  · exact False.elim (seven rfl)
  · exact Or.inl value


theorem no_refresh {state : GeneralNominalVersionedJournal232.State roles}
    (allocated reserved atoms)
    (current : state.core.erased.current.context.state =
      GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved atoms)
    (valid : GeneralNominalVersionedJournal232.Models state model)
    (certificate : GeneralNominalVersionedMixedObservations233.Refresh state nextContext)
    (unknown : ¬ GeneralNominalState.Known state.core.erased.current.context.state identity)
    (known : GeneralNominalState.Known nextContext.state identity) : False := by
  have next := (GeneralNominalVersionedMixedObservations233.refresh_models certificate).mpr valid
  exact GeneralDictionaryMixedGround218Refresh235.no_new_head model nextContext.state
    (fun _ recorded => GeneralCanonicalObservations.recorded_sound nextContext.state model next.1.1 recorded)
    identity (unknown_shape allocated reserved atoms (current ▸ unknown)) known
end Yulang.GeneralDictionaryMixedGround218PointRefresh235
