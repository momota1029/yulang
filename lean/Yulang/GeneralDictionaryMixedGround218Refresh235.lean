import Yulang.GeneralDictionaryMixedGround218Safety235
import Yulang.GeneralDictionaryGroundCopy218Refresh
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedGround218Refresh235
open GeneralDictionaryGroundCopy218Source

open GeneralDictionaryMixedGround218Leaf235
open GeneralDictionaryMixedGround218Install234 (installed installed_model)
open GeneralDictionaryGroundCopy218Stability (model_no_scalar)
open GeneralDictionaryGroundCopy218Refresh
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralDictionaryGroundCopy218Install (model)
theorem no_new_head
    (model : Assignment)
    (snapshot : GeneralNominalState.State)
    (cache : ∀ observation, GeneralCanonicalObservations.Recorded snapshot observation → observation.Holds model)
    (identity : Nat)
    (shape : (model identity).1 = .bottom ∨ (model identity).1 = .top ∨
      ∃ base, (model identity).1 = variant 0 (.base base) ∧
        ∀ source, ¬ Equivalent (model source).1 (.base base)) :
    ¬ GeneralNominalState.Known snapshot identity := by
  intro known
  rcases shape with bottom | top | ⟨base,value,absent⟩
  · obtain ⟨test,observation,headed⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
    have held := head_holds headed
      (cache _ (GeneralNominalSupport.head_recorded headed))
    rw [bottom] at held
    exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head test held
  · obtain ⟨test,observation,headed⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
    have held := head_holds headed
      (cache _ (GeneralNominalSupport.head_recorded headed))
    rw [top] at held
    exact top_no_head test held
  · obtain ⟨slot,same⟩ := variant_represented snapshot model identity 0 (.base base) known
      cache
      (value ▸ ⟨subtype_refl _,subtype_refl _⟩)
    exact absent (snapshot.base.source slot) same

theorem unknown_shape (unknown : ¬ GeneralNominalState.Known ctx.state identity) :
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
    exact unknown ⟨(6 : Fin 8),rfl,Or.inr ⟨loose,rfl⟩⟩
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


theorem no_refresh
    (certificate : GeneralNominalVersionedMixedObservations233.Refresh installed nextContext)
    (unknown : ¬ GeneralNominalState.Known ctx.state identity)
    (known : GeneralNominalState.Known nextContext.state identity) : False := by
  have next := (GeneralNominalVersionedMixedObservations233.refresh_models certificate).mpr installed_model
  exact no_new_head model nextContext.state
    (fun _ recorded => GeneralCanonicalObservations.recorded_sound nextContext.state model next.1.1 recorded)
    identity (unknown_shape unknown) known
end Yulang.GeneralDictionaryMixedGround218Refresh235
