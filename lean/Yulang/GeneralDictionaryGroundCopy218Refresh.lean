import Yulang.GeneralNominalCenteredHeadMatHeadShape
import Yulang.GeneralDictionaryLooseVariant217
import Yulang.GeneralNominalCenteredHeadMatStepRefresh
import Yulang.GeneralNominalCenteredHeadMatStepCache

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryGroundCopy218Refresh
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralDictionaryInspectionHeads215 GeneralNominalFiniteHeadInversion
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCommonBridge (Assignment)

/-- The general carrier's top has no exact constructor head. -/
theorem top_no_head (test : Test) : ¬ test.Holds (.top : Ty) := by
  intro held
  have impossible := (tagged_test test held ⟨fun _ => .bottom,fun _ => [head test]⟩).mpr
    (List.mem_singleton_self _)
  exact impossible

/-- An observed variant requires a source slot for its payload. -/
theorem variant_represented (snapshot : GeneralNominalState.State) (model : Assignment)
    (identity tag : Nat) (payload : Ty)
    (known : GeneralNominalState.Known snapshot identity)
    (cache : ∀ observation, GeneralCanonicalObservations.Recorded snapshot observation → observation.Holds model)
    (value : Equivalent (model identity).1 (variant tag payload)) :
    ∃ slot : Fin snapshot.base.slots, Equivalent (model (snapshot.base.source slot)).1 payload := by
  obtain ⟨test,observation,headed⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  cases headed with
  | scalar slot base recorded =>
      have actual := cache _ (.scalar slot base recorded)
      have tags := tag_subtype (tagged_equivalent value (by intro env; rfl))
        (tagged_scalar base) actual.1
      cases tags
  | nominal slot descriptor recorded =>
      obtain ⟨arguments,_,actual⟩ := cache _ (.nominal slot descriptor recorded)
      have tags := tag_subtype (tagged_equivalent value (by intro env; rfl))
        (tagged_nominal _ _) actual.1
      cases tags
  | structural slot kind children recorded =>
      have actual := cache _ (.structural slot kind children recorded)
      have buildEq : Equivalent (model (snapshot.base.source slot)).1
          (shapeValue (snapshot.view.shapes kind)
            (List.ofFn fun i => (model (snapshot.base.source (children i))).1)) := by
        change Equivalent _ (((snapshot.view.shapes kind).term children).eval CommonNominalFullCarrier.model
          (GeneralNominalCommonBridge.assignment snapshot.base model)) at actual
        have equal := GeneralNominalStructuralReadback.shape_values (snapshot.view.shapes kind) children
          (GeneralNominalCommonBridge.assignment snapshot.base model)
        exact equal.symm ▸ actual
      have tags := tag_subtype (tagged_equivalent value (by intro env; rfl))
        (tagged_shape _ _ (List.length_ofFn ..)) buildEq.1
      have shapeEq : snapshot.view.shapes kind = .variant tag := by
        cases shape : snapshot.view.shapes kind with
        | pair | record | exactEmpty => simp [shape,head] at tags
        | variant other =>
          have same : tag = other := by simpa [shape,head] using tags
          exact congrArg GeneralNormalizedObservation.Shape.variant same.symm
      let index : Fin (snapshot.view.shapes kind).arity := ⟨0,by rw [shapeEq]; exact Nat.zero_lt_succ 0⟩
      have generic (shape : GeneralNormalizedObservation.Shape)
          (cs : Fin shape.arity → Fin snapshot.base.slots) (i : Fin shape.arity)
          (same : shape = .variant tag) :
          (shape.term cs).eval CommonNominalFullCarrier.model
            (GeneralNominalCommonBridge.assignment snapshot.base model) =
            variant tag (model (snapshot.base.source (cs i))).1 := by
        subst shape
        change Fin 1 at i
        have zero : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      have rhs := generic _ children index shapeEq
      change Equivalent _ (((snapshot.view.shapes kind).term children).eval CommonNominalFullCarrier.model
        (GeneralNominalCommonBridge.assignment snapshot.base model)) at actual
      rw [rhs] at actual
      exact ⟨children index,(common_variant_iff ..).mp (subtype_trans actual.2 value.1),
        (common_variant_iff ..).mp (subtype_trans value.2 actual.1)⟩

theorem head_holds {snapshot : GeneralNominalState.State} {model : Assignment} (headed : GeneralNominalSupport.Head snapshot identity test observation)
    (held : observation.Holds model) : test.Holds (model identity).1 := by
  cases headed with
  | scalar => exact held
  | nominal slot descriptor recorded =>
    obtain ⟨arguments,fit,equal⟩ := held
    exact ⟨arguments,GeneralNominalLinearMaterializationFacts.fitsAll_length _ _ _ _ fit,equal⟩
  | structural slot kind children recorded =>
    refine ⟨List.ofFn (fun index => (model (snapshot.base.source (children index))).1),List.length_ofFn,?_⟩
    have equal := GeneralNominalStructuralReadback.shape_values (snapshot.view.shapes kind) children
      (GeneralNominalCommonBridge.assignment snapshot.base model)
    exact equal.symm ▸ held

/-- No cache certificate can add a head for an unrepresented scalar payload.
This quantifies over all source identities of the proposed snapshot. -/
theorem no_new_head {roles : Roles.RoleDecls}
    (state : State roles) (model : Assignment) (valid : Models state model)
    (snapshot : GeneralNominalState.State)
    (cache : GeneralNominalCenteredHeadMatStepObservations.CacheSound state snapshot)
    (identity : Nat)
    (shape : (model identity).1 = .bottom ∨ (model identity).1 = .top ∨
      ∃ base, (model identity).1 = variant 0 (.base base) ∧
        ∀ source, ¬ Equivalent (model source).1 (.base base)) :
    ¬ GeneralNominalState.Known snapshot identity := by
  intro known
  rcases shape with bottom | top | ⟨base,value,absent⟩
  · obtain ⟨test,observation,headed⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
    have held := head_holds headed
      (GeneralNominalCenteredHeadMatStepObservations.cache_sound cache
        (GeneralNominalSupport.head_recorded headed) valid)
    rw [bottom] at held
    exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head test held
  · obtain ⟨test,observation,headed⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
    have held := head_holds headed
      (GeneralNominalCenteredHeadMatStepObservations.cache_sound cache
        (GeneralNominalSupport.head_recorded headed) valid)
    rw [top] at held
    exact top_no_head test held
  · obtain ⟨slot,same⟩ := variant_represented snapshot model identity 0 (.base base) known
      (fun _ recorded => GeneralNominalCenteredHeadMatStepObservations.cache_sound cache recorded valid)
      (value ▸ ⟨subtype_refl _,subtype_refl _⟩)
    exact absent (snapshot.base.source slot) same

end Yulang.GeneralDictionaryGroundCopy218Refresh
