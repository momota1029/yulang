import Yulang.GeneralDictionaryBinderLocations
import Yulang.GeneralDictionaryOutputBinderExamples

/-!
# Computed output locations retain global and local identities

Only the head and endpoint/target locations are inputs. The output vector is
computed from the checked declaration's real RHS. Repeated output occurrences
are retained, and one unsupported or absent source makes the build deferred.
-/
namespace Yulang.GeneralDictionaryBinderLocationExamples
open GeneralDeclarations GeneralDeclarationDemands
open GeneralDeclarationExamples (roles wrap)
open GeneralDictionaryOutputBinderExamples
open GeneralDictionaryBinderLocations
open GeneralDictionaryStateEquations
open GeneralSourceState (State Demand)

abbrev inputs : Inputs state demand where
  lower := located.lower
  upper := located.upper
  head := located.head
  target := located.target
  arguments := located.arguments
  targets := located.targets

theorem prior_source_lookup : sourceSlot state 2 = some 2 := rfl

theorem prior_rhs_compiles : compile state roles binderWrap capture 0 = some (.var 2) := rfl

private theorem prior_occurrence_compiles (index : Fin demand.outputs.length) :
    compile state roles binderWrap capture (demand.outputs[index]).name = some (.var 2) := by
  obtain ⟨index, bound⟩ := index
  change index < 2 at bound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

/-- The prior handwritten output vector is reconstructed without supplying it. -/
theorem reconstructs_prior_located : build binderWrap capture inputs = some located := by
  have complete : ∀ index : Fin demand.outputs.length,
      (compile state roles binderWrap capture (demand.outputs[index]).name).isSome = true := by
    intro index
    rw [prior_occurrence_compiles index]
    rfl
  unfold build
  rw [dite_eq_left complete]
  congr 1
  congr
  funext index
  simp only [prior_occurrence_compiles index, Option.get_some]

abbrev shiftedState : State :=
  { state with
    source := fun slot => slot.val + 10
    source_injective := by
      intro first last equal
      apply Fin.ext
      change first.val + 10 = last.val + 10 at equal
      exact Nat.add_right_cancel equal }

abbrev shiftedCapture : Capture := ⟨fun _ => (10, 11), fun _ => 12⟩

abbrev shiftedDemand : Demand roles where
  role := 1
  arguments := fun _ => (10, 11)
  outputs := [⟨0, 13⟩, ⟨0, 14⟩]
  declared := by
    intro output member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨none, rfl⟩

abbrev shiftedLocated : Located shiftedState shiftedDemand where
  lower := fun _ => 0
  upper := fun _ => 1
  head := fun _ => .var 0
  target := fun index => ⟨index.val + 3, by
    have bound := index.isLt
    change index.val < 2 at bound
    change index.val + 3 < 5
    omega⟩
  output := fun _ => .var 2
  arguments := fun _ => rfl
  targets := by
    rintro ⟨index, bound⟩
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> rfl

abbrev shiftedInputs : Inputs shiftedState shiftedDemand where
  lower := shiftedLocated.lower
  upper := shiftedLocated.upper
  head := shiftedLocated.head
  target := shiftedLocated.target
  arguments := shiftedLocated.arguments
  targets := shiftedLocated.targets

/-- Source 12 is local slot 2. Local slot number 2 is not a present source ID. -/
theorem nonidentity_source_lookup : sourceSlot shiftedState 12 = some 2 ∧
    sourceSlot shiftedState 2 = none := ⟨rfl, rfl⟩

theorem nonidentity_rhs_compiles :
    compile shiftedState roles binderWrap shiftedCapture 0 = some (.var 2) := rfl

theorem nonidentity_lift_returns_actual_source :
    liftType shiftedState (.var 2) = .var 12 := rfl

private theorem shifted_occurrence_compiles (index : Fin shiftedDemand.outputs.length) :
    compile shiftedState roles binderWrap shiftedCapture (shiftedDemand.outputs[index]).name =
      some (.var 2) := by
  obtain ⟨index, bound⟩ := index
  change index < 2 at bound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

theorem builds_nonidentity_locations :
    build binderWrap shiftedCapture shiftedInputs = some shiftedLocated := by
  have complete : ∀ index : Fin shiftedDemand.outputs.length,
      (compile shiftedState roles binderWrap shiftedCapture
        (shiftedDemand.outputs[index]).name).isSome = true := by
    intro index
    rw [shifted_occurrence_compiles index]
    rfl
  unfold build
  rw [dite_eq_left complete]
  congr 1
  congr
  funext index
  simp only [shifted_occurrence_compiles index, Option.get_some]

/-- The whole result retains both targets rather than deduplicating the name. -/
theorem success_preserves_repeated_targets :
    (build binderWrap shiftedCapture shiftedInputs).map
      (fun result => [shiftedState.source (result.target ⟨0, by decide⟩),
        shiftedState.source (result.target ⟨1, by decide⟩)]) = some [13, 14] := by
  rw [builds_nonidentity_locations]
  rfl

abbrev absentCapture : Capture := { shiftedCapture with outputs := fun _ => 99 }

theorem missing_binder_source_defers : build binderWrap absentCapture shiftedInputs = none := by
  unfold build
  apply dite_eq_right
  intro complete
  have impossible := complete ⟨0, by decide⟩
  contradiction

theorem compound_defers_entire_build : build wrap capture inputs = none := by
  unfold build
  apply dite_eq_right
  intro complete
  have impossible := complete ⟨0, by decide⟩
  contradiction

theorem input_defers_entire_build : build inputWrap capture inputs = none := by
  unfold build
  apply dite_eq_right
  intro complete
  have impossible := complete ⟨0, by decide⟩
  contradiction

end Yulang.GeneralDictionaryBinderLocationExamples
