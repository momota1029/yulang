import Yulang.GeneralDictionaryOutputBinderTerms
import Yulang.GeneralDeclarationExamples

/-!
# Actual output-binder RHS and non-vacuous recording regressions

The checked declaration is `wrap` with only its associated RHS changed to the
produced output variable. Input variables, compound RHSs, and positional role
defaults remain deferred. The general-state fixture checks the output bridge;
its supplied head term is not a declaration-head elaboration theorem.
-/
namespace Yulang.GeneralDictionaryOutputBinderExamples
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDeclarationExamples
open GeneralDictionaryOutputBinderTerms
open GeneralSourceState (State Demand Assignment Models)
open GeneralDictionaryStateEquations
open GeneralDictionaryEquationRecording (record record_models atoms)

abbrev binderEquation : Equation := { outDefinition with rhs := .var 1 }
abbrev binderWrap : Declaration := { wrap with associated := [binderEquation] }

theorem binderWrap_checked : DeclarationChecked constructors roles binderWrap := by
  constructor
  · refine ⟨rfl, ?_, ?_, wrap_checked.signature.2.2.2⟩
    · intro equation member
      have same := List.mem_singleton.mp member
      subst equation
      exact ⟨none, rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name
        exact Or.inl ⟨binderEquation, by simp, rfl⟩
      · simp [roles, outputRole, zero] at present
  · simp [Declaration.Identified, Declaration.outputNames]
  · exact wrap_checked.produced
  · exact wrap_checked.outputOnly
  · simp [Declaration.Scoped, Declaration.inputNames, Declaration.outputNames,
      normalizeArgs, normalize, variablesArgs, Pattern.variables]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped, constructors]
  · exact wrap_checked.countsCovered
  · exact wrap_checked.paterson
  · exact wrap_checked.conservative
  · exact wrap_checked.captureStable

abbrev capture : Capture := ⟨fun _ => (0, 1), fun _ => 2⟩
abbrev allocation : Allocation roles containerChild := ⟨fun _ => (30, 31), fun _ => 40⟩

theorem actual_rhs_lookup : lookup roles binderWrap capture 0 = some (.var 2) := rfl

theorem actual_rhs_denotes : Denotes roles binderWrap capture 0 (.var 2) :=
  (lookup_exact roles binderWrap capture binderWrap_checked.identified.2.2.1 0 (.var 2)).mp
    actual_rhs_lookup

/-- The producer output is the same captured identity, not its spare allocation. -/
theorem child_producer_target :
    (childDemand binderWrap containerChild
      (binderWrap_checked.signature.2.2.2 containerChild (by simp)) capture allocation).outputs =
      [⟨1, 2⟩] := rfl

theorem compound_deferred : lookup roles wrap capture 0 = none := rfl

abbrev inputWrap : Declaration :=
  { wrap with associated := [{ outDefinition with rhs := .var 0 }] }

theorem input_deferred : lookup roles inputWrap capture 0 = none := rfl

abbrev defaultRoles : Roles.RoleDecls := fun _ =>
  { arity := 1
    assoc := fun name => if name = 0 then some (some (.var 0)) else none
    defaultsScoped := by
      intro name rhs present
      split at present
      · cases present; simp [Roles.Term.bound]
      · cases present }

abbrev defaultWrap : Declaration := { binderWrap with associated := [] }

theorem positional_default_retained :
    GeneralDictionaryAssociatedProvenance.lookup defaultRoles defaultWrap 0 =
      some (.default 1 0 (.var 0)) := rfl

theorem default_deferred : lookup defaultRoles defaultWrap capture 0 = none := rfl

abbrev demand : Demand roles where
  role := 1
  arguments := fun _ => (0, 1)
  outputs := [⟨0, 3⟩, ⟨0, 4⟩]
  declared := by
    intro output member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨none, rfl⟩

/-- One associated name retains both distinct target occurrences. -/
theorem repeated_root_targets : outputs roles binderWrap capture demand =
    [(⟨0, 3⟩, some (.var 2)), (⟨0, 4⟩, some (.var 2))] := rfl

abbrev state : State where
  slots := 5
  source := Fin.val
  source_injective := by intro first last same; exact Fin.ext same
  rowSource := fun slot => slot.val + 10
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro index; exact Fin.elim0 index
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev located : Located state demand where
  lower := fun _ => 0
  upper := fun _ => 1
  head := fun _ => .var 0
  target := fun index => ⟨index.val + 3, by have bound := index.isLt; change index.val < 2 at bound; change index.val + 3 < 5; omega⟩
  output := fun _ => .var 2
  arguments := fun _ => rfl
  targets := by
    intro index
    obtain ⟨index, bound⟩ := index
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> rfl

theorem located_interpreted : Interpreted binderWrap capture located := by
  intro index
  obtain ⟨index, bound⟩ := index
  change index < 2 at bound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

abbrev assignment : Assignment := fun _ => (.base .int, Common.rowEmpty)

theorem recording_has_model : Models (record located) assignment := by
  apply (record_models located assignment).mpr
  constructor
  · apply (GeneralSourceState.models_ordinary state assignment).mpr
    intro atom member
    cases member
  · constructor
    · intro index
      exact ⟨Common.subtype_refl _, Common.subtype_refl _⟩
    · intro index
      exact Common.equivalent_refl _

/-- Every recorded model equates each actual root target with the real captured
output binder. The witness above rules out a vacuous all-model statement. -/
theorem all_model_binder_output (model : Assignment) (valid : Models (record located) model)
    (index : Fin demand.outputs.length) :
    Common.Equivalent (model (demand.outputs[index]).target).1 (model 2).1 :=
  (recorded_output_denotes binderWrap capture binderWrap_checked.identified.2.2.1
    located located_interpreted model valid index).2

/-- The binder is also the emitted child output, at the unchanged source ID. -/
theorem all_model_child_output (model : Assignment) (valid : Models (record located) model)
    (index : Fin demand.outputs.length) :
    Common.Equivalent (model (demand.outputs[index]).target).1
      (model (outputTarget binderWrap capture allocation.outputs itemEquation)).1 :=
  all_model_binder_output model valid index

abbrev allocations (clause : Clause) : Allocation roles clause :=
  ⟨fun _ => (30, 31), fun _ => 40⟩

/-- The generic source-producer theorem also applies to this concrete checked
example, without selecting an arbitrary implementation of associated outputs. -/
theorem all_model_actual_producer (model : Assignment) (valid : Models (record located) model)
    (index : Fin demand.outputs.length) :
    ∃ clause, ∃ present : clause ∈ binderWrap.requirements, ∃ equation ∈ clause.outputs,
      ⟨equation.name, outputTarget binderWrap capture (allocations clause).outputs equation⟩ ∈
        (childDemand binderWrap clause
          (binderWrap_checked.signature.2.2.2 clause present) capture (allocations clause)).outputs ∧
      Common.Equivalent (model (demand.outputs[index]).target).1
        (model (outputTarget binderWrap capture (allocations clause).outputs equation)).1 :=
  recorded_output_producer binderWrap_checked capture located located_interpreted allocations
    model valid index

theorem repeated_equations_recorded : demand.outputs.length = 2 ∧ (atoms located).length = 6 :=
  ⟨rfl, rfl⟩

end Yulang.GeneralDictionaryOutputBinderExamples
