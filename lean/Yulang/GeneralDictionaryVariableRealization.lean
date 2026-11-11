import Yulang.GeneralDictionaryVariableMaterialization

/-!
# Variable RHS meaning for every compatible captured instantiation

The source compiler does not prove that capture was obtained by matching a
head. This boundary states precisely what such a matcher must provide: input
values lie in captured intervals and output values agree with captured source
variables. An exact-input alias is correct for every such realization, not
because an arbitrary interval midpoint was chosen by the compiler.
-/
namespace Yulang.GeneralDictionaryVariableRealization
open GeneralDeclarations GeneralDeclarationDemands GeneralDeclarationPatterns
open GeneralSourceState (State Demand Assignment Models)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralDictionaryStateEquations
open GeneralDictionaryBinderLocations (Inputs)
open GeneralDictionaryVariableTerms (Denotes build)
open Core.PresenceGeneration (TyTerm)
variable {roles : Roles.RoleDecls} {state : State} {demand : Demand roles}

/-- Local compatibility, not candidate selection or a successful head match. -/
def Realizes (declaration : Declaration) (capture : Capture)
    (assignment : Assignment) (values : Nat → Common.Ty) : Prop :=
  (∀ binder ∈ declaration.inputNames,
    Common.Subtype (assignment (capture.inputs binder).1).1 (values binder) ∧
    Common.Subtype (values binder) (assignment (capture.inputs binder).2).1) ∧
  (∀ binder ∈ declaration.outputNames,
    Common.Equivalent (values binder) (assignment (capture.outputs binder)).1)

/-- Every value in an interval with the same endpoint identity is equivalent
to that endpoint, without solving or selecting any other interval. -/
theorem singleton_value (capture : Capture) (assignment : Assignment)
    (binder : Nat) (value : Common.Ty)
    (same : (capture.inputs binder).1 = (capture.inputs binder).2)
    (inside : Common.Subtype (assignment (capture.inputs binder).1).1 value ∧
      Common.Subtype value (assignment (capture.inputs binder).2).1) :
    Common.Equivalent value (assignment (capture.inputs binder).1).1 := by
  rw [← same] at inside
  exact ⟨inside.2, inside.1⟩

/-- Actual normalized variable RHS provenance plus correctness for every
capture realization. No arbitrary associated-type meaning function is used. -/
theorem denotes_realization (roles : Roles.RoleDecls) (declaration : Declaration)
    (capture : Capture) (assignment : Assignment) (values : Nat → Common.Ty)
    (realized : Realizes declaration capture assignment values) (name : Nat) (term : TyTerm Nat)
    (denoted : Denotes roles declaration capture name term) :
    ∃ equation binder, Supplies roles declaration name (.explicit equation) ∧
      normalize equation.rhs = .var binder ∧
      Common.Equivalent (values binder) (term.eval Common.model assignment) := by
  obtain ⟨equation, binder, supplied, normalized, source⟩ := denoted
  refine ⟨equation, binder, supplied, normalized, ?_⟩
  rcases source with ⟨output, rfl⟩ | ⟨_, input, same, rfl⟩
  · exact realized.2 binder output
  · exact singleton_value capture assignment binder (values binder) same (realized.1 binder input)

/-- Recorded root targets equal the actual RHS variable value in every final
model and every compatible capture realization. Existence of a head match or
such a model is not assumed silently or derived from this output theorem. -/
theorem built_output_realization (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup)
    (inputs : Inputs state demand) (located : Located state demand)
    (built : build declaration capture inputs = some located)
    (assignment : Assignment) (model : Models (GeneralDictionaryEquationRecording.record located) assignment)
    (values : Nat → Common.Ty) (realized : Realizes declaration capture assignment values)
    (index : Fin demand.outputs.length) :
    ∃ equation binder, Supplies roles declaration (demand.outputs[index]).name (.explicit equation) ∧
      normalize equation.rhs = .var binder ∧
      Common.Equivalent (assignment (demand.outputs[index]).target).1 (values binder) := by
  have output := GeneralDictionaryVariableTerms.built_output_models declaration capture unique inputs located
    built assignment model index
  obtain ⟨equation, binder, supplied, normalized, meaning⟩ :=
    denotes_realization roles declaration capture assignment values realized _ _ output.1
  exact ⟨equation, binder, supplied, normalized,
    Common.equivalent_trans output.2 (Common.equivalent_symm meaning)⟩

end Yulang.GeneralDictionaryVariableRealization
