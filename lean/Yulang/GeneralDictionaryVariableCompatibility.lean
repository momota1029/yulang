import Yulang.GeneralDictionaryVariableTerms

/-! # Successful binder-only packages are unchanged by singleton-input support -/
namespace Yulang.GeneralDictionaryVariableCompatibility
open GeneralDeclarations GeneralDeclarationDemands
open GeneralDictionaryStateEquations GeneralDictionaryVariableTerms
open GeneralDictionaryBinderLocations (Inputs)
open GeneralSourceState (State Demand)
open Core.PresenceGeneration (TyTerm)
variable {roles : Roles.RoleDecls} {state : State} {demand : Demand roles}

theorem compile_preserved (state : State) (roles : Roles.RoleDecls) (declaration : Declaration)
    (capture : Capture) (unique : (declaration.associated.map Equation.name).Nodup)
    (name : Nat) (term : TyTerm (Fin state.slots))
    (found : GeneralDictionaryBinderLocations.compile state roles declaration capture name = some term) :
    compile state roles declaration capture name = some term := by
  obtain ⟨source, original, localized⟩ := Option.bind_eq_some_iff.mp found
  unfold compile
  rw [output_lookup_preserved roles declaration capture unique name source original]
  exact localized

/-- All fields, including every compiled output occurrence, remain identical. -/
theorem build_preserved (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup)
    (inputs : Inputs state demand) (located : Located state demand)
    (built : GeneralDictionaryBinderLocations.build declaration capture inputs = some located) :
    build declaration capture inputs = some located := by
  unfold GeneralDictionaryBinderLocations.build at built
  split at built
  next complete =>
    cases built
    have compiled : ∀ index : Fin demand.outputs.length,
        compile state roles declaration capture (demand.outputs[index]).name =
          some ((GeneralDictionaryBinderLocations.compile state roles declaration capture
            (demand.outputs[index]).name).get (complete index)) := by
      intro index
      exact compile_preserved state roles declaration capture unique _ _
        (Option.some_get (complete index)).symm
    have allPresent : ∀ index : Fin demand.outputs.length,
        (compile state roles declaration capture (demand.outputs[index]).name).isSome = true := by
      intro index
      rw [compiled index]
      rfl
    unfold build
    rw [dite_eq_left allPresent]
    congr 1
    congr
    funext index
    simp only [compiled index, Option.get_some]
  next incomplete => cases built

end Yulang.GeneralDictionaryVariableCompatibility
