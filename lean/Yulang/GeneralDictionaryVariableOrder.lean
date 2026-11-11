import Yulang.GeneralDictionaryVariableMaterialization

/-!
# Visible and where order invariance of computed variable packages

At the same state, source occurrence, key, inputs and resolved frame, moving
visible declarations or where clauses changes neither complete child output nor
computed ordinary terms. This is exact package equality, not final-state or
candidate-selection independence. Unsupported materialization stays deferred.
-/
namespace Yulang.GeneralDictionaryVariableOrder
open GeneralDeclarations GeneralDeclarationDemands GeneralSourceDictionaries
open GeneralRegistryReordering GeneralDictionaryEmissionPlans
open GeneralDictionaryVariablePlans (Result)
open GeneralDictionaryBinderLocations (Inputs)
open GeneralSourceState (State)
open GeneralDictionaryAssociatedProvenance (Body)
open Core.PresenceGeneration (TyTerm)
variable {roles : Roles.RoleDecls} {state : State}

theorem bodyTerm_reorders (order : DeclarationReorders first last)
    (capture : Capture) (body : Body) :
    GeneralDictionaryVariableTerms.bodyTerm first capture body =
      GeneralDictionaryVariableTerms.bodyTerm last capture body := by
  rw [declarationReorders_update order]
  rfl

theorem term_lookup_reorders (roles : Roles.RoleDecls)
    (order : DeclarationReorders first last) (capture : Capture) (name : Nat) :
    GeneralDictionaryVariableTerms.lookup roles first capture name =
      GeneralDictionaryVariableTerms.lookup roles last capture name := by
  unfold GeneralDictionaryVariableTerms.lookup
  rw [GeneralDictionaryAssociatedProvenance.lookup_reorders roles order name]
  apply congrArg
  funext body
  exact bodyTerm_reorders order capture body

theorem compile_reorders (roles : Roles.RoleDecls) (state : State)
    (order : DeclarationReorders first last) (capture : Capture) (name : Nat) :
    GeneralDictionaryVariableTerms.compile state roles first capture name =
      GeneralDictionaryVariableTerms.compile state roles last capture name := by
  unfold GeneralDictionaryVariableTerms.compile
  rw [term_lookup_reorders roles order capture name]

theorem build_reorders (order : DeclarationReorders first last)
    (capture : Capture) (inputs : Inputs state demand) :
    GeneralDictionaryVariableTerms.build first capture inputs =
      GeneralDictionaryVariableTerms.build last capture inputs := by
  unfold GeneralDictionaryVariableTerms.build
  simp only [compile_reorders _ _ order capture]

/-- Transport retains the entire computed result, including unsupported cases
at the unchanged source state and source identities. -/
theorem lookup_reorders_forward (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frame : Frame roles) (root : Occurrence roles) (key : Nat)
    (inputs : Inputs state root.demand) (result : Result state root)
    (found : GeneralDictionaryVariablePlans.lookup ⟨constructors, roles, first⟩ one frame root key inputs = some result) :
    GeneralDictionaryVariablePlans.lookup ⟨constructors, roles, last⟩ two frame root key inputs = some result := by
  obtain ⟨declaration, present, identity, role, built, generated⟩ :=
    (GeneralDictionaryVariablePlans.lookup_exact _ one frame root key inputs result).mp found
  obtain ⟨other, member, reordered⟩ := reorders_visible order declaration present
  apply (GeneralDictionaryVariablePlans.lookup_exact _ two frame root key inputs result).mpr
  refine ⟨other, member, reordered.id.symm.trans identity, reordered.role.symm.trans role, ?_, ?_⟩
  · rw [← reordered.id, ← build_reorders reordered]
    exact built
  · exact generated.trans (children_reorders frame root reordered
      (one.2 declaration present) (two.2 other member))

/-- Successful complete results and `none` are both invariant. No survivor or
head-applicability claim is inferred from this fixed-input property. -/
theorem lookup_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frame : Frame roles) (root : Occurrence roles) (key : Nat)
    (inputs : Inputs state root.demand) :
    GeneralDictionaryVariablePlans.lookup ⟨constructors, roles, first⟩ one frame root key inputs =
      GeneralDictionaryVariablePlans.lookup ⟨constructors, roles, last⟩ two frame root key inputs := by
  cases found : GeneralDictionaryVariablePlans.lookup ⟨constructors, roles, first⟩ one frame root key inputs with
  | some result =>
      exact (lookup_reorders_forward constructors roles first last one two order frame root key inputs result found).symm
  | none =>
      cases other : GeneralDictionaryVariablePlans.lookup ⟨constructors, roles, last⟩ two frame root key inputs with
      | none => rfl
      | some result =>
          have backward := lookup_reorders_forward constructors roles last first two one
            (GeneralRegistryChildOrder.reorders_symm order) frame root key inputs result other
          rw [found] at backward
          cases backward

end Yulang.GeneralDictionaryVariableOrder
