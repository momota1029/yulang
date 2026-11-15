import Yulang.GeneralDictionaryDefaultEvidence204
import Yulang.GeneralDictionaryAllocDefaultSource202

set_option backward.isDefEq.respectTransparency false

/-! Explicit, default, and overriding bodies use the same total-expression
meaning. These are source-output examples, independent of candidate selection. -/
namespace Yulang.GeneralDictionaryDefaultEvidence204Outputs
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryDefaultEvidence204 GeneralDictionaryAssociatedProvenance
open GeneralNominalCenteredHeadMatEffects GeneralNominalCenteredHeadMatExpressions
open GeneralDeclarationExamples (constructors)
open GeneralDictionaryAllocDefaultSource202 (context model)
open CommonNominalFullCarrier

def roles (fallback : Bool) : Roles.RoleDecls := fun _ =>
  { arity := 1
    assoc := fun name => if name = 0 then some (if fallback then some (.var 0) else none) else none
    defaultsScoped := by
      intro name rhs found
      split at found
      · cases fallback <;> simp at found
        cases found; simp [Roles.Term.bound]
      · cases found }

abbrev equation : Equation := ⟨17,0,.app 2 []⟩
abbrev declaration : Declaration := ⟨38,0,[.app 2 []],[],[equation],[]⟩
abbrev registry (fallback : Bool) : Registry := ⟨constructors,roles fallback,[declaration]⟩

theorem checked (fallback : Bool) : DeclarationChecked constructors (roles fallback) declaration := by
  constructor
  · refine ⟨rfl,?_,?_,by simp⟩
    · intro e member
      cases List.mem_singleton.mp member
      exact ⟨_,rfl⟩
    · intro name body found
      change (if name = 0 then _ else none) = some body at found
      split at found
      · rename_i same
        exact Or.inl ⟨equation,List.mem_singleton_self _,same.symm⟩
      · cases found
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables,equation]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,equation]
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member

abbrev root (fallback : Bool) : Occurrence (roles fallback) :=
  ⟨100,⟨0,fun _ => (1,1),[⟨0,1⟩],by
    intro output member
    cases List.mem_singleton.mp member
    exact ⟨_,rfl⟩⟩⟩
abbrev packet (fallback : Bool) : GeneralNominalSaturationState.Packet (roles fallback) :=
  ⟨registry fallback,context,GeneralNominalDemandMerging.pointSite (root fallback),declaration,checked fallback,[(1,1)]⟩
abbrev plan (fallback : Bool) : Plan (roles fallback) :=
  ⟨packet fallback,rootSite context.state.seed (root fallback),rfl⟩

theorem explicit_lookup : lookup (roles false) declaration 0 = some (.explicit equation) := rfl

theorem override_lookup : lookup (roles true) declaration 0 = some (.explicit equation) := rfl

theorem explicit_total (fallback : Bool) :
    compileBody (plan fallback) (.explicit equation) = some (.primitive (.scalar .int) []) := rfl

theorem explicit_body_holds (fallback : Bool) : BodyHolds (plan fallback) 1 model (.explicit equation) := by
  apply (body_equation (explicit_total fallback)).mpr
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem explicit_output : OutputWitness (plan false) model ⟨0,1⟩ :=
  ⟨.explicit equation,.explicit equation (List.mem_singleton_self _) rfl,
    ⟨_,explicit_total false⟩,explicit_body_holds false⟩

theorem override_output : OutputWitness (plan true) model ⟨0,1⟩ :=
  ⟨.explicit equation,.explicit equation (List.mem_singleton_self _) rfl,
    ⟨_,explicit_total true⟩,explicit_body_holds true⟩

/-- A role default is present, yet may not be used when the implementation
supplies a body of the same name. -/
theorem override_excludes_default (body : Roles.Term) :
    ¬ Supplies (roles true) declaration 0 (.default 0 0 body) := by
  intro supplied
  cases supplied with
  | default rhs absent _ => exact absent equation (List.mem_singleton_self _) rfl

end Yulang.GeneralDictionaryDefaultEvidence204Outputs
