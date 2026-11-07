import Yulang.CommonPatternSourceArmSolved

/-! Actual concrete values are checked by the existing finite data generator,
not by a semantic predicate embedded as an atom. Named returned bindings use
the very same type references as pattern/default/guard/body generation. -/

namespace Yulang.CommonPatternRuntimeValueConstraints

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternTyping (valueAt bindingTypes)
open CommonPatternGenerationProvenance (BinderType SafeFormula GoodBindings)

def valueConstraints (value : CommonData.Value) (type : TyTerm α) : Formula α :=
  CommonPatternSourceScope.generateData [] [] (.value value) (.pure type)

/-- All real values, all Common assignments and all requested value types.
The finite formula uses ordinary constructor/type/row atoms only. -/
theorem value_constraints_exact (assignment : α → Comp Common.model) (value : CommonData.Value) (type : TyTerm α) :
    (valueConstraints value type).Holds Common.model assignment ↔ valueAt (type.eval Common.model assignment) value := by
  rw [valueConstraints, CommonPatternSourceScope.generateData_exact _ _ assignment [] [] []
    (CommonSyntax.EnvRel.nil Common.model) (EnvRel.nil Common.model assignment)]
  change CommonSyntax.Typing Common.model [] (.data value) (Comp.pure Common.model (type.eval Common.model assignment)) ↔ _
  constructor
  · intro typed; cases typed with | data valid => exact valid
  · exact CommonSyntax.Typing.data

theorem safe_valueConstraints (value : CommonData.Value) (type : TyTerm α) (good : BinderType type) :
    SafeFormula (valueConstraints value type) := by
  have environment : CommonPatternGenerationProvenance.SafeEnvironment ([] : SchemeEnv α) := by
    constructor <;> intro scheme member <;> cases member
  exact CommonPatternSourceArmSolved.safe_generateData [] environment [] (.value value) (.pure type) good rfl

def bindingConstraints : NamedTerms α → CaseValues.Bindings Empty → Formula α
  | [], [] => .top
  | (name, type) :: rest, (actualName, value) :: values =>
      if name = actualName then .and (valueConstraints value type) (bindingConstraints rest values) else .bot
  | _, _ => .bot

/-- Arbitrary literal returned names/order and real values, not merely an
existential environment with the same names. Each type reference is shared. -/
theorem binding_constraints_exact (assignment : α → Comp Common.model)
    (types : NamedTerms α) (actual : CaseValues.Bindings Empty) :
    (bindingConstraints types actual).Holds Common.model assignment ↔
      CaseValues.BindingsHold (bindingTypes (evalTypes assignment types)) actual := by
  induction types generalizing actual with
  | nil =>
      cases actual with
      | nil => exact ⟨fun _ => .nil, fun _ => True.intro⟩
      | cons binding rest => exact ⟨False.elim, fun typed => by cases typed⟩
  | cons binding rest ih =>
      rcases binding with ⟨name, type⟩
      cases actual with
      | nil => exact ⟨False.elim, fun typed => by cases typed⟩
      | cons binding values =>
          rcases binding with ⟨actualName, value⟩
          by_cases same : name = actualName
          · subst actualName
            simp only [bindingConstraints, ↓reduceIte, Formula.Holds, value_constraints_exact, ih]
            constructor
            · rintro ⟨head, tail⟩; exact .cons head tail
            · intro typed; cases typed with | cons head tail => exact ⟨head, tail⟩
          · simp only [bindingConstraints, same, ↓reduceIte, Formula.Holds]
            constructor
            · exact False.elim
            · intro typed
              cases typed
              exact same rfl

theorem safe_bindingConstraints (types : NamedTerms α) (good : GoodBindings types)
    (actual : CaseValues.Bindings Empty) : SafeFormula (bindingConstraints types actual) := by
  induction types generalizing actual with
  | nil => cases actual <;> first | exact .top | exact .bot
  | cons binding rest ih =>
      rcases binding with ⟨name, type⟩
      cases actual with
      | nil => exact .bot
      | cons binding values =>
          simp only [bindingConstraints]
          split
          · exact .and (safe_valueConstraints _ type (good (name, type) List.mem_cons_self))
              (ih (fun binding member => good binding (List.mem_cons_of_mem _ member)) values)
          · exact .bot

end Yulang.CommonPatternRuntimeValueConstraints
