import Yulang.GeneralDeclarativeSupportedReads321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCenterEntails321
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeSubstitution320 (EquationRead equation_read logical logical_value)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeNormalized320 (Center center_sound)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralNominalCenteredHeadMatExpressions (translate)

theorem center_entails {s : State} (read : Center s capture arg code) :
    Entails s ⟨arg.center,logical capture .actual code⟩ := by
  intro m valid
  simp only [Holds,logical_value]
  exact center_sound read m valid

theorem supported_center (p : Supported s completed)
    (read : Center (restriction p) capture arg code) :
    Entails s ⟨arg.center,logical capture .actual code⟩ := by
  intro m valid
  exact center_entails read m (restrict_models p m valid)

def HeadDerivation (s : State) (catalogue : GeneralDeclarationPatterns.Constructors) (interp : GeneralNominalInspection.Interpretation) (capture : Nat → GeneralDeclarativeWhere319.Capture) (arg : GeneralDeclarativeWhere319.Capture) (pattern : GeneralDeclarationPatterns.Pattern) : Prop :=
  ∃ code, translate catalogue interp pattern = some code ∧ Center s capture arg code

theorem actual_head_row (p : Supported s completed)
    (read : HeadDerivation (restriction p) catalogue interp capture arg pattern) :
    ∃ rows, headFact catalogue interp capture arg pattern = some rows ∧ ∀ row ∈ rows, Entails s row := by
  obtain ⟨code,compiled,derived⟩ := read
  refine ⟨[⟨arg.center,logical capture .actual code⟩],by simp [headFact,compiled],?_⟩
  intro row repeated
  have eq := List.mem_singleton.mp repeated
  subst row
  exact supported_center p derived

end Yulang.GeneralDeclarativeCenterEntails321
