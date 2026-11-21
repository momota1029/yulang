import Yulang.GeneralDeclarativeTermWalk322
import Yulang.GeneralDeclarativeHeadCases321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTermHead322
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeTermWalk322 (Walk Binds actual_head_eq)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (translate_value compiled_normalized)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Constructors Pattern normalize)

def Actual (s : State) (capture : Nat → Capture) (arg : Capture) (code : Expr) : Prop :=
  ∃ term seen, Derives s (.variable arg.center) term ∧ Walk .actual term code seen ∧ Binds s capture seen

/-- The source observer may retain compound terms rather than flattening
them into intermediate names. The mode-correct ordinary compiler equation
still follows, after source normalization and all-model substitution. -/
theorem actual_result {s : State} (original : translate c interp pattern = some raw)
    (normalized : translate c interp (normalize pattern) = some code)
    (read : Actual s capture arg code) :
    Result s (headFact c interp capture arg pattern) := by
  obtain ⟨term,seen,hasActual,matched,binds⟩ := read
  refine ⟨[⟨arg.center,logical capture .actual raw⟩],by simp [headFact,original],?_⟩
  intro row used m valid
  cases List.mem_singleton.mp used
  simp only [Holds,logical_value]
  have eq := entails (actual_head_eq hasActual matched binds) m valid
  simp only [Holds,logical_value] at eq
  rw [translate_value (normalize pattern) normalized] at eq
  exact eqv_trans eq (eqv_symm (compiled_normalized (variables := variables capture m) original))

end Yulang.GeneralDeclarativeTermHead322
