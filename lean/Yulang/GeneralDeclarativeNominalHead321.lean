import Yulang.GeneralDeclarativeNominalProjection321
import Yulang.GeneralDeclarativeNormalizedCompiler321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNominalHead321
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models backed_iff)
open GeneralDeclarativeTrace321 (Trace Links trace_model)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeNominalProjection321 (nominal_center)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized translate_value)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarationPatterns (normalize)

/-- The compiler sees an actual invariant head even if the center is not
recorded and the upper parameter names are different. Only the lower
head walk supplies capture identities, and it must have supported origins. -/
theorem supported_nominal_head (p : Supported s completed)
    (bounds : Bounds s arg)
    (lower : (⟨arg.lower,.nominal tag xs⟩ : Equation) ∈ (restriction p).equations)
    (upper : (⟨arg.upper,.nominal other ys⟩ : Equation) ∈ s.equations)
    (original : translate catalogue interp pattern = some originalCode)
    (normalized : translate catalogue interp (normalize pattern) = some normalizedCode)
    (trace : Trace (restriction p) .actual arg.lower normalizedCode seen)
    (shared : Links (restriction p) capture seen) :
    Result s (headFact catalogue interp capture arg pattern) := by
  refine ⟨[⟨arg.center,logical capture .actual originalCode⟩],by simp [headFact,original],?_⟩
  intro row included m valid
  cases List.mem_singleton.mp included
  simp only [Holds,logical_value]
  have lo := p.ordinary ((backed_iff p _).mp lower).choose_spec.1
  have center := nominal_center bounds lo upper m valid
  have actualLower := trace_model m (restrict_models p m valid) capture trace shared
  rw [translate_value (normalize pattern) normalized] at actualLower
  refine eqv_trans center (eqv_trans (eqv_symm (valid.2 _ lo)) ?_)
  exact eqv_trans actualLower (eqv_symm (compiled_normalized (variables := variables capture m) original))

end Yulang.GeneralDeclarativeNominalHead321
