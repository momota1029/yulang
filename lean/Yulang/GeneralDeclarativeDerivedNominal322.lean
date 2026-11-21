import Yulang.GeneralDeclarativeInequality322
import Yulang.GeneralDeclarativeTermHead322
import Yulang.GeneralDeclarativeNormalSupport321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeDerivedNominal322
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeEqualities322 (Derives semantic entails)
open GeneralDeclarativeInequality322 (Le invariant_at)
open GeneralDeclarativeNormalSupport321 (NormalSupport observed restricted_valid)
open GeneralDeclarativeTermWalk322 (Walk Binds actual_head_eq)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value values)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized translate_value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralNominalIntervalLaws (nominal_sandwich)

/-- The lower equation is an actual derived observation, not necessarily a
literal row. The upper equation is used only for invariance of the actual
type; it does not authorize considering a candidate. -/
theorem center_observed {s : State} {arg : Capture}
    (p : NormalSupport s completed) (bounds : Bounds s arg)
    (lo : Derives (observed p) (.variable arg.lower) (.nominal left xs))
    (hi : Derives s (.variable arg.upper) (.nominal right ys))
    (m : Assignment) (valid : Models s m) :
    Equivalent (m arg.center).1 (value (environment m) .actual (.nominal left xs)) := by
  have span := bounds_sound bounds m valid
  have low := semantic lo m (restricted_valid p m valid)
  have up := semantic hi m valid
  exact (nominal_sandwich left right
    ((values (environment m) .actual xs).map Sum.inl)
    ((values (environment m) .actual ys).map Sum.inl) _
    (subtype_trans low.2 span.1) (subtype_trans span.2 up.1)).1

theorem head_row {s : State} {capture : Nat → Capture} {arg : Capture}
    (p : NormalSupport s completed) (bounds : Bounds s arg)
    (lo : Derives (observed p) (.variable arg.lower) (.nominal left xs))
    (hi : Derives s (.variable arg.upper) (.nominal right ys))
    (original : translate c interp pattern = some raw)
    (normalized : translate c interp (normalize pattern) = some code)
    (walk : Walk .actual (.nominal left xs) code seen)
    (linked : Binds (observed p) capture seen) :
    Result s (headFact c interp capture arg pattern) := by
  refine ⟨[⟨arg.center,logical capture .actual raw⟩],by simp [headFact,original],?_⟩
  intro eq inBatch m valid
  cases List.mem_singleton.mp inBatch
  have one := center_observed p bounds lo hi m valid
  have lowered := semantic (GeneralDeclarativeTermWalk322.substitute walk linked) m (restricted_valid p m valid)
  rw [logical_value,translate_value (normalize pattern) normalized] at lowered
  simp only [Holds,logical_value]
  exact eqv_trans (eqv_trans one lowered)
    (eqv_symm (compiled_normalized (variables := variables capture m) original))

end Yulang.GeneralDeclarativeDerivedNominal322
