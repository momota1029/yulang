import Yulang.GeneralDeclarativeNestedDecode332
import Yulang.GeneralDeclarativeInlineCompiler331

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeNestedExample332
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeNestedDecode332 (normalized normalized_sound)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open GeneralDeclarativeInlineCompiler331 (Source)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarationExamples (constructors)

def interpretation : Interpretation :=
  ⟨fun n => if n = 5 then some .pair else none,fun n => n == 0,by
    intro n top
    have hn : n = 0 := by simpa using top
    simp [hn]⟩

abbrev terminal : Expr := .primitive .exactEmpty []
abbrev innerResidual : Expr := .record 6 (.variable 12) terminal
abbrev outerResidual : Expr := .record 9 (.variable 15) terminal
abbrev inner : Expr := .record 3 (.nominal 0 [.variable 11])
  (.record 3 (.variable 12) innerResidual)
abbrev outer : Expr := .record 7 (.variant 4 (.primitive .pair [.variable 3,.variable 14]))
  (.record 7 (.variable 15) outerResidual)
abbrev pat : Pattern := .record 7
  (.variant 4 (.app 5 [.var 0,.record 3 (.app 0 [.var 3]) (.var 4)])) (.var 1)
abbrev outerRow : Equation := ⟨0,outer⟩
abbrev innerRow : Equation := ⟨14,inner⟩
abbrev scalar : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev rows : List Equation := [outerRow,innerRow,scalar]
abbrev state : State := ⟨⟨[],[]⟩,rows⟩

def supports (done : Nat → Prop) : Supported state done :=
  ⟨fun e origin => e ∈ rows ∧ origin = .source,fun h => h.1⟩

def visible (n : Nat) : Option Expr := if n = 0 then some outer else if n = 14 then some inner else none

def indexed (done : Nat → Prop) : Sources (restriction (supports done)) :=
  ⟨visible,by
    intro n rhs result
    by_cases r : n = 0
    · subst n
      have eq : outer = rhs := Option.some.inj result
      subst rhs
      exact ⟨0,alias_refl _,from_source _ ⟨List.mem_cons_self,rfl⟩⟩
    · by_cases k : n = 14
      · subst n
        have eq : inner = rhs := Option.some.inj result
        subst rhs
        exact ⟨14,alias_refl _,from_source _ ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩⟩
      · simp [visible,r,k] at result,
    fun _ => none,fun _ _ _ h => by cases h⟩

def uses (mode : Mode) : List Occurrence :=
  [⟨0,mode,.variable 3⟩,⟨3,.actual,.variable 11⟩,⟨4,mode,innerResidual⟩,⟨1,mode,outerResidual⟩]

theorem actual_lower (done : Nat → Prop) :
    normalized (indexed done) constructors interpretation .lower (.variable 0) pat = some (uses .lower) := rfl
theorem actual_upper (done : Nat → Prop) :
    normalized (indexed done) constructors interpretation .upper (.variable 0) pat = some (uses .upper) := rfl
theorem actual_center (done : Nat → Prop) :
    normalized (indexed done) constructors interpretation .actual (.variable 0) pat = some (uses .actual) := rfl

theorem observed_endpoints (done : Nat → Prop) :
    Matches (restriction (supports done)) constructors interpretation (point 0) pat := by
  obtain ⟨l,printL,lo⟩ := normalized_sound (actual_lower done)
  obtain ⟨h,printH,hi⟩ := normalized_sound (actual_upper done)
  have same := Option.some.inj (printL.symm.trans printH)
  exact ⟨point_bounded _ _,l,_,_,printL,lo,same.symm ▸ hi⟩

/-- The result comes from independently computing on the actual source:
the nested invariant argument changes only its own mode, the two
closed residuals remain distinct, and the inner row was opened from a
real stored source RHS rather than a proposed child. -/
theorem observed_center (done : Nat → Prop) :
    Source (supports done) constructors interpretation [point 0] [pat] := by
  obtain ⟨_,written,read⟩ := normalized_sound (actual_center done)
  exact .inline (point_bounded _ _) written read .nil

end Yulang.GeneralDeclarativeNestedExample332
