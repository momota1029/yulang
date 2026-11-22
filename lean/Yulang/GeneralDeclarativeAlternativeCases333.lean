import Yulang.GeneralDeclarativeAlternativeReadComplete333
import Yulang.GeneralDeclarativeNestedExample332

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 20000000
namespace Yulang.GeneralDeclarativeAlternativeCases333
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeAlternativeView333 (ofTable Index)
open GeneralDeclarativeAlternativeRead333 (normalized read)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeEntailment320 (appendFacts model_append conservative_append)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarationExamples (constructors)

abbrev a : Expr := .primitive .pair [.variable 3,.variable 11]
abbrev b : Expr := .primitive .pair [.variable 11,.variable 3]
abbrev joint : Expr := .join (.variable 0) (.variable 0)
abbrev duo : Expr := .primitive .pair [.variable 0,.variable 1]
abbrev two : State := ⟨⟨[],[]⟩,[⟨0,a⟩,⟨0,b⟩]⟩

def twoIndex : Index two := ofTable two.equations (fun _ h => h) []

abbrev firstPattern : Pattern := .variant 4 (.app 5 [.var 0,.var 1])
abbrev firstSpelling : Equation := ⟨0,.variable 0⟩
abbrev secondSpelling : Equation := ⟨0,.variant 4 a⟩
abbrev writerState : State := ⟨⟨[],[]⟩,[firstSpelling,secondSpelling]⟩
def actualIndex : Index writerState := ofTable writerState.equations (fun _ y => y) []

theorem first_index_sticks :
    GeneralDeclarativeNestedDecode332.normalized
      (GeneralDeclarativeNestedIndex332.ofRows writerState.equations (fun _ h => h))
      constructors interpretation .actual (.variable 0) firstPattern = none := rfl

abbrev x : List GeneralDeclarativeTermWalk322.Occurrence := [⟨0,.actual,.variable 3⟩,⟨1,.actual,.variable 11⟩]
abbrev y : List GeneralDeclarativeTermWalk322.Occurrence := [⟨0,.actual,.variable 11⟩,⟨1,.actual,.variable 3⟩]

theorem regardless_of_first :
    (normalized actualIndex 7 constructors interpretation .actual (.variable 0) firstPattern).head? =
      some x := rfl

theorem from_second :
    x ∈ normalized actualIndex 7 constructors interpretation .actual (.variable 0) firstPattern := by
  have h := regardless_of_first
  cases r : normalized actualIndex 7 constructors interpretation .actual (.variable 0) firstPattern with
  | nil => simp [r] at h
  | cons y ys =>
    have eq : y = x := by simpa [r] using h
    subst y
    exact List.mem_cons_self

theorem both_spelling_orders :
    (read twoIndex 8 .actual joint (.join duo duo)).map Subtype.val =
      [x++x,x++y,y++x,y++y] := rfl

theorem same_single_index_cannot_mix (src : GeneralDeclarativeNestedView332.Sources two) :
    GeneralDeclarativeNestedRun332.run src .actual joint
      (.join (.primitive .pair (.cons (.capture 0) (.cons (.capture 1) .nil)))
        (.primitive .pair (.cons (.capture 0) (.cons (.capture 1) .nil)))) ≠ some (x++y) := by
  let n : GeneralDeclarativeNestedSyntax332.Node := .primitive .pair (.cons (.capture 0) (.cons (.capture 1) .nil))
  change GeneralDeclarativeNestedRun332.run src .actual joint (.join n n) ≠ _
  intro h
  cases b : GeneralDeclarativeNestedRun332.run src .actual (.variable 0) n with
  | none => simp [GeneralDeclarativeNestedRun332.run,joint,GeneralDeclarativeNestedView332.expand,b] at h
  | some seen =>
    have impossible : seen ++ seen = x++y := by
      simpa [GeneralDeclarativeNestedRun332.run,joint,GeneralDeclarativeNestedView332.expand,b] using h
    have sizes := congrArg List.length impossible
    change (seen ++ seen).length = 4 at sizes
    rw [List.length_append] at sizes
    have two : seen.length = 2 := by omega
    cases seen with
    | nil => cases two
    | cons a tail =>
      cases tail with
      | nil => cases two
      | cons b others =>
        cases others with
        | nil => cases impossible
        | cons c rest => simp at two

end Yulang.GeneralDeclarativeAlternativeCases333
