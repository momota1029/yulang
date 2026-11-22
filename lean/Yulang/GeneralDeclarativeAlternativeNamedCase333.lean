import Yulang.GeneralDeclarativeAlternativeNamedHeads333
import Yulang.GeneralDeclarativeNestedExample332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeNamedCase333
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeAlternativeView333 (ofTable Index)
open GeneralDeclarativeAlternativeNamedHeads333 (normalized)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeTrace321 (Occurrence Trace)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeExampleSource320 (int)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarationPatterns (Pattern)
open CommonNominalFullCarrier (Ty exactEmpty record)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev rootRow : Equation := ⟨0,.record 7 (.variable 3) (.variable 4)⟩
abbrev scalar : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev state : State := ⟨⟨[],[]⟩,[rootRow,scalar]⟩
abbrev pat : Pattern := .record 7 (.var 0) (.var 1)
abbrev code : Expr := .record 7 (.variable 0) (.variable 1)
abbrev reads : List Occurrence := [⟨0,.actual,3⟩,⟨1,.actual,4⟩]
def source : Index state := ofTable state.equations (fun _ x => x) []

theorem has_exact_old_actual : normalized source 4 constructors interpretation .actual 0 pat = [reads] := rfl

theorem cannot_assume_closed_tail :
    GeneralDeclarativeAlternativeRead333.normalized source 4 constructors interpretation .actual (.variable 0) pat =
      [] := rfl

theorem both_source_modes_not_interchangeable :
    (∃ old, old ∈ normalized source 4 constructors interpretation .actual 0 pat) ∧
    GeneralDeclarativeAlternativeRead333.normalized source 4 constructors interpretation .actual (.variable 0) pat =
      [] :=
  ⟨⟨reads,has_exact_old_actual.symm ▸ List.mem_cons_self⟩,cannot_assume_closed_tail⟩

def model : Assignment := fun n =>
  (if n = 0 then record 7 int exactEmpty else if n = 4 then exactEmpty else int,Common.rowEmpty)

theorem actual_ordinary_model : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ no => False.elim (List.not_mem_nil no)⟩,?_⟩
  intro known used
  rcases List.mem_cons.mp used with rfl|other
  · exact eqv_refl _
  · cases List.mem_singleton.mp other
    exact eqv_refl _

end Yulang.GeneralDeclarativeAlternativeNamedCase333
