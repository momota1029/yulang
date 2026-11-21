import Yulang.GeneralDeclarativeHiddenWhere324
import Yulang.GeneralDeclarativeDerivedSource325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNamedAliasState325
open GeneralDeclarativeHiddenWhere324 (root child parent implementation registry)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation empty normCode normal_compiles)
open GeneralDeclarativeHiddenState324 (direct opened regularRecord)
open GeneralDeclarativeExampleSource320 (int point)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeClauseOrigins325 (Origin origin_reads)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)

abbrev rows : List Equation :=
  [⟨0,opened⟩,⟨0,direct⟩,⟨2,empty⟩,⟨3,.primitive (.scalar .int) []⟩,
   ⟨6,.variable 53⟩,⟨53,.variable 3⟩,⟨55,.variable 54⟩,⟨54,direct⟩]
abbrev ordinary : State := ⟨⟨[],[]⟩,rows⟩
def sources (completed : Nat → Prop) : Supported ordinary completed :=
  ⟨fun row o => row ∈ rows ∧ o = .source,fun h => h.1⟩

theorem retained (completed : Nat → Prop) {row : Equation} (inState : row ∈ rows) :
    row ∈ (restriction (sources completed)).equations := from_source _ ⟨inState,rfl⟩

abbrev rootOut : Equation := ⟨6,.variable 3⟩
abbrev childOut : Equation := ⟨55,direct⟩

theorem literal_absent : rootOut ∉ ordinary.equations ∧ childOut ∉ ordinary.equations := by
  constructor
  all_goals
    intro conflict
    change _ ∈ rows at conflict
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at conflict
    rcases conflict with h|h|h|h|h|h|h|h
    all_goals cases h

theorem named_where_alias : Origin ordinary 55 direct :=
  ⟨54,.forward (by simp [rows]),by simp [rows]⟩

theorem child_derived : Derives ordinary (.variable childOut.left) childOut.right :=
  origin_reads named_where_alias

theorem parent_derived : Derives ordinary (.variable rootOut.left) rootOut.right :=
  .trans (b := .variable 53) (.row (by simp [rows])) (.row (by simp [rows]))

def assignment : Assignment := fun n =>
  (if n = 0 ∨ n = 54 ∨ n = 55 then regularRecord else if n = 2 then
    CommonNominalFullCarrier.emptyRecord else int,Common.rowEmpty)

theorem populated : Models ordinary assignment := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro _ impossible
    cases impossible
  · intro row h
    change row ∈ rows at h
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

end Yulang.GeneralDeclarativeNamedAliasState325
