import Yulang.GeneralDeclarativePlainCapture323
import Yulang.GeneralDeclarativeExampleSource320
import Yulang.GeneralDeclarativeRepeat320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePlainFixture323
open GeneralDeclarativeExampleSource320 (registry interp point)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativePlainCapture323 (actual_probe tag_head WholeNames)
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeEntailment320 (Entails Holds literal)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeRepeat320 (int int_top top_not_int)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent variant common_union_is_join subtype_refl)

abbrev merged : Pattern := .join (.var 0) (.var 1)
abbrev source : Pattern := .join (.variant 7 (.var 0)) (.variant 7 (.var 1))
abbrev decl : Declaration := ⟨84,0,[source],[],[],[]⟩
abbrev logicalPayload : Expr := .variable 5
abbrev goalRow : GeneralDeclarativeHead320.Equation := ⟨0,.variant 7 logicalPayload⟩

theorem normalized : normalize source = .variant 7 merged := by decide +kernel

theorem actual_source_lowering :
    GeneralNominalInspection.translate registry.constructors interp (normalize source) =
      .node (.variant 7) [.variables [0,1]] := by rw [normalized]; exact actual_probe rfl

theorem declaration_checked : DeclarationChecked registry.constructors registry.roles decl := by
  constructor
  · refine ⟨rfl,by simp,?_,by simp⟩
    intro name body declared
    cases declared
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.variablesArgs,Pattern.variables,normalized]
  · simp [Declaration.ConstructorScoped,GeneralDeclarationPatterns.ArgsWellScoped,GeneralDeclarationPatterns.WellScoped]
  all_goals intro clause present; cases present

def state : State := ⟨⟨[],[]⟩,[goalRow]⟩

abbrev both : Nat → GeneralDeclarativeWhere319.Capture := fun _ => point 5
abbrev split : Nat → GeneralDeclarativeWhere319.Capture := fun n => point (if n = 0 then 2 else 5)

def model : Assignment := fun n =>
  (if n = 0 then variant 7 .top else if n = 5 then .top else int, Common.rowEmpty)

theorem fits : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ nowhere => False.elim (List.not_mem_nil nowhere)⟩,?_⟩
  intro row found
  cases List.mem_singleton.mp found
  exact eqv_refl _

theorem both_actual : WholeNames state both logicalPayload [0,1] :=
  fun _ _ m _ => eqv_refl (m 5).1

theorem real_head : Result state (headFact registry.constructors interp both (point 0) source) :=
  tag_head normalized rfl rfl rfl (literal List.mem_cons_self) both_actual

/-- The ordinary union equation also permits distinct assigned operands.
The source's whole-payload inspection (not this equality) rules out
splitting the merged payload into two arbitrary parts. -/
theorem union_alone_does_not_give_whole :
    Equivalent (.union (model (split 0).center).1 (model (split 1).center).1)
      (model 5).1 ∧ ¬ WholeNames state split logicalPayload [0,1] := by
  constructor
  · change Equivalent (.union int .top) .top
    exact ⟨(common_union_is_join ..).mpr ⟨int_top,subtype_refl _⟩,
      ((common_union_is_join ..).mp (subtype_refl (.union int .top))).2⟩
  · intro all
    have broken : Equivalent int .top := all 0 List.mem_cons_self model fits
    exact top_not_int broken.2

end Yulang.GeneralDeclarativePlainFixture323
