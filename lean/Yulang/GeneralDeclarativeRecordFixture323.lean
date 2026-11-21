import Yulang.GeneralDeclarativeRecordHead323
import Yulang.GeneralDeclarativeExampleSource320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordFixture323
open GeneralDeclarativeExampleSource320 (registry interp point int)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordHead323 (head)
open GeneralDeclarativeEntailment320 (literal)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (record)

abbrev terminal : Expr := .primitive .exactEmpty []
abbrev fields : List (Nat × Expr) := [(9,.variable 51),(7,.variable 3)]
abbrev written : List (Nat × Expr) := [(7,.variable 0)]
abbrev source : Pattern := .record 7 (.var 0) (.var 1)
abbrev capture : Nat → GeneralDeclarativeWhere319.Capture := fun n => point (if n = 0 then 3 else 4)
abbrev state : State := ⟨⟨[],[]⟩,
  [⟨0,withTail fields terminal⟩,⟨4,withTail [(9,.variable 51)] terminal⟩]⟩

theorem based_on_actual_remainder :
    Result state (headFact registry.constructors interp capture (point 0) source) := by
  refine head fields written terminal (by decide +kernel) (literal List.mem_cons_self)
    (literal (List.mem_cons_of_mem _ List.mem_cons_self)) ?_ rfl rfl
  intro m valid
  exact .cons ⟨rfl,eqv_refl _⟩ .nil

def model : Assignment := fun n =>
  (if n = 0 then record 9 int (record 7 int .exactEmpty)
   else if n = 4 then record 9 int .exactEmpty
   else int, Common.rowEmpty)

theorem fits : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ bad => False.elim (List.not_mem_nil bad)⟩,?_⟩
  intro eq there
  rcases List.mem_cons.mp there with rfl|later
  · exact eqv_refl _
  · cases List.mem_singleton.mp later
    exact eqv_refl _

theorem closed_nonempty :
    Models state model ∧ Result state (headFact registry.constructors interp capture (point 0) source) :=
  ⟨fits,based_on_actual_remainder⟩

end Yulang.GeneralDeclarativeRecordFixture323
