import Yulang.GeneralDeclarativeRecordDecl326
import Yulang.GeneralDeclarativeRecordK2326
import Yulang.GeneralDeclarativeOutputOrigins323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordState326
open GeneralDeclarativeRecordDecl326
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeFreshTail326 (tailRow extended Closed materialize)
open GeneralDeclarativeVisibleRecord326 (visible_spine)
open GeneralDeclarativeRecordK2326 (row)
open GeneralDeclarativeExampleSource320 (point int)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativeEntailment320 (Entails appendFacts model_append conservative_append)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (record emptyRecord)

abbrev rawNames : List (Nat × Nat) := [(7,3),(7,0),(8,4)]
abbrev raw : List (Nat × Expr) := rawNames.map (fun v => (v.1,.variable v.2))
abbrev terminal : Expr := .primitive .emptyRecord []
abbrev sourceRow : Equation := ⟨0,row rawNames⟩
abbrev lower3 : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev lower4 : Equation := ⟨4,.primitive (.scalar .bool) []⟩
abbrev rawState : State := ⟨⟨[],[]⟩,[sourceRow,lower3,lower4]⟩
abbrev tail := tailRow rawState [5,6] 0 raw [7] terminal
abbrev afterTail := extended rawState [5,6] 0 raw [7] terminal
abbrev readRow : Equation := ⟨0,.record 7 (.variable 3) (.variable 7)⟩
abbrev projected := appendFacts afterTail [readRow]
abbrev parentRow : Equation := ⟨6,.variable 7⟩
abbrev childRow : Equation := ⟨5,.variable 3⟩
abbrev final := appendFacts (appendFacts projected [parentRow]) [childRow]

theorem tail_exact : tail = ⟨7,.record 8 (.variable 4) terminal⟩ := rfl

theorem reconstructed : Entails afterTail readRow :=
  materialize [5,6] raw [7] .width (.row (show sourceRow ∈ rawState.equations from List.mem_cons_self))

theorem new_names_only : ∀ m, Models projected m ↔ Models afterTail m :=
  conservative_append (fun _ h => by cases List.mem_singleton.mp h; exact reconstructed)

abbrev sourceFacts := [sourceRow,lower3,lower4,tail,readRow]
def support0 (done : Nat → Prop) : Supported projected done :=
  ⟨fun eq origin => eq ∈ sourceFacts ∧ origin = .source,fun h => h.1⟩
abbrev support2 (done : Nat → Prop) := emit (emit (support0 done) 1 [parentRow]) 2 [childRow]

theorem authorized (done : Nat → Prop) {eq : Equation} (stored : eq ∈ sourceFacts) :
    eq ∈ (restriction (support2 done)).equations :=
  from_source _ (.inl (.inl ⟨stored,rfl⟩))

theorem point_bound (n : Nat) : Bounds final (point n) := ⟨.refl _,.refl _⟩

abbrev flag : CommonNominalFullCarrier.Ty := .base .bool
abbrev tailType := record 8 flag emptyRecord
abbrev rootType := record 7 int tailType

def model : Assignment := fun n =>
  (if n = 0 then rootType else if n = 6 ∨ n = 7 then tailType else if n = 4 then flag else int,
    Common.rowEmpty)

theorem raw_models : Models rawState model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ h => False.elim (List.not_mem_nil h)⟩,?_⟩
  intro row hit
  change row ∈ [sourceRow,lower3,lower4] at hit
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with rfl|rfl|rfl
  · exact eqv_symm (visible_spine model raw terminal)
  · exact eqv_refl _
  · exact eqv_refl _

theorem populated : Models final model := by
  have hasTail : Models afterTail model := (model_append _).mpr ⟨raw_models,fun row h => by
    cases List.mem_singleton.mp h
    exact eqv_refl _⟩
  have withRead : Models projected model := (new_names_only model).mpr hasTail
  apply (model_append _).mpr
  refine ⟨(model_append _).mpr ⟨withRead,?_⟩,?_⟩
  all_goals
    intro row allowed
    cases List.mem_singleton.mp allowed
    exact eqv_refl _

end Yulang.GeneralDeclarativeRecordState326
