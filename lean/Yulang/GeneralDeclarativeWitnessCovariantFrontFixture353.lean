import Yulang.GeneralDeclarativeWitnessCovariantFront353
import Yulang.GeneralDeclarativeWitnessCovariantWrittenFixture353
import Yulang.GeneralDeclarativeWitnessCovariantIntervalNestedModel353

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 38000
set_option maxHeartbeats 31000000
namespace Yulang.GeneralDeclarativeWitnessCovariantFrontFixture353
open GeneralDeclarativeWitnessCovariantFront353 (Input Result decode exact_author_report)
open GeneralDeclarativeWitnessCovariantWrittenFixture353 (intervalLines)
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line printRow)
open GeneralDeclarativeWitnessCovariantIntervalNested353 (rootProblem data report environment)
open GeneralDeclarativeWitnessCovariantIntervalNestedModel353 (model model_fits)
open GeneralDeclarativeWitnessCovariantIntervalForest353 (Wire)
open GeneralDeclarativeWitnessCompiler350 (Finished)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open CommonRoleOutermostResolver (All₂)

def problem (f : Finished) : Input :=
  ⟨rootProblem,intervalLines,(environment f).origins,(environment f).layout⟩

def check (f : Input → Input := id) : Bool :=
  (data.map fun (top,s,w) => (decode (f (problem top)) s w report).isSome).getD false

theorem accepted_authored_nonpoint_forest : check = true := by decide +kernel

theorem cannot_replace_typed_current_center :
    check (fun p => {p with written := intervalLines.take 2 ++
      [⟨99,.variant 13 (.app 0 [.var 9])⟩] ++ intervalLines.drop 3}) = false := by decide +kernel

theorem withheld_author_variance_cannot_be_guessed :
    check (fun p => {p with base := {p.base with metadata := {p.base.metadata with variance := []}}}) = false := by decide +kernel

theorem concrete_full_path :
    ∃ (top : Finished) (s : State) (w : Wire) (a : Result (problem top) s w report),
      data = some (top,s,w) ∧ Models s model ∧ a.typed.rows.map printRow = intervalLines ∧
      a.receipt.children.entries = [.node 93 [],.node 94 []] ∧
      All₂ (Evidence (registry a.receipt.ordinary) (interpretation a.receipt.ordinary.snapshot) model)
        a.receipt.root.compiler.compiled.kids [.node 93 [],.node 94 []] ∧
      w.rootOut.outputRows.map Equation.left = [5,6] ∧
      ∀ e ∈ w.rootOut.outputRows,Holds model e := by
  have ok := accepted_authored_nonpoint_forest
  unfold check at ok
  cases got : data with
  | none => simp [got] at ok
  | some pack =>
    obtain ⟨top,s,w⟩ := pack
    have accepts : (decode (problem top) s w report).isSome = true := by simpa [got] using ok
    cases exact : decode (problem top) s w report with
    | none => simp [exact] at accepts
    | some a =>
      have fit := model_fits got
      obtain ⟨printed,selected,_,children,targets,writes⟩ := exact_author_report a model fit
      change CommonRoleOutermostResolver.Result.selected (.node 92 [.node 93 [],.node 94 []]) =
        .selected (.node a.receipt.root.facts.center.decl.id a.receipt.children.entries) at selected
      have dict := (CommonRoleOutermostResolver.Dictionary.node.inj
        (CommonRoleOutermostResolver.Result.selected.inj selected)).2.symm
      rw [dict] at children
      exact ⟨top,s,w,a,rfl,fit,printed,dict,children,targets,writes⟩

end Yulang.GeneralDeclarativeWitnessCovariantFrontFixture353
