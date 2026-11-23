import Yulang.GeneralDeclarativeWitnessOrderedReport358
import Yulang.GeneralDeclarativeWitnessRecursiveModel358

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 61000
set_option maxHeartbeats 79000000
namespace Yulang.GeneralDeclarativeWitnessRecursiveFixture358
open GeneralDeclarativeWitnessRecursiveSeed358 (Data data author recipe parentLayout childLayout)
open GeneralDeclarativeWitnessRecursiveModel358 (model fits)
open GeneralDeclarativeWitnessDeclaredState357 (ModelsCurrent)
open GeneralDeclarativeWitnessJoinedFixture357 (root written)
open GeneralDeclarativeWitnessOrderedReplay358 (Code LayoutAt)
open GeneralDeclarativeWitnessOrderedReport358 (Packet verify Checked report_sound)
open GeneralDeclarativeWitnessOrderedMeaning358 (Entry dict)
open GeneralDeclarativeWitnessProjectionRule358 (Rule Evidence)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeWitnessReifiedViews357 (modelViews)
open CommonRoleOutermostResolver (Classify Dictionary Result)

def atLayouts (d : Data) : LayoutAt :=
  fun path => if path = [5] then parentLayout else childLayout d.first

def code (d : Data) : Code :=
  .node (.join written) d.parentWire
    (.cons (.node (.project recipe 33) d.childWire .nil) .nil)

def output : Packet :=
  ⟨⟨.selected 92 [.selected 93 []],.selected (.node 92 [.node 93 []]),root.outputs⟩,
   [⟨[5],(5,[(20,20,20)],[(0,60)]),[⟨60,.variable 10⟩]⟩,
    ⟨[5,0],(6,[(63,10,64)],[(0,41)]),[⟨41,.variant 7 (.variable 4)⟩]⟩]⟩

def test (packet : Packet := output) (adjust : Code → Code := id) (source : Source := author) : Bool :=
  (data.map fun d => (verify source d.current (atLayouts d) [5] root (adjust (code d)) packet).isSome).getD false

theorem actual_nonpoint_selected_recursively : test = true := by decide +kernel

theorem child_cannot_be_erased : test output (fun
    | .node method response _ => .node method response .nil) = false := by decide +kernel

theorem cannot_reverse_ordered_writes : test {output with writes := output.writes.reverse} = false := by decide +kernel

theorem cannot_replace_fixed_child_target : test {output with writes :=
    (output.writes.map (fun e => if e.path = [5,0] then
      {e with equations := [⟨60,.variant 7 (.variable 4)⟩]} else e))} = false := by decide +kernel

theorem cannot_rebase_child_path : test {output with writes :=
    (output.writes.map (fun e => if e.path = [5,0] then {e with path := [0]} else e))} = false := by decide +kernel

theorem cannot_replace_selected_rule : test {output with report :=
    {output.report with result := .selected (.node 92 [.node 94 []])}} = false := by decide +kernel

theorem no_recursive_replay_without_source : test output id ⟨[]⟩ = false := by decide +kernel

theorem actual_same_model_report :
    ∃ (d : Data) (a : Checked author d.current [5] root output),data = some d ∧
      ModelsCurrent d.current model (modelViews d.current model) ∧
      Classify (Rule author d.current) root output.report.result ∧
      dict a.proof = .node 92 [.node 93 []] ∧
      Evidence author d.current model (modelViews d.current model) root (.node 92 [.node 93 []]) ∧
      ∀ row ∈ output.writes,row.Holds model := by
  have yes := actual_nonpoint_selected_recursively
  unfold test at yes
  cases actual : data with
  | none => rw [actual] at yes; cases yes
  | some d =>
    rw [actual] at yes
    have projected : (verify author d.current (atLayouts d) [5] root (code d) output).isSome = true := yes
    cases found : verify author d.current (atLayouts d) [5] root (code d) output with
    | none => rw [found] at projected; cases projected
    | some a =>
      have fit := fits actual
      obtain ⟨_,_,docs,_,chosen,proof,covered⟩ := report_sound a model (modelViews d.current model) fit
      have exactDict : dict a.proof = .node 92 [.node 93 []] := (Result.selected.inj docs).symm
      exact ⟨d,a,rfl,fit,chosen,exactDict,exactDict ▸ proof,covered⟩

end Yulang.GeneralDeclarativeWitnessRecursiveFixture358
