import Yulang.GeneralDeclarativeWitnessSiblingModel358

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 64000
set_option maxHeartbeats 95000000
namespace Yulang.GeneralDeclarativeWitnessSiblingFixture358
open GeneralDeclarativeWitnessSiblingSeed358 (Data data layouts code shape)
open GeneralDeclarativeWitnessSiblingModel358 (model same_actual_models)
open GeneralDeclarativeWitnessRecursiveSeed358 (author)
open GeneralDeclarativeWitnessJoinedFixture357 (root)
open GeneralDeclarativeWitnessOrderedReport358 (Packet Checked verify report_sound)
open GeneralDeclarativeWitnessOrderedReplay358 (Code Codes)
open GeneralDeclarativeWitnessOrderedMeaning358 (dict Entry)
open GeneralDeclarativeWitnessProjectionRule358 (Rule Evidence)
open GeneralDeclarativeWitnessDeclaredState357 (ModelsCurrent)
open GeneralDeclarativeWitnessReifiedViews357 (modelViews)
open CommonRoleOutermostResolver (Classify Result Dictionary)

def answer : Packet :=
  ⟨⟨.selected 92 [.selected 93 [],.selected 94 []],
    .selected (.node 92 [.node 93 [],.node 94 []]),root.outputs⟩,
    [⟨[5],(5,[(20,20,20)],[(0,60)]),[⟨60,.variable 10⟩]⟩,
     ⟨[5,0],(6,[(63,10,64)],[(0,41)]),[⟨41,.variant 7 (.variable 4)⟩]⟩,
     ⟨[5,1],(7,[(61,10,62)],[(0,42)]),[⟨42,.variant 7 (.variable 4)⟩]⟩]⟩

def test (packet : Packet := answer) (edit : Code → Code := id) : Bool :=
  (data.map fun d =>
    (verify author d.current (layouts d) [5] root (edit (code d)) packet).isSome).getD false

theorem actual_written_sibling_order : shape =
    some ([(6,[(63,10,64)],[(0,41)]),(7,[(61,10,62)],[(0,42)])],[[60],[41],[42]]) := rfl

theorem actual_two_ordered_children_selected : test = true := by decide +kernel

def swapFirst (c : Code) : Code :=
  match c with
  | .node head packet (.cons first (.cons last tail)) =>
    .node head packet (.cons last (.cons first tail))
  | other => other

theorem cannot_swap_semantically_equal_payload_children : test answer swapFirst = false := by decide +kernel

theorem cannot_swap_child_dictionary :
    test {answer with report := {answer.report with result := .selected (.node 92 [.node 94 [],.node 93 []])}} =
      false := by decide +kernel

theorem cannot_swap_child_fixed_targets :
    test {answer with writes := (answer.writes.map fun row =>
      {row with equations := row.equations.map (fun item =>
        if item.left = 41 then {item with left := 42} else
        if item.left = 42 then {item with left := 41} else item)})} = false := by decide +kernel

theorem both_actual_children_in_one_native_model :
    ∃ (d : Data) (a : Checked author d.current [5] root answer),data = some d ∧
      ModelsCurrent d.current model (modelViews d.current model) ∧
      Classify (Rule author d.current) root answer.report.result ∧
      dict a.proof = .node 92 [.node 93 [],.node 94 []] ∧
      Evidence author d.current model (modelViews d.current model) root (.node 92 [.node 93 [],.node 94 []]) ∧
      ∀ row ∈ answer.writes,row.Holds model := by
  have yes := actual_two_ordered_children_selected
  unfold test at yes
  cases actual : data with
  | none => rw [actual] at yes; cases yes
  | some d =>
    rw [actual] at yes
    have checked : (verify author d.current (layouts d) [5] root (code d) answer).isSome = true := yes
    cases out : verify author d.current (layouts d) [5] root (code d) answer with
    | none => rw [out] at checked; cases checked
    | some a =>
      have fit := same_actual_models actual
      obtain ⟨_,_,found,_,chosen,sound,rows⟩ := report_sound a model (modelViews d.current model) fit
      have order : dict a.proof = .node 92 [.node 93 [],.node 94 []] := (Result.selected.inj found).symm
      exact ⟨d,a,rfl,fit,chosen,order,order ▸ sound,rows⟩

end Yulang.GeneralDeclarativeWitnessSiblingFixture358
