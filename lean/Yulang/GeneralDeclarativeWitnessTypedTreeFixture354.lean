import Yulang.GeneralDeclarativeWitnessTypedTree354
import Yulang.GeneralDeclarativeWitnessTypedModel354
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 38000
set_option maxHeartbeats 31000000
namespace Yulang.GeneralDeclarativeWitnessTypedTreeFixture354
open GeneralDeclarativeWitnessTypedFixture354 (problem data actualRoot)
open GeneralDeclarativeWitnessTypedModel354 (model model_fits)
open GeneralDeclarativeWitnessTypedTree354 (Envelope Accepted decode exactly)
open GeneralDeclarativeWitnessTypedSound354 (childView released_type_at_actual_center both)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessTypedChild354 (Wire)
open GeneralDeclarativeWitnessCovariantOrigin353 (View)

def answer : Report := ⟨.selected 92 [.selected 93 []],.selected (.node 92 [.node 93 []]),actualRoot.outputs⟩
def envelope (w : Wire) : Envelope := ⟨[4],[4,0],w,answer⟩
def test (edit : Envelope → Envelope := id) : Bool :=
  (data.map (fun (s,w) => (decode problem s (edit (envelope w))).isSome)).getD false

theorem actual_tree : test = true := by decide +kernel

theorem wrong_child_path : test (fun e => {e with childPath := [4,1]}) = false := by decide +kernel

theorem wrong_writer_path : test (fun e => {e with writerPath := [5]}) = false := by decide +kernel

theorem wrong_dictionary :
    test (fun e => {e with reported := {answer with result := .selected (.node 92 [.node 94 []])}}) = false := by
  decide +kernel

theorem target_sequence_changed :
    test (fun e => {e with reported := {answer with outputs := answer.outputs.reverse}}) = false := by decide +kernel

theorem concrete_same_model_tree :
    ∃ (s : State) (w : Wire) (a : Accepted problem s (envelope w)),
      data = some (s,w) ∧ Models s model ∧
      (envelope w).reported.result = .selected (.node 92 [.node 93 []]) ∧
      (envelope w).childPath = [4,0] ∧
      (∃ v : View,childView a.core model a.core.receiver.facts.arg.center = some v ∧
        v.tag = a.core.emitted.atWrite.typed.tag ∧ v.box = a.core.emitted.atWrite.typed.box) := by
  have yes := actual_tree
  unfold test at yes
  cases h : data with
  | none => simp [h] at yes
  | some pair =>
    obtain ⟨s,w⟩ := pair
    have ok : (decode problem s (envelope w)).isSome = true := by simpa [h] using yes
    cases checked : decode problem s (envelope w) with
    | none => simp [checked] at ok
    | some a =>
      have valid := model_fits h
      obtain ⟨chosen,here,tag,box,_⟩ := released_type_at_actual_center a.core model valid
      exact ⟨s,w,a,rfl,valid,rfl,rfl,⟨chosen,here,tag,box⟩⟩

end Yulang.GeneralDeclarativeWitnessTypedTreeFixture354
