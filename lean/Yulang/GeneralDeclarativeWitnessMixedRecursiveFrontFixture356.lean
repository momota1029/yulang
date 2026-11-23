import Yulang.GeneralDeclarativeWitnessMixedPathLedger356
import Yulang.GeneralDeclarativeWitnessMixedNestedModel356
import Yulang.GeneralDeclarativeWitnessMixedFrontFixture356
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 66000
set_option maxHeartbeats 85000000
namespace Yulang.GeneralDeclarativeWitnessMixedRecursiveFrontFixture356
open GeneralDeclarativeWitnessRecursiveSource356 (AuthorPlans Source Wire Found read actual_authored_model)
open GeneralDeclarativeWitnessMixedNestedSeed356 (root)
open GeneralDeclarativeWitnessMixedNestedFixture356 (Data data)
open GeneralDeclarativeWitnessMixedNestedModel356 (model model_fits)
open GeneralDeclarativeWitnessMixedLedgerFixture356 (packet)
open GeneralDeclarativeWitnessMixedReal356 (entry location)
open GeneralDeclarativeWitnessMixedFrontFixture356 (authorLine first)
open GeneralDeclarativeWitnessMixedLedger356 (Entry Meaning)
open GeneralDeclarativeWitnessRecursiveTree356 (dictionary)
open GeneralDeclarativeWitnessRecursiveSound356 (Evident)
open GeneralDeclarativeWitnessCovariantOrigin353 (Valuation)
open GeneralDeclarativeHead320 (Models)

def authoredPlan : AuthorPlans := .cons (.typed first (.cons (.payload 82 31) .nil))
  (.cons (.payload 81 32) .nil)

def source (d : Data) : Source :=
  ⟨{root with rows := []},location,[authorLine 30 7,authorLine 31 8,authorLine 20 10],d.environment,authoredPlan⟩

def wire (d : Data) : Wire := ⟨entry,d.emitter,d.ordered,packet⟩

def test (update : Source → Source := id) : Bool :=
  (data.map (fun d => (read (update (source d)) d.state (wire d)).isSome)).getD false

theorem complete_authored_shape_matches_actual : test = true := by decide +kernel

theorem inner_wrong_authored_clause_rejected :
    test (fun p => {p with author := .cons (.typed first (.cons (.payload 81 31) .nil)) (.cons (.payload 81 32) .nil)}) = false := by decide +kernel

theorem typed_roles_cannot_be_hidden_inside_ordinary_scope :
    test (fun p => {p with environment := {p.environment with typedRoles := [1,3,5]}}) = false := by decide +kernel

theorem actual_author_tree_with_exact_mixed_model :
    ∃ (d : Data) (a : Found (source d) d.state (wire d)),
      Models d.state model ∧
      packet.outputs.map Entry.path = [[4],[4,0],[4,0,0],[4,1]] ∧
      packet.answer.result = .selected (dictionary a.replay.proof) ∧
      (∀ t ∈ packet.outputs,Meaning model t) ∧
      ∃ v : Valuation,Evident d.state model v (source d).base.demand (dictionary a.replay.proof) := by
  have good := complete_authored_shape_matches_actual
  unfold test at good
  cases got : data with
  | none => rw [got] at good; cases good
  | some d =>
    cases recorded : read (source d) d.state (wire d) with
    | none => simp [got,recorded] at good
    | some a =>
      have fit := model_fits got
      have exact := actual_authored_model a model fit
      exact ⟨d,a,fit,rfl,exact.2.1,exact.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessMixedRecursiveFrontFixture356
