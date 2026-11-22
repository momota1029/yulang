import Yulang.GeneralDeclarativeWitnessMixedReleaseMeaning356
import Yulang.GeneralDeclarativeWitnessMixedRealModel356
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 60000
set_option maxHeartbeats 75000000
namespace Yulang.GeneralDeclarativeWitnessMixedFrontFixture356
open GeneralDeclarativeWitnessMixedFront356 (Source Wire SitePlan read)
open GeneralDeclarativeWitnessSpineFront355 (Site)
open GeneralDeclarativeWitnessMixedReal356 (problem entry location typedPlan)
open GeneralDeclarativeWitnessMixedRealFixture356 (Data data report)
open GeneralDeclarativeWitnessMixedRealModel356 (model model_fits)
open GeneralDeclarativeWitnessTypedJoint354 (shared)
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line)

def authorLine (r n : Nat) : Line := ⟨r,.variant 13 (.app 0 [.var n])⟩
def first : Site := ⟨typedPlan.authority,1,8,
  [authorLine 30 7,authorLine 31 8,authorLine 32 32,authorLine 33 33],typedPlan.keep,typedPlan.fallback⟩
def supplied (d : Data) : Source :=
  ⟨{problem with rows := []},location,[authorLine 30 7,authorLine 31 8,authorLine 20 10],d.env,
  [.typed first [],.ordinaryPayload 81 32]⟩
def signed (d : Data) : Wire := ⟨entry,d.root,d.children,report⟩
def test (change : Source → Source := id) (edit : Wire → Wire := id) : Bool :=
  (data.map (fun d => (read (change (supplied d)) d.current (edit (signed d))).isSome)).getD false

theorem independent_full_front_is_accepted : test = true := by decide +kernel

theorem cannot_author_issued_nominal_center :
    test (fun w => {w with plans :=
      [.typed {first with rows := first.rows ++ [authorLine 10 10]} [],.ordinaryPayload 81 32]}) =
      false := by decide +kernel

theorem ordinary_source_is_separately_required :
    test (fun w => {w with scope := {w.scope with origins := {w.scope.origins with authored := []}}}) =
      false := by decide +kernel

theorem same_number_not_a_carrier_tag :
    (data.map (fun d => ((read (supplied d) d.current (signed d)).map (fun a =>
      ((shared a.root.input (a.root.input.rows ++ a.replay.children.rows) model 10).map
        fun v => decide (v.tag = 13 ∧ v.box = 0)).getD false)).getD false)).getD false =
      true := by decide +kernel

theorem has_explicit_two_carriers_on_actual_model :
    ∃ (d : Data)
      (a : GeneralDeclarativeWitnessMixedFront356.Found (supplied d) d.current (signed d)),
      GeneralDeclarativeHead320.Models d.current model ∧
      (model 10).1 = GeneralDeclarativeTaggedFixtureModel340.actualRoot ∧
      ∃ v : GeneralDeclarativeWitnessCovariantOrigin353.Valuation,
        (∃ nom, v 10 = some nom ∧ nom.tag = 13 ∧ nom.box = 0) ∧
        GeneralDeclarativeWitnessMixedReleaseMeaning356.group model v a.replay.children := by
  have tagged := same_number_not_a_carrier_tag
  cases got : data with
  | none => rw [got] at tagged; cases tagged
  | some d =>
    cases proof : read (supplied d) d.current (signed d) with
    | none => simp [got,proof] at tagged
    | some a =>
      have fit := model_fits got
      let v := shared a.root.input (a.root.input.rows ++ a.replay.children.rows) model
      have tagged : ((v 10).map fun x => decide (x.tag = 13 ∧ x.box = 0)).getD false = true := by
        simpa [got,proof,v] using tagged
      have each := GeneralDeclarativeWitnessTypedJoint354.author_rows (p := a.root.input) a.replay.compatible model
      have scopedRead := GeneralDeclarativeWitnessMixedReleaseMeaning356.actual_branch_facts
        a.replay.children model fit v (fun row has => each row (List.mem_append_right _ has))
      cases lookup : v 10 with
      | none => simp [lookup] at tagged
      | some x =>
        have good : decide (x.tag = 13 ∧ x.box = 0) = true := by simpa [lookup] using tagged
        exact ⟨d,a,fit,rfl,v,⟨x,lookup,(of_decide_eq_true good).1,(of_decide_eq_true good).2⟩,scopedRead⟩

end Yulang.GeneralDeclarativeWitnessMixedFrontFixture356
