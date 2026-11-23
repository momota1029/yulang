import Yulang.GeneralDeclarativeWitnessClosedRecordReport358

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 64000
set_option maxHeartbeats 92000000
namespace Yulang.GeneralDeclarativeWitnessClosedRecordVerified358
open GeneralDeclarativeWitnessClosedRecordReport358 (Pair Rule decode same_model_pair)
open GeneralDeclarativeWitnessClosedRecordFixture358 (Data data author receipt)
open GeneralDeclarativeWitnessClosedRecordModel358 (model fits)
open GeneralDeclarativeWitnessClosedRecordLocal358 (closed)
open GeneralDeclarativeWitnessSharedTailProjection358 (rows)
open GeneralDeclarativeWitnessOrderedReport358 (Packet)
open GeneralDeclarativeWitnessOrderedMeaning358 (Entry)
open GeneralDeclarativeWitnessJoinedFixture357 (root)
open GeneralDeclarativeWitnessDeclaredState357 (ModelsCurrent)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessReifiedViews357 (modelViews)
open CommonRoleOutermostResolver (Classify Result)

def output : Packet :=
  ⟨⟨.selected 92 [.selected 96 []],.selected (.node 92 [.node 96 []]),root.outputs⟩,
   [⟨[5],(5,[(20,20,20)],[(0,60)]),[⟨60,.variable 10⟩]⟩,
    ⟨[5,0],(6,[(63,10,64)],[(0,41)]),[⟨41,.record 7 (.variable 4) (.variable 0)⟩]⟩]⟩

def test (source : Source := author) (out : Packet := output) : Bool :=
  (data.map (fun d => (decode d source out).isSome)).getD false

theorem actual_closed_report_verified : test = true := by decide +kernel

theorem text_equivalent_tail_cannot_replace_authorship :
    test ⟨rows receipt⟩ = false := by decide +kernel

theorem exact_record_payload_and_rest :
    test author {output with writes := (output.writes.map (fun received => if received.path = [5,0]
      then {received with equations := [⟨41,.record 7 (.variable 0) (.variable 4)⟩]} else received))} = false := by
  decide +kernel

theorem actual_closed_report_with_real_current_model :
    ∃ (d : Data) (p : Pair d author output),data = some d ∧
      ModelsCurrent d.current model (modelViews d.current model) ∧
      Classify (Rule author d.current) root output.report.result ∧
      (model p.child.chosen.proj.remainder).1 =
        CommonNominalFullCarrier.exactEmpty ∧
      ∀ e ∈ output.writes,e.Holds model := by
  have tested := actual_closed_report_verified
  unfold test at tested
  cases obtained : data with
  | none => rw [obtained] at tested; cases tested
  | some d =>
    rw [obtained] at tested
    have yes : (decode d author output).isSome = true := tested
    cases checked : decode d author output with
    | none => rw [checked] at yes; cases yes
    | some p =>
      have fit := fits obtained
      obtain ⟨_,_,_,classified,_,closedShape,good⟩ := same_model_pair p model (modelViews d.current model) fit
      refine ⟨d,p,rfl,fit,classified,?_,good⟩
      have actual : (data.map (fun d => ((decode d author output).map (fun p =>
          decide (p.child.chosen.proj.remainder = 0))).getD false)).getD false = true := by
        decide +kernel
      rw [obtained] at actual
      change ((decode d author output).map (fun p => decide (p.child.chosen.proj.remainder = 0))).getD false =
        true at actual
      rw [checked] at actual
      have root : p.child.chosen.proj.remainder = 0 := of_decide_eq_true actual
      rw [root]
      rfl

end Yulang.GeneralDeclarativeWitnessClosedRecordVerified358
