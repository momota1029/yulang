import Yulang.GeneralDeclarativeWitnessVarianceReport357
import Yulang.GeneralDeclarativeWitnessVarianceEndToEnd357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 49000
set_option maxHeartbeats 57000000
namespace Yulang.GeneralDeclarativeWitnessVarianceReportFixture357
open GeneralDeclarativeWitnessVarianceReport357 (Leaf checkLeaf exact_leaf_certificate)
open GeneralDeclarativeWitnessJoinedFixture357 (Data data root written layout)
open GeneralDeclarativeWitnessVarianceModel357 (model views fits_data)
open GeneralDeclarativeWitnessVarianceEndToEnd357 (declared_root)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessClassifyVariance357 (Rule Evidence)
open GeneralDeclarativeWitnessDeclaredState357 (ModelsCurrent)
open GeneralDeclarativeEntailment320 (Holds)
open CommonRoleOutermostResolver (Classify)

def answer : Report := ⟨.selected 92 [],.selected (.node 92 []),root.outputs⟩
def tries (child : Bool) (report : Report := answer) : Bool :=
  ((data child).map fun d => (checkLeaf d.current root written layout d.wire report).isSome).getD false

theorem accepted_actual_report : tries false = true := by decide +kernel

theorem wrong_diagnostic : tries false {answer with tree := .selected 99 []} = false := by decide +kernel

theorem wrong_dictionary : tries false {answer with result := .selected (.node 99 [])} = false := by decide +kernel

theorem wrong_requested_output : tries false {answer with outputs := [⟨0,10⟩]} = false := by decide +kernel

theorem real_branch_cannot_end_at_leaf : tries true = false := by decide +kernel

theorem actual_report_in_real_combined_model :
    ∃ (d : Data) (_ : Leaf d.current root d.wire answer),data false = some d ∧
      ModelsCurrent d.current model views ∧ Classify (Rule d.current) root answer.result ∧
      (∃ k,answer.result = .selected (.node k []) ∧ Evidence d.current model views root (.node k [])) ∧
      ∀ eq ∈ d.wire.outputRows,Holds model eq := by
  have yes := accepted_actual_report
  unfold tries at yes
  cases found : data false with
  | none => rw [found] at yes; cases yes
  | some d =>
    rw [found] at yes
    have check : (checkLeaf d.current root written layout d.wire answer).isSome = true := yes
    cases exact : checkLeaf d.current root written layout d.wire answer with
    | none => rw [exact] at check; cases check
    | some verified =>
      have fit := fits_data found
      obtain ⟨_,dict,_,selected,proof,_,outputs⟩ := exact_leaf_certificate verified (declared_root found) model views fit
      exact ⟨d,verified,rfl,fit,selected,⟨_,dict,proof⟩,outputs⟩

end Yulang.GeneralDeclarativeWitnessVarianceReportFixture357
