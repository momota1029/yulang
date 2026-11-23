import Yulang.GeneralDeclarativeWitnessVarianceModel357
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 49000
set_option maxHeartbeats 55000000
namespace Yulang.GeneralDeclarativeWitnessVarianceEndToEnd357
open GeneralDeclarativeWitnessVarianceModel357 (model views fits_data leaf_classify)
open GeneralDeclarativeWitnessJoinedFixture357 (Data data root written layout test)
open GeneralDeclarativeWitnessDeclaredState357 (ModelsCurrent authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (Rule Evidence dictionary_sound SourceChecked)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage check check_exact)
open GeneralDeclarativeWitnessModeDeclaration357 (ready source_ready)
open GeneralDeclarativeWitnessJoinedCheck357 (Answer replay)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEntailment320 (Holds)
open CommonRoleOutermostResolver (Classify)

def acceptedLeaf (d : Data) : Bool :=
  ((replay d.current root written layout d.wire).map fun a =>
    (a.impl.id == 92) && a.kids.isEmpty).getD false &&
  check d.current.environment && ready d.current &&
  GeneralSourceMetadataRoles291.check d.current.environment.source.roles

theorem literal_leaf_verified : ((data false).map acceptedLeaf).getD false = true := by decide +kernel

theorem source_checks {d : Data} (verified : acceptedLeaf d = true) :
    Coverage d.current.environment ∧ SourceChecked d.current := by
  obtain ⟨lh, roles⟩ := splitAnd verified
  obtain ⟨l,source⟩ := splitAnd lh
  obtain ⟨_,cov⟩ := splitAnd l
  have covered := (check_exact (GeneralSourceMetadataRoles291.check_exact .. |>.mp roles)).mp cov
  exact ⟨covered,source_ready covered source⟩

theorem declared_root {d : Data} (found : data false = some d) :
    Declared (authoredRegistry d.current) root := by
  have literal : ((data false).map (fun d => ((authoredRegistry d.current).roles 5).assoc 0)).getD none =
      some none := by decide +kernel
  rw [found] at literal
  intro out requested
  have isFixed : out = (⟨0,60⟩ : GeneralSourceState.Output) := by
    simpa [root] using requested
  subst out
  exact ⟨none,literal⟩

theorem same_model_regular_leaf :
    ∃ (d : Data) (a : Answer d.current root d.wire), data false = some d ∧
      ModelsCurrent d.current model views ∧
      Classify (Rule d.current) root (.selected (.node 92 [])) ∧
      Evidence d.current model views root (.node 92 []) ∧
      a.kids = [] ∧ ∀ e ∈ d.wire.outputRows,Holds model e := by
  have positive := literal_leaf_verified
  cases seen : data false with
  | none => rw [seen] at positive; cases positive
  | some d =>
    rw [seen] at positive
    have ready_ : acceptedLeaf d = true := positive
    have ⟨cov,ready⟩ := source_checks ready_
    have off := (splitAnd (splitAnd (splitAnd ready_).1).1).1
    change (((replay d.current root written layout d.wire).map fun a =>
      (a.impl.id == 92) && a.kids.isEmpty).getD false) = true at off
    cases decoded : replay d.current root written layout d.wire with
    | none => rw [decoded] at off; cases off
    | some a =>
      rw [decoded] at off
      have tests : (a.impl.id == 92) && a.kids.isEmpty = true := off
      have chosen : a.impl.id = 92 := beq_iff_eq.mp (splitAnd tests).1
      have none : a.kids = [] := List.isEmpty_iff.mp (splitAnd tests).2
      have selected := leaf_classify a none
      rw [chosen] at selected
      have fit := fits_data seen
      have evidence := dictionary_sound ready cov (declared_root seen) selected model views fit
      have body := GeneralDeclarativeWitnessDeclaredState357.output_meaning a.localRead.body model fit.1
      refine ⟨d,a,rfl,fit,selected,evidence,none,?_⟩
      rw [a.actualWrites]
      exact body.2

end Yulang.GeneralDeclarativeWitnessVarianceEndToEnd357
