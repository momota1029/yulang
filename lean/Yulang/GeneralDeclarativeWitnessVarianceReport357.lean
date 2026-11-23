import Yulang.GeneralDeclarativeWitnessReifiedViews357
import Yulang.GeneralDeclarativeWitnessJoinedCheck357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessVarianceReport357
open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry ModelsCurrent)
open GeneralDeclarativeWitnessClassifyVariance357 (Rule SourceChecked Evidence dictionary_sound)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage)
open GeneralDeclarativeWitnessJoinedCheck357 (Recipe Layout Answer replay replay_rule)
open GeneralDeclarativeWitnessCompiler350 (Wire)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeWitnessProblem349 (Problem splitAnd)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Tree Classify Dictionary)

def problem (s : Current) (d : Demand) : Problem :=
  ⟨GeneralSourceMetadataBareBundle291.forget s.environment.source,s.ordinary,d⟩

structure Leaf (s : Current) (d : Demand) (w : Wire) (report : Report) where
  answer : Answer s d w
  noChildren : answer.kids = []
  soundSource : SourceChecked s
  covered : Coverage s.environment
  printed : agrees (problem s d) (.selected answer.impl.id []) report = true

def checkLeaf (s : Current) (d : Demand) (a : Recipe) (l : Layout) (w : Wire) (r : Report) :
    Option (Leaf s d w r) := do
  let ans ← replay s d a l w
  if empty : ans.kids.isEmpty = true then
    if legal : GeneralSourceMetadataRoles291.check s.environment.source.roles = true then
      if cover : GeneralDeclarativeWitnessModeCoverage357.check s.environment = true then
        if ready : GeneralDeclarativeWitnessModeDeclaration357.ready s = true then
          if printed : agrees (problem s d) (.selected ans.impl.id []) r = true then
            let known := (GeneralDeclarativeWitnessModeCoverage357.check_exact
              ((GeneralSourceMetadataRoles291.check_exact _).mp legal)).mp cover
            some ⟨ans,List.isEmpty_iff.mp empty,
              GeneralDeclarativeWitnessModeDeclaration357.source_ready known ready,known,printed⟩
          else none
        else none
      else none
    else none
  else none

theorem exact_leaf_certificate {s d w r} (a : Leaf s d w r)
    (asked : Declared (authoredRegistry s) d) (m : Assignment)
    (v : GeneralDeclarativeWitnessDeclaredState357.Views) (fit : ModelsCurrent s m v) :
    r.tree = .selected a.answer.impl.id [] ∧
    r.result = .selected (.node a.answer.impl.id []) ∧
    r.outputs = d.outputs ∧
    Classify (Rule s) d r.result ∧
    Evidence s m v d (.node a.answer.impl.id []) ∧
    w.outputRows.map GeneralDeclarativeHead320.Equation.left = d.outputs.map GeneralSourceState.Output.target ∧
    ∀ eq ∈ w.outputRows,Holds m eq := by
  have rPrinted := exact_report a.printed
  have run := replay_rule a.answer
  rw [a.noChildren] at run
  have classified : Classify (Rule s) d (.selected (.node a.answer.impl.id [])) :=
    ⟨.selected a.answer.impl.id [],.selected run .nil,.selected .nil (.selected rfl)⟩
  have result : r.result = .selected (.node a.answer.impl.id []) := rPrinted.2.1
  have output := GeneralDeclarativeWitnessDeclaredState357.output_meaning a.answer.localRead.body m fit.1
  refine ⟨rPrinted.1,result,rPrinted.2.2,?_⟩
  rw [result,a.answer.actualWrites]
  exact ⟨classified,dictionary_sound a.soundSource a.covered asked classified m v fit,output⟩

end Yulang.GeneralDeclarativeWitnessVarianceReport357
