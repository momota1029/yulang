import Yulang.GeneralDeclarativeWitnessClosedRecordModel358
import Yulang.GeneralDeclarativeWitnessActualAddress358

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessClosedRecordReport358
open GeneralDeclarativeWitnessClosedRecordLocal358 (Chosen Checked)
open GeneralDeclarativeWitnessClosedRecordFixture358 (Data data author receipt firstLayout laterLayout)
open GeneralDeclarativeWitnessClosedRecordModel358 (model fits)
open GeneralDeclarativeWitnessJoinedFixture357 (root written)
open GeneralDeclarativeWitnessJoinedCheck357 (Answer replay)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessDeclaredState357 (Current ModelsCurrent Views authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (SourceChecked)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage)
open GeneralDeclarativeWitnessOrderedReport358 (Packet)
open GeneralDeclarativeWitnessOrderedMeaning358 (Entry)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWitnessTree349 (agrees exact_report)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent record exactEmpty)
open CommonRoleOutermostResolver (Tree Dictionary Classify Frontier)

inductive Rule (source : Source) (s : Current) : Demand → Frontier Demand → Prop where
  | stable : GeneralDeclarativeWitnessProjectionRule358.Rule source s d front → Rule source s d front
  | record (r : Chosen source s d impl children) : Rule source s d (.selected impl.id children)

structure Pair (d : Data) (a : Source) (out : Packet) where
  parent : Answer d.current root d.parentAnswer
  child : Checked a d.current d.reached d.ownAnswer
  reaches : parent.kids = [d.reached]
  complete : child.kids = []
  book : SourceChecked d.current
  cover : Coverage d.current.environment
  report : agrees (GeneralDeclarativeWitnessVarianceReport357.problem d.current root)
    (.selected parent.impl.id [.selected child.impl.id []]) out.report = true
  writes : out.writes =
    [⟨[5],printDemand root,d.parentAnswer.outputRows⟩,⟨[5,0],printDemand d.reached,d.ownAnswer.outputRows⟩]

def decode (d : Data) (a : Source) (out : Packet) : Option (Pair d a out) := do
  let top ← replay d.current root written firstLayout d.parentAnswer
  let child ← GeneralDeclarativeWitnessClosedRecordLocal358.read a d.current d.reached receipt 33 34
    (laterLayout d.first) d.ownAnswer
  if shape : top.kids.map printDemand = [printDemand d.reached] ∧ child.kids.isEmpty = true then
    if sources : GeneralSourceMetadataRoles291.check d.current.environment.source.roles = true ∧
        GeneralDeclarativeWitnessModeCoverage357.check d.current.environment = true ∧
        GeneralDeclarativeWitnessModeDeclaration357.ready d.current = true then
      if report : agrees (GeneralDeclarativeWitnessVarianceReport357.problem d.current root)
          (.selected top.impl.id [.selected child.impl.id []]) out.report = true then
        if exact : out.writes =
            [⟨[5],printDemand root,d.parentAnswer.outputRows⟩,⟨[5,0],printDemand d.reached,d.ownAnswer.outputRows⟩] then
          let covered := (GeneralDeclarativeWitnessModeCoverage357.check_exact
              ((GeneralSourceMetadataRoles291.check_exact _).mp sources.1)).mp sources.2.1
          some ⟨top,child,GeneralDeclarativeWitnessCompiler350.map_injective
            (fun h => GeneralDeclarativeWitnessCompiler350.print_injective h) shape.1,
            List.isEmpty_iff.mp shape.2,
            GeneralDeclarativeWitnessModeDeclaration357.source_ready covered sources.2.2,covered,report,exact⟩
        else none
      else none
    else none
  else none

theorem same_model_pair {d a out} (packet : Pair d a out) (m : Assignment) (v : Views)
    (fit : ModelsCurrent d.current m v) :
    Declared (authoredRegistry d.current) root ∧ Declared (authoredRegistry d.current) d.reached ∧
    out.report.result = .selected (.node packet.parent.impl.id [.node packet.child.impl.id []]) ∧
    Classify (Rule a d.current) root out.report.result ∧
    GeneralDeclarativeWitnessProjectionRule358.LocalEvidence a d.current m v root packet.parent.impl.id
      [d.reached] ∧
    Equivalent (m packet.child.chosen.proj.remainder).1 exactEmpty ∧
    ∀ row ∈ out.writes,row.Holds m := by
  have parentRule := GeneralDeclarativeWitnessJoinedCheck357.replay_rule packet.parent
  rw [packet.reaches] at parentRule
  have ch : Rule a d.current d.reached (.selected packet.child.impl.id packet.child.kids) :=
    .record packet.child.chosen
  rw [packet.complete] at ch
  have top : Rule a d.current root (.selected packet.parent.impl.id [d.reached]) := .stable (.prior parentRule)
  have old := exact_report packet.report
  have value : out.report.result = .selected (.node packet.parent.impl.id [.node packet.child.impl.id []]) := old.2.1
  have actual : Classify (Rule a d.current) root out.report.result := by
    rw [value]
    exact ⟨.selected packet.parent.impl.id [.selected packet.child.impl.id []],
      .selected top (.cons (.selected ch .nil) .nil),
      .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩
  have asked := GeneralDeclarativeWitnessOrderedMeaning358.local_declared
    (a := a) (.joined packet.parent) packet.book
  have sem := GeneralDeclarativeWitnessProjectionRule358.local_sound (a := a) packet.book packet.cover
    (.prior parentRule) asked m v fit
  have child := GeneralDeclarativeWitnessClosedRecordLocal358.same_model packet.child packet.book m fit.1
  have outParent := GeneralDeclarativeWitnessDeclaredState357.output_meaning packet.parent.localRead.body m fit.1
  refine ⟨asked,child.1,value,actual,sem.1,child.2.2.1,?_⟩
  rw [packet.writes]
  intro row seen
  simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with rfl|rfl
  · change (d.parentAnswer.outputRows.map GeneralDeclarativeHead320.Equation.left =
      (root.outputs.map GeneralDeclarativeWitnessCompiler350.pair).map Prod.snd) ∧ _
    rw [packet.parent.actualWrites,List.map_map]
    exact outParent
  · change (d.ownAnswer.outputRows.map GeneralDeclarativeHead320.Equation.left =
      (d.reached.outputs.map GeneralDeclarativeWitnessCompiler350.pair).map Prod.snd) ∧ _
    rw [List.map_map]
    exact child.2.2.2.2.2.2

end Yulang.GeneralDeclarativeWitnessClosedRecordReport358
