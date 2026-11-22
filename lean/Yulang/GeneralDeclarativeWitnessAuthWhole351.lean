import Yulang.GeneralDeclarativeWitnessAuthForest351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessAuthWhole351
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeWitnessAuthForest351 (Problem Global Replayed rules replayTree)
open GeneralDeclarativeWitnessCatalog351 (Receipt)
open GeneralDeclarativeWitnessIdentity351 (table)
open GeneralDeclarativeWitnessForest350 (Code Fixed)
open GeneralDeclarativeWitnessRecordHeader350 (replay replay_sound)
open GeneralDeclarativeWitnessRecordNodes350 (same_table)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report classifies)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralSourceMetadataBareBundle291 (compile)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify Dictionary)

def goal (p : Problem) : GeneralDeclarativeWitnessProblem349.Problem :=
  ⟨p.consumer,p.current,p.target⟩

structure Wire where
  prior : Code
  priorReport : Report
  consumer : Code

structure Accepted (p : Problem) (w : Wire) (report : Report) where
  writer : Receipt p.writer w.prior w.priorReport
  env : Global p (table p.writer.authored writer.owned p.writer.releases)
  diagnostic : Replayed env p.target
  metadata : SourceBundle
  header : replay (goal p) ⟨report.outputs⟩ = some metadata
  exactReport : agrees (goal p) diagnostic.tree report = true

/-- The producer and consumer are independently replayed against the
same ordinary state. The consumer's supported view retains output
origin and uses only the authoritative exact occurrence releases. -/
def decode (p : Problem) (w : Wire) (report : Report) : Option (Accepted p w report) := do
  let producer ← GeneralDeclarativeWitnessCatalog351.check p.writer w.prior w.priorReport
  match compiledTable : compile p.consumer with
  | none => none
  | some tab =>
    let env : Global p _ := ⟨tab,compiledTable,producer.catalogue⟩
    let verified ← replayTree env [] p.target w.consumer
    match header : replay (goal p) ⟨report.outputs⟩ with
    | none => none
    | some written =>
      if exact : agrees (goal p) verified.tree report = true
      then some ⟨producer,env,verified,written,header,exact⟩
      else none

def check (p : Problem) (w : Wire) (report : Report) : Bool := (decode p w report).isSome

theorem checked {p : Problem} {w : Wire} {report : Report} (ok : check p w report = true) :
    Nonempty (Accepted p w report) := by
  unfold check at ok
  cases x : decode p w report with
  | none => simp [x] at ok
  | some yes => exact ⟨yes⟩

theorem exact_result {p : Problem} {w : Wire} {report : Report} (a : Accepted p w report) :
    report.tree = a.diagnostic.tree ∧ report.outputs = p.target.outputs ∧
      Classify (rules a.env a.diagnostic.sidecar) p.target report.result ∧
      ∀ f ∈ a.diagnostic.fixed, Fixed.Meaning f p.current := by
  have matched := exact_report a.exactReport
  exact ⟨matched.1,matched.2.2,classifies
    (GeneralDeclarativeWitnessAuthForest351.resolves a.diagnostic) a.exactReport,
    a.diagnostic.fixedMeaning⟩

theorem selected {p : Problem} {w : Wire} {report : Report} (a : Accepted p w report)
    {d : Dictionary} (result : report.result = .selected d)
    (m : Assignment) (fit : Models p.current m) :
    Evidence (registry a.env.bundle) (interpretation a.env.bundle.snapshot) m p.target d ∧
      ∀ f ∈ a.diagnostic.fixed, f.equations.map GeneralDeclarativeHead320.Equation.left =
        f.demand.outputs.map GeneralSourceState.Output.target ∧
        ∀ e ∈ f.equations,GeneralDeclarativeEntailment320.Holds m e := by
  obtain ⟨_,_,classification,writes⟩ := exact_result a
  rw [result] at classification
  obtain ⟨_,well,coverage,declared,_⟩ := replay_sound a.header
  have same : a.metadata = a.env.bundle := same_table a.header a.env.canonical
  rw [same] at well coverage declared
  refine ⟨GeneralDeclarativeTaggedDictionary340.dictionary_sound well coverage declared classification
    (GeneralDeclarativeWitnessAuthForest351.models a.diagnostic m fit),?_⟩
  intro f found
  have meaning := writes f found
  exact ⟨meaning.1,meaning.2 m fit⟩

theorem producer_same_model {p : Problem} {w : Wire} {report : Report} (a : Accepted p w report)
    {d : Dictionary} (result : w.priorReport.result = .selected d)
    (m : Assignment) (fit : Models p.current m) :
    Evidence (registry a.writer.producer.global.table)
      (interpretation a.writer.producer.global.table.snapshot) m p.writer.root d :=
  (GeneralDeclarativeWitnessRecordWhole350.selected a.writer.producer result m fit).1

end Yulang.GeneralDeclarativeWitnessAuthWhole351
