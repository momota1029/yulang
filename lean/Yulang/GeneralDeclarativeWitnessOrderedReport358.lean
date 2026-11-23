import Yulang.GeneralDeclarativeWitnessOrderedMeaning358
import Yulang.GeneralDeclarativeWitnessReifiedViews357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOrderedReport358
open GeneralDeclarativeWitnessOrderedReplay358 (Code Tree LayoutAt read)
open GeneralDeclarativeWitnessOrderedMeaning358 (Entry diag dict ledger classify declared_tree ledger_exact)
open GeneralDeclarativeWitnessDeclaredState357 (Current Views ModelsCurrent authoredRegistry)
open GeneralDeclarativeWitnessProjectionRule358 (Rule Evidence dictionary_sound)
open GeneralDeclarativeWitnessClassifyVariance357 (SourceChecked)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeWitnessVarianceReport357 (problem)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)

deriving instance DecidableEq for Entry

structure Packet where
  report : Report
  writes : List Entry

structure Checked (a : Source) (s : Current) (p : List Nat) (d : Demand) (packet : Packet) where
  proof : Tree a s p d
  declarations : SourceChecked s
  modes : Coverage s.environment
  decoded : agrees (problem s d) (diag proof) packet.report = true
  exactWrites : packet.writes = ledger proof

def verify (source : Source) (s : Current) (layout : LayoutAt) (path : List Nat) (d : Demand)
    (code : Code) (packet : Packet) : Option (Checked source s path d packet) := do
  let proof ← read source s layout path d code
  if roles : GeneralSourceMetadataRoles291.check s.environment.source.roles = true then
    if scopes : GeneralDeclarativeWitnessModeCoverage357.check s.environment = true then
      if declarations : GeneralDeclarativeWitnessModeDeclaration357.ready s = true then
        if matchesReport : agrees (problem s d) (diag proof) packet.report = true then
          if correct : packet.writes = ledger proof then
            let modes := (GeneralDeclarativeWitnessModeCoverage357.check_exact
              ((GeneralSourceMetadataRoles291.check_exact _).mp roles)).mp scopes
            some ⟨proof,GeneralDeclarativeWitnessModeDeclaration357.source_ready modes declarations,
              modes,matchesReport,correct⟩
          else none
        else none
      else none
    else none
  else none

theorem report_sound {a s p d result} (c : Checked a s p d result)
    (m : Assignment) (v : Views) (fit : ModelsCurrent s m v) :
    Declared (authoredRegistry s) d ∧
    result.report.tree = diag c.proof ∧
    result.report.result = .selected (dict c.proof) ∧
    result.report.outputs = d.outputs ∧
    Classify (Rule a s) d result.report.result ∧
    Evidence a s m v d (dict c.proof) ∧
    ∀ row ∈ result.writes,row.Holds m := by
  obtain ⟨shape,choice,out⟩ := exact_report c.decoded
  have classified := classify c.proof
  have declared := declared_tree c.proof c.declarations
  have result_is : result.report.result = .selected (dict c.proof) :=
    choice.trans ((declarative_tree c.proof).2 |> (CommonRoleOutermostResolver.classification_exact ..).mpr)
  exact ⟨declared,shape,result_is,out,result_is.symm ▸ classified,
    dictionary_sound c.declarations c.modes declared classified m v fit,
    c.exactWrites.symm ▸ ledger_exact c.proof m v fit⟩
where
  declarative_tree := @GeneralDeclarativeWitnessOrderedMeaning358.declarative_tree

end Yulang.GeneralDeclarativeWitnessOrderedReport358
