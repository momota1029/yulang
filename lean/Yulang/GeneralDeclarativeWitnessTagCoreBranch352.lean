import Yulang.GeneralDeclarativeWitnessTagCore352

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagCoreBranch352
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration Registry Clause)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach)
open GeneralDeclarativeWitnessTagElection352 (Ends reads Elected elect)
open GeneralDeclarativeWitnessTagLocal351 (Route PatternData parse context spans)
open GeneralDeclarativeWitnessTagHeader352 (replay replay_first replay_sound)
open GeneralDeclarativeWitnessTagBranch352 (Wire same_table)
open GeneralDeclarativeWitnessTagCore352 (literal_node)
open GeneralDeclarativeAssembly320 (Node)
open GeneralDeclarativeWitnessBound349 (Range)
open GeneralDeclarativeWitnessAuthNode351 (Anchor)
open GeneralDeclarativeWitnessOneRecord350 (pointPortal)
open GeneralDeclarativeWitnessPointInput349 (pick picked)
open GeneralDeclarativeWitnessProblem349 (Problem splitAnd)
open GeneralDeclarativeWitnessCompiler350 (Accepted)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessAllocation350 (names)
open GeneralSourceMetadataBareBundle291 (compile reassemble)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeExactDictionary337 (LocalNode)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCommonBridge (Assignment)

structure CoreRoute (p : Anchor) (table : SourceBundle) where
  decl : Declaration
  kids : List Demand
  meaning : ∀ m : Assignment, Models p.problem.state m →
    Node (registry table) (interpretation table.snapshot) m p.problem.demand decl.id kids

/-- Rechecks the same tagged certificate while reflecting the literal
semantic conclusion used by C334. This is not a C334 verdict. -/
def decode (p : Anchor) {table : SourceBundle}
    (metadata : compile p.problem.source = some table) (live : Attached p.problem.state p.manifest)
    (w : Wire) : Option (CoreRoute p table) := do
  match checked : replay p.problem ⟨p.problem.demand.outputs⟩ with
  | none => none
  | some found =>
    have same : found = table := same_table checked metadata
    match chosen : pick (pointPortal p.problem) found with
    | none => none
    | some decl =>
      match args : p.problem.demand.arguments, head : decl.head with
      | [arg],[pat] =>
        match normalize pat with
        | .variant tag _ => do
          let checkedPat ← parse (registry found).constructors (interpretation found.snapshot) pat tag
          let src ← attach p.before p.manifest
          let before ← reads src arg tag w.originalBounds w.originalReads
          let current ← reads live arg tag w.currentBounds w.currentReads
          if ranked : GeneralDeclarativeWitnessRank350.check p.problem.state w.rank = true then
            if _kept : GeneralDeclarativeWitnessLiteral349.preserves p.before p.problem.state = true then
              if _actualSlots : w.namedSlots = names (spans before checkedPat p.keep) then do
                let body ← GeneralDeclarativeWitnessCompiler350.decode
                  (context p.problem.demand decl before checkedPat p.keep p.fallback p.targets) p.problem.state w.emitted
                let _actualElection := elect live args head chosen current checkedPat ranked
                let well := replay_sound checked
                let foundDecl := picked chosen
                have positive : CoreRoute p found := {
                  decl := decl
                  kids := body.compiled.kids
                  meaning := fun m okay =>
                    (literal_node before checkedPat body well.2.1 well.2.2.1 foundDecl.1 foundDecl.2.1
                      well.2.2.2.1 args head m okay).1 }
                pure (same ▸ positive)
              else none
            else none
          else none
        | _ => none
      | _,_ => none

end Yulang.GeneralDeclarativeWitnessTagCoreBranch352
