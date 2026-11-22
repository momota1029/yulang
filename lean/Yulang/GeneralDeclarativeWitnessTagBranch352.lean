import Yulang.GeneralDeclarativeWitnessTagHeader352
import Yulang.GeneralDeclarativeWitnessTagElection352
import Yulang.GeneralDeclarativeWitnessTagNode351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagBranch352
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration Registry Clause)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach)
open GeneralDeclarativeWitnessTagElection352 (Ends reads Elected elect)
open GeneralDeclarativeWitnessTagLocal351 (Route PatternData parse context spans)
open GeneralDeclarativeWitnessTagHeader352 (replay replay_first replay_sound)
open GeneralDeclarativeWitnessTagNode351 (local_node)
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

structure Wire where
  originalBounds : Range
  originalReads : Ends
  currentBounds : Range
  currentReads : Ends
  rank : List Nat
  namedSlots : List (Nat × Nat × Nat × Nat)
  emitted : GeneralDeclarativeWitnessCompiler350.Wire

structure LocalRoute {s : State} {t : Table} (live : Attached s t) (table : SourceBundle) (d : Demand) where
  decl : Declaration
  kids : List Demand
  election : Elected live (registry table) (interpretation table.snapshot) d decl
  meaning : ∀ m : Assignment, Models s m →
    LocalNode (registry table) (interpretation table.snapshot) m d decl.id kids ∧
      (∀ child ∈ kids, Declared (registry table) child)
  fixed : List Equation
  fixedMeaning : ∀ path, (Fixed.mk path d fixed).Meaning s

theorem same_table {p : Problem} {w} {s t : SourceBundle}
    (registered : replay p w = some s) (actual : compile p.source = some t) : s = t := by
  have scanned := (replay_first registered).1
  obtain ⟨input,valid,_⟩ := GeneralDeclarativeWitnessProblem349.first_sound scanned
  have recovered := reassemble s valid
  rw [input,actual] at recovered
  exact (Option.some.inj recovered).symm

/-- At the current state readiness/election are rechecked. Independently,
the source snapshot supplies the actual allocation origin and compiler.
Exact slots, children, target rows and their semantic receipt are checked. -/
def decode (p : Anchor) {table : SourceBundle}
    (metadata : compile p.problem.source = some table) (live : Attached p.problem.state p.manifest)
    (w : Wire) : Option (LocalRoute live table p.problem.demand) := do
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
                let right := elect live args head chosen current checkedPat ranked
                let well := replay_sound checked
                let foundDecl := picked chosen
                have positive : LocalRoute live found p.problem.demand := {
                  decl := decl
                  kids := body.compiled.kids
                  election := right
                  meaning := fun m okay =>
                    local_node before checkedPat body well.2.1 well.2.2.1 foundDecl.1 foundDecl.2.1
                      well.2.2.2.1 args head m okay
                  fixed := w.emitted.outputRows
                  fixedMeaning := fun _ => ⟨by rw [body.fixed]; exact GeneralDeclarativeWitnessCompiler350.fixed_targets body.run,
                    fun m okay => (GeneralDeclarativeWitnessCompiler350.fixed_in_current body m okay).2⟩ }
                pure (same ▸ positive)
              else none
            else none
          else none
        | _ => none
      | _,_ => none

end Yulang.GeneralDeclarativeWitnessTagBranch352
