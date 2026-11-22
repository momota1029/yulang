import Yulang.GeneralDeclarativeWitnessCovariantCompiler353
import Yulang.GeneralDeclarativeWitnessMixedWhole352
import Yulang.GeneralDeclarativeWitnessPathOrder352

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantSubtree353
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem)
open GeneralDeclarativeWitnessForest350 (Layout Fixed)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open GeneralSourceMetadataBareBundle291 (InputBundle compile)
open GeneralDeclarativeWitnessMixedForest352 (Global Code replayTree)
open GeneralDeclarativeWitnessMixedWhole352 (Accepted goal)
open GeneralDeclarativeWitnessTree349 (Report agrees)
open GeneralDeclarativeWitnessTagHeader352 (replay)
open GeneralDeclarations (Declaration)

def ordinarySource (p : Problem) : InputBundle :=
  let base := p.metadata.sourceInput
  {base with declarations := base.declarations.filter (fun c => c.role != p.demand.role)}

theorem all_other_roles_preserved (p : Problem) (d : Declaration) (other : d.role ≠ p.demand.role) :
    d ∈ (ordinarySource p).declarations ↔ d ∈ p.metadata.sourceInput.declarations := by
  unfold ordinarySource
  simp [other]

def problem (p : Problem) (s : State) (d : Demand) (t : Table) (layout : List Nat → Demand → Layout) :
    GeneralDeclarativeWitnessMixedForest352.Problem := ⟨ordinarySource p,s,t,d,layout⟩

structure Child (p : GeneralDeclarativeWitnessMixedForest352.Problem) (index : Nat)
    (d : Demand) (report : Report) where
  actual : Accepted p d report
  paths : actual.diagnostic.fixed.map Fixed.path =
    GeneralDeclarativeWitnessPathOrder352.preorder [index] actual.diagnostic.tree

/-- Existing C352 evidence verifies ordinary child branches at their
genuine occurrence paths, with unchanged role and constructor metadata.
The covariant root is not reclassified in the old carrier. -/
def decodeAt (p : GeneralDeclarativeWitnessMixedForest352.Problem) (index : Nat) (d : Demand)
    (w : Code) (report : Report) : Option (Child p index d report) :=
  match compiled : compile p.source with
  | none => none
  | some source => do
    let a ← attach p.current p.origins
    let g : Global p := ⟨source,compiled,a⟩
    match ran : replayTree g [index] d w with
    | none => none
    | some found =>
      match register : replay (goal p d) ⟨report.outputs⟩ with
      | none => none
      | some table =>
        if exactResult : agrees (goal p d) found.tree report = true then
          let r : Accepted p d report := ⟨g,found,table,register,exactResult⟩
          some ⟨r,GeneralDeclarativeWitnessPathOrder352.exact_tree w ran⟩
        else none

end Yulang.GeneralDeclarativeWitnessCovariantSubtree353
