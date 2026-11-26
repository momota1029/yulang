import Yulang.GeneralDeclarativeI65I74StructuralWherePairRead427

/-! Shared, finite C427 source snapshot and executable input witnesses for isolated audits.
    These are replay data, not an additional classifier or acceptance branch. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1600
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereAuditFixture429
open GeneralDeclarativeI65
open StructuralWhere427
open Checker408 (Problem)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarations (Declaration Clause)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation Read)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEmissionForest322 (Placement)
open RecordK2412 (closedHead412 query412 recordInput412 recordRow412)
open CommonNominalFullCarrier (Ty record subtype_refl Equivalent)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def recursiveWhere : Clause := ⟨6,19,[writtenRecord427 30 8 9],[]⟩
def compoundParent : Declaration := ⟨218,19,[closedHead412 30 31 9 8],[recursiveWhere],[],[]⟩
def scalarPattern : GeneralDeclarationPatterns.Pattern :=
  .record 30 (.app 10 []) (.app 9 [])
def scalarBase : Declaration := ⟨219,19,[scalarPattern],[],[],[]⟩
def surface (order : List Declaration) : InputBundle :=
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
    ⟨10,some ⟨[],10⟩,.primitive (.scalar .int)⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,order⟩

def deepRow : Equation := ⟨0,.record 30 (.variable 1) (.variable 2)⟩
def nestedRow : Equation := ⟨1,.record 31 (.variable 3) (.variable 2)⟩
def emptyRow : Equation := ⟨2,.primitive .emptyRecord []⟩
def integerRow : Equation := ⟨3,.primitive (.scalar .int) []⟩
def whereRow : Equation := recordRow412 4 30 3
def childDestructure : Equation := ⟨4,.record 30 (.variable 3) (.variable 2)⟩
def originalShape0 : Equation := recordRow412 0 30 1
def originalShape1 : Equation := recordRow412 1 31 3
def rows : List Equation :=
  [deepRow,nestedRow,emptyRow,integerRow,whereRow,childDestructure,originalShape0,originalShape1]
def auth : Origin := ⟨0,[32],recordInput412 30 1⟩
def build (order : List Declaration := [compoundParent,scalarBase])
    (ordinary : List Equation := rows) : Option Problem := do
  let graph ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile (surface order)
  let env : Environment := ⟨0,0,0,bodies,graph,source⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨env,⟨⟨[],[]⟩,ordinary⟩,[]⟩,[],[auth],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[71],⟨19,[point 0],[]⟩⟩⟩
def fixture : Problem := build.get (by decide +kernel)
def bindRoot (n : Nat) : Capture := if n = 8 then point 3 else point 0
def parentEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[0,1,2,1,2]⟩
def nestedEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,0,2,1,2]⟩
def childEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,2,2,1,0]⟩
def scalarEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,2,2,0,2]⟩
def blockedBase : RivalWire427 := ⟨1,6,7,parentEscape,nestedEscape⟩
def blockedCompound : RivalWire427 := ⟨0,4,3,childEscape,scalarEscape⟩
def say (n : Nat) : Ty :=
  if n = 0 then record 30 (record 31 (.base .int) .emptyRecord) .emptyRecord
  else if n = 1 then record 31 (.base .int) .emptyRecord
  else if n = 2 then .emptyRecord
  else if n = 4 then record 30 (.base .int) .emptyRecord
  else .base .int
def model : I72.Model :=
  ⟨fun n => (say n,Common.rowEmpty),fun _ => none,
    fun n => if n = 0 then some (recordInput412 30 1) else none⟩
theorem same_role_original_snapshot_fits427 : I72.Fits fixture.state model := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ e; cases e
  · intro _ e; cases e
  · intro e present
    change e ∈ rows at present
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ e; cases e
  · intro _ a
    change _ ∈ [auth] at a
    cases List.mem_singleton.mp a
    rfl

def reversedFixture : Problem := (build [scalarBase,compoundParent]).get (by decide +kernel)
def cyclic : Problem := (build (ordinary := rows ++ [⟨3,.variable 1⟩])).get (by decide +kernel)
end Yulang.GeneralDeclarativeI65.I72.StructuralWhereAuditFixture429

namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereReadback427
open GeneralDeclarativeI65
open StructuralWhere427
open StructuralWhereAuditFixture429
open GeneralDeclarativeWitnessDeclaredState357 (point)

def emptyEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,2,0,2,2]⟩
def rootHeadWire : PositiveHeadWire427 :=
  ⟨0,0,2,parentEscape,nestedEscape,emptyEscape,.nested 1 2 scalarEscape emptyEscape⟩
def leafHeadWire : PositiveHeadWire427 :=
  ⟨1,5,2,childEscape,scalarEscape,emptyEscape,.scalar 3⟩
def positiveWire : PositivePairWire427 :=
  ⟨rootHeadWire,4,leafHeadWire,blockedBase,blockedCompound⟩
theorem positiveWire_some :
    (readOriginalPositivePair427 fixture.state.core fixture.root positiveWire).isSome = true := by decide +kernel
def rebuilt : ReadPositivePair427 fixture.state.core fixture.root :=
  (readOriginalPositivePair427 fixture.state.core fixture.root positiveWire).get positiveWire_some

end Yulang.GeneralDeclarativeI65.I72.StructuralWhereReadback427
