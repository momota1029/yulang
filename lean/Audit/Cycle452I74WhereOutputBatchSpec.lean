import Yulang.GeneralDeclarativeI65I74WhereOutputBatch452

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.PairBatchFixture452
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open List410 (listPoint410 invariantValue410 ExactEscapeWire)
open CommonNominalFullCarrier (Ty Equivalent nominal)
open PresenceNormalForm (Atom)
open Checker408 (Result)
open CommonRoleOutermostResolver (Tree)

def listSource : Source 2 1 0 :=
  ⟨[⟨90,[(.value,0)]⟩],
    (fun node => if node.val = 0 then .union .emptyRecord (.pair (.inr 0) (.inl 1))
      else .nominal 90 [.inl (.inr 0)]),fun _ => 0⟩

def whereFirst : Clause := ⟨60,8,[.var 11],[]⟩
def whereSecond : Clause := ⟨61,8,[.var 12],[]⟩
def whereThird : Clause := ⟨62,8,[.var 13],[]⟩

def authoredParent : Declaration :=
  ⟨89,7,[.app 90 [.var 11],.app 90 [.var 12],.app 90 [.var 13]],
    [whereFirst,whereSecond,whereThird],[],[]⟩

def safeImpl : Declaration := ⟨88,8,[.app 90 [.var 14]],[],[],[]⟩

def surface : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[.type],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,3,[]⟩,⟨8,1,[]⟩]⟩,[authoredParent,safeImpl]⟩

def edge (owner child : Nat) : Equation := ⟨owner,.nominal 90 [.variable child]⟩
def sourceAlias : Equation := ⟨6,.variable 1⟩
def self (p : Nat) : Atom Nat := .tyLe (.var p) (.var p)
def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨[self 1,self 6,self 4,self 2],[]⟩,[edge 0 1,edge 5 6,edge 7 4,edge 1 1,sourceAlias,edge 4 2]⟩

def roots : List Origin :=
  [⟨0,[42],listPoint410 90 1⟩,⟨5,[43],listPoint410 90 6⟩,⟨7,[44],listPoint410 90 4⟩,⟨4,[45],listPoint410 90 2⟩]

def build (ordinary : GeneralDeclarativeHead320.State) : Option FullProblem := do
  let graph ← compile listSource
  let author ← GeneralSourceMetadataBareBundle291.compile surface
  let env : Environment := ⟨2,1,0,listSource,graph,author⟩
  let state : GeneralDeclarativeI65.State :=
    ⟨⟨env,ordinary,[]⟩,List.replicate 90 [] ++ [[invariantValue410]],roots,[]⟩
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨state,atlas⟩,⟨[27,31],⟨7,[point 0,point 5,point 7],[]⟩⟩⟩)

def p : FullProblem := (build raw).get (by decide +kernel)
def noAlias : FullProblem := (build {raw with equations := [edge 0 1,edge 5 6,edge 7 4,edge 1 1]}).get (by decide +kernel)
def cycleAtParent : FullProblem := (build {raw with equations := edge 0 0 :: raw.equations}).get (by decide +kernel)

def cut (xs : List Nat) : ExactEscapeWire := ⟨List.range 8,xs⟩
def e0 := cut [0,1,2,2,2,2,1,2]
def e5 := cut [2,1,2,2,2,0,1,2]
def e7 := cut [2,2,1,2,1,2,2,0]
def e4 := cut [2,2,1,2,0,2,2,2]
def sep14 := cut [2,0,2,2,1,2,0,2]
def parent : ParentWire := ⟨[0,1,2],[e0,e5,e7]⟩
def w1 : RootWire := .cycle ⟨0,⟨3,.same,1⟩,[],.same⟩
def w6 : RootWire := .cycle ⟨0,⟨3,.forward 4,1⟩,[],.backward 4⟩
def w4 : RootWire := .safe e4
def statusWires : List RootWire := [w1,w6,w4]

def matrix : List (List ExactPairWire) :=
  [[.linked .same,.linked (.backward 4),.separate sep14],
   [.linked (.forward 4),.linked .same,.separate sep14],
   [.separate sep14,.separate sep14,.linked .same]]

def actualWire : SourceDiagnosticWire := ⟨parent,⟨⟨[17,17,99],matrix⟩,statusWires⟩⟩
open InternalK2452
open OutputPhase452

def pairSummary (p : FullProblem) (w : SourceDiagnosticWire) (i j : Nat) := do
  let record ← readInternalReport452 p w
  let pair ← readActualPhasePair452 record.original.diagnostics i j
  pure (pair.left.ordinal,pair.first.site.occurrence.identity,pair.first.request.occurrence,pair.first.capture,
    pair.right.ordinal,pair.second.site.occurrence.identity,pair.second.request.occurrence,pair.second.capture,
    pair.rows.length)

def isActualPair (x : FullProblem) (w : SourceDiagnosticWire) (a b : Nat) : Bool :=
  (pairSummary x w a b).isSome

def runBatch (p : FullProblem) (w : SourceDiagnosticWire) : Option (List (Nat × Nat) × Nat × List (List Nat)) :=
  (readInternalReport452 p w).map fun data =>
    let pairs := verifiedEmissionPairs452 data.original.diagnostics
    (pairs.map fun x => (x.left.ordinal,x.right.ordinal), (emissionRows pairs).length,
      data.groups.map fun g => g.marks.map OriginalMark.writtenId)

def expectedBatch : Option (List (Nat × Nat) × Nat × List (List Nat)) :=
  some ([(0,0),(0,1),(1,0),(1,1),(2,2)],0,[[60,61]])

def renamed : SourceDiagnosticWire := { actualWire with
  diagnostic := { actualWire.diagnostic with cohorts :=
    { actualWire.diagnostic.cohorts with labels := [101,101,7] } } }

def bogusClass : SourceDiagnosticWire := { actualWire with
  diagnostic := { actualWire.diagnostic with cohorts :=
    { actualWire.diagnostic.cohorts with labels := [17,17,17] } } }

/-- info: [true, true, true, false, false, false, false, false, false] -/
#guard_msgs in
#eval [
  pairSummary p actualWire 0 1 == some (0,60,[27,31,0],1,1,61,[27,31,1],6,0),
  runBatch p actualWire == expectedBatch,
  runBatch p renamed == expectedBatch,
  isActualPair p actualWire 0 2,
  isActualPair p actualWire 0 3,
  isActualPair p bogusClass 0 2,
  isActualPair noAlias actualWire 0 1,
  isActualPair cycleAtParent actualWire 0 1,
  (runBatch p bogusClass).isSome]

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.PairBatchFixture452
