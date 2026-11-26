import Yulang.GeneralDeclarativeI65I74WhereGuard450

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.GuardedFixture
open Yulang.GeneralDeclarativeI65
open Checker408 (Result)
open RetainedFull445
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeGraphRows321 (literal_head)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarations (Declaration Clause)
open PresenceNormalForm (Atom)
open CommonNominalFullCarrier (Ty Equivalent nominal)
open CommonRoleOutermostResolver (Tree)
open List410 (listPoint410 invariantValue410 ExactEscapeWire)

def listSource : Source 2 1 0 :=
  ⟨[⟨90,[(.value,0)]⟩],
    (fun node => if node.val = 0 then .union .emptyRecord (.pair (.inr 0) (.inl 1))
      else .nominal 90 [.inl (.inr 0)]),fun _ => 0⟩

def goodClause : Clause := ⟨40,8,[.var 11],[]⟩
def badClause : Clause := ⟨41,9,[.var 12],[]⟩
def lastClause : Clause := ⟨42,10,[.var 11],[]⟩
def implParent (clauses : List Clause) : Declaration :=
  ⟨89,7,[.app 90 [.var 11],.app 90 [.var 12]],clauses,[],[]⟩
def implGood : Declaration := ⟨88,8,[.app 90 [.var 13]],[],[],[]⟩
def implLast : Declaration := ⟨87,10,[.app 90 [.var 14]],[],[],[]⟩

def surface (clauses : List Clause) : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[.type],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,2,[]⟩,⟨8,1,[]⟩,⟨9,1,[]⟩,⟨10,1,[]⟩]⟩,
    [implParent clauses,implGood,implLast]⟩

def rootEdge (x y : Nat) : Equation := ⟨x,.nominal 90 [.variable y]⟩
def selfAtom (x : Nat) : Atom Nat := .tyLe (.var x) (.var x)
def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨[selfAtom 1,selfAtom 6,selfAtom 4],[]⟩,
    [rootEdge 0 1,rootEdge 1 4,rootEdge 5 6,rootEdge 6 6,rootEdge 4 4]⟩

def parentRaw : GeneralDeclarativeHead320.State := { raw with equations := rootEdge 0 0 :: raw.equations }
def brokenChildRaw : GeneralDeclarativeHead320.State := { raw with
  equations := [rootEdge 0 1,rootEdge 1 4,rootEdge 5 6,rootEdge 4 4] }

def build (ordinary : GeneralDeclarativeHead320.State) (clauses : List Clause) : Option FullProblem := do
  let graph ← compile listSource
  let source ← GeneralSourceMetadataBareBundle291.compile (surface clauses)
  let env : Environment := ⟨2,1,0,listSource,graph,source⟩
  let core : GeneralDeclarativeI65.State :=
    ⟨⟨env,ordinary,[]⟩,List.replicate 90 [] ++ [[invariantValue410]],
      [⟨0,[42],listPoint410 90 1⟩,⟨5,[43],listPoint410 90 6⟩,⟨1,[44],listPoint410 90 4⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[27,31],⟨7,[point 0,point 5],[]⟩⟩⟩)

def clauses : List Clause := [goodClause,badClause]
def p : FullProblem := (build raw clauses).get (by decide +kernel)
def cycleAtParent : FullProblem := (build parentRaw clauses).get (by decide +kernel)
def onlyPayloadWasCyclic : FullProblem := (build brokenChildRaw clauses).get (by decide +kernel)
def three : FullProblem := (build raw [goodClause,lastClause,badClause]).get (by decide +kernel)
def reversed : FullProblem := (build raw [badClause,goodClause]).get (by decide +kernel)

def cut0 : ExactEscapeWire := ⟨List.range 7,[0,1,2,2,1,2,2]⟩
def cut5 : ExactEscapeWire := ⟨List.range 7,[2,2,2,2,2,0,1]⟩
def cut1 : ExactEscapeWire := ⟨List.range 7,[2,0,2,2,1,2,2]⟩
def parent : ParentWire := ⟨[0,1],[cut0,cut5]⟩
def safe : ChildWire := .leaf ⟨[2],[cut1]⟩
def looping : ChildWire := .raw ⟨0,⟨3,.same,6⟩,[],.same⟩
def wrongRoot : ChildWire := .raw ⟨0,⟨4,.same,4⟩,[],.same⟩
def wire : WhereWire := ⟨parent,[safe,looping]⟩

def expected : Result := ⟨.selected 89 [.selected 88 [],.rejected],.rejected,[]⟩
def expectThree : Result := ⟨.selected 89 [.selected 88 [],.selected 87 [],.rejected],.rejected,[]⟩
def expectReversed : Result := ⟨.selected 89 [.rejected,.selected 88 []],.rejected,[]⟩
def expectParentOnly : Result := ⟨.rejected,.rejected,[]⟩
def expectDropped : Result := ⟨.selected 89 [.rejected],.rejected,[]⟩

def actualParent : ParentSelection p.old :=
  ⟨implParent clauses,(readParentChoice p.old (implParent clauses) rfl parent).get (by decide +kernel)⟩

theorem original_two_requests_use_distinct_binders_and_source_slots450 :
    actualParent.children = [⟨[27,31,0],⟨8,[point 1],[]⟩⟩,⟨[27,31,1],⟨9,[point 6],[]⟩⟩] :=
  rfl


def sameInputDifferentClause : Clause := { goodClause with id := 43 }
def duplicate : FullProblem :=
  (build raw [goodClause,sameInputDifferentClause,badClause]).get (by decide +kernel)
def duplicateReport : Result := ⟨.selected 89 [.selected 88 [],.selected 88 [],.rejected],.rejected,[]⟩
def duplicateParent : ParentSelection duplicate.old :=
  ⟨implParent [goodClause,sameInputDifferentClause,badClause],
    (readParentChoice duplicate.old (implParent [goodClause,sameInputDifferentClause,badClause])
      rfl parent).get (by decide +kernel)⟩

theorem duplicate_is_not_fabricated_source_case450 :
    duplicateParent.children[0]? = some ⟨[27,31,0],⟨8,[point 1],[]⟩⟩ ∧
      duplicateParent.children[1]? = some ⟨[27,31,1],⟨8,[point 1],[]⟩⟩ ∧
      duplicateParent.children[2]? = some ⟨[27,31,2],⟨9,[point 6],[]⟩⟩ ∧
      goodClause.id ≠ sameInputDifferentClause.id :=
  ⟨rfl,rfl,rfl,by decide⟩

theorem promoted_rejects_same_input_duplicates_for_all_wires450 (w : WhereWire) :
    NoSiblingMerge.check_full450 duplicate duplicateReport (.whereRoot w) = false := by
  have actual : NoSiblingMerge.noSiblingMerge duplicate = false := by decide +kernel
  simp only [NoSiblingMerge.check_full450,actual,Bool.false_and]

def checked (p : FullProblem) (r : Result) (ws : List ChildWire) : Bool :=
  NoSiblingMerge.check_full450 p r (.whereRoot ⟨parent,ws⟩)

/-- info: [true, true, true, true, false, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval [checked p expected [safe,looping],checked three expectThree [safe,safe,looping],
  checked reversed expectReversed [looping,safe],
  WhereSites450.check_full450 duplicate duplicateReport (.whereRoot ⟨parent,[safe,safe,looping]⟩),
  checked duplicate duplicateReport [safe,safe,looping],checked p expectParentOnly [safe,looping],
  checked cycleAtParent expected [safe,looping],checked p expectDropped [looping],
  checked p expected [looping,safe],checked p expected [safe,wrongRoot],
  checked p expected [safe,looping,safe],checked onlyPayloadWasCyclic expected [safe,looping]]

#print axioms duplicate_is_not_fabricated_source_case450
#print axioms promoted_rejects_same_input_duplicates_for_all_wires450
end Yulang.GeneralDeclarativeI65.I72.WhereSites450.GuardedFixture
