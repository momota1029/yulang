import Yulang.GeneralDeclarativeI65I74G05TaggedEntry487
import Yulang.GeneralDeclarativeI65I74ComputedOriginalRoots487
import Yulang.GeneralDeclarativeI65I74RecordEntry412

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485.ActualG05TaggedScope487
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem)
open CommonNominalFullCarrier (Ty Equivalent record)
open RecordK2412 (closedWhere412 closedHead412 recordInput412 recordRow412)
open RetainedFull445 (FullProblem liftProblem)
open PreparedDeclarations463 (CertificateProtocol CheckedTable prepareTable)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open LiteralVisits473 (Checkpoint)
open ObservationRawAlias471 (ClassWire)

def inspectingFirst : Declaration :=
  ⟨57,7,[closedHead412 20 21 9 8,closedWhere412 20 9 14],[],[],[]⟩
def inspectingSecond : Declaration :=
  ⟨69,7,[closedWhere412 20 9 18,closedHead412 20 21 9 24],[],[],[]⟩
def binderOnly : Declaration :=
  ⟨56,7,[closedWhere412 20 9 3,closedWhere412 20 9 13],[],[],[]⟩
def outsideRole : Declaration := {binderOnly with id := 71, role := 11}
def roster : List Declaration := [outsideRole,inspectingFirst,binderOnly,inspectingSecond]

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def surface (rows : List Declaration) : InputBundle :=
  let primitives : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,primitives⟩,⟨.absent,primitives⟩,⟨0,[⟨7,2,[]⟩]⟩,rows⟩

def outer : Equation := recordRow412 0 20 1
def cycle : Equation := recordRow412 1 21 1
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[outer,cycle]⟩

def build (rows : List Declaration) (raw : GeneralDeclarativeHead320.State := ordinary) :
    Option Problem := do
  let program ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile (surface rows)
  let environment : Environment := ⟨0,0,0,bodies,program,source⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨environment,raw,[]⟩,[],[⟨0,[22],recordInput412 20 1⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩,⟨0,0,0⟩],[]⟩⟩⟩


def actual : Problem := (build roster).get (by decide +kernel)
def unchangedFull := liftProblem actual
def candidatePositions : Positions 4 :=
  let wireFor := fun n => (⟨[(n,.same)],⟨(List.range 2).map
    (fun j => if j = n then 1 else 0),[1]⟩⟩ : ClassWire)
  ⟨#v[⟨.logical 0,0⟩,⟨.logical 1,1⟩,⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩],
    [.record [20],.record [21]],#v[wireFor 0,wireFor 1,wireFor 0,wireFor 1]⟩

def candidatePairs : List (Fin 4 × Fin 4) :=
  [(0,0),(0,2),(2,0),(2,2),(1,1),(1,3),(3,1),(3,3)]

def exampleCertificateProtocol487 (fp : FullProblem) : CertificateProtocol fp.old.state.core.current where
  Data := Unit
  verify d _ := RecordTrail455.localAuthorBits fp.old.state.core.current.environment d &&
    decide (d.requirements = [])
  sound := by
    intro d _ accepted
    obtain ⟨localBits,emptyBody⟩ := Bool.and_eq_true_iff.mp accepted
    obtain ⟨covered,sig,id,produces,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp localBits
    refine ⟨sig,id,produces,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl covered,?_⟩
    intro cl member
    rw [of_decide_eq_true emptyBody] at member
    cases member

def verifiedGD : CheckedTable unchangedFull.old.state.core.current :=
  (prepareTable (exampleCertificateProtocol487 unchangedFull) [(inspectingFirst,()),(binderOnly,()),(inspectingSecond,())]).get
    (by decide +kernel)


def exactFirstKey487 : CandidateVisitKey485 4 := ⟨0,[(.field 20,[.payload])],[0,1]⟩
def exactSecondKey487 : CandidateVisitKey485 4 := ⟨1,[(.field 20,[.payload])],[0,1]⟩

def exactTwoVisited487 (ord : Nat) (key : CandidateVisitKey485 4) : Bool :=
  decide (ord = 1 ∧ key = exactFirstKey487 ∨ ord = 3 ∧ key = exactSecondKey487)

def noInspections487 (_ : Nat) (_ : CandidateVisitKey485 4) : Bool := false

/-- Only an explicitly recognised local fixture receipt has a result.
The general source matcher behind this finite interface remains separate. -/
def fixtureLocalOutcome487 (visibleIndex ordinal : Nat) (d : Declaration)
    (input : List Nat) : Option G05LocalVerdict487 :=
  if (visibleIndex,ordinal,d.id,input) = (0,1,57,[11]) then some .rigidMatch
  else if (visibleIndex,ordinal,d.id,input) = (1,2,56,[12]) then some .unresolved
  else if (visibleIndex,ordinal,d.id,input) = (2,3,69,[13]) then some .rigidMismatch
  else none

def scopedWireFromActual487 (permit : Nat → CandidateVisitKey485 4 → Bool)
    (tokens : List (Option (List Nat))) : Option (G05FiniteWitness487 4) := do
  let roots ← computedOriginalRootCertificates487 unchangedFull.old.state.core candidatePositions candidatePairs
    (unchangedFull.old.root.demand.arguments.map (·.lower))
  let computed ← compileScopedRoster487 unchangedFull verifiedGD candidatePositions candidatePairs
    (computedOriginalPalette486 unchangedFull.old.state.core candidatePositions candidatePairs)
    (roots.map Checkpoint.which) permit
  pure ⟨roots,computed.map (fun row => (row.authoredOrdinal,row.packet)),tokens⟩

def readActualTaggedScope487 (permit : Nat → CandidateVisitKey485 4 → Bool)
    (tokens : List (Option (List Nat))) : Option (G05Report487 4) :=
  (scopedWireFromActual487 permit tokens).bind
    (readG05ScopedReport487 unchangedFull verifiedGD candidatePositions candidatePairs [0,0]
      permit fixtureLocalOutcome487)

def expectedPriorityReport487 : G05Report487 4 :=
  ⟨[⟨1,[exactFirstKey487],.requiredCycle⟩,
    ⟨2,[],.nonrecursive .unresolved⟩,
    ⟨3,[exactSecondKey487],.requiredCycle⟩],.recursive [1,3]⟩

def expectedNonrecursiveReport487 : G05Report487 4 :=
  ⟨[⟨1,[],.nonrecursive .rigidMatch⟩,⟨2,[],.nonrecursive .unresolved⟩,
    ⟨3,[],.nonrecursive .rigidMismatch⟩],.eligible [(1,.rigidMatch),(2,.unresolved),(3,.rigidMismatch)]⟩

theorem actual_tagged_scope_keeps_rigid_match_mismatch_and_unresolved_distinct487 :
    (readActualTaggedScope487 noInspections487 [some [11],some [12],some [13]]).map g05ReportData487 =
      some (g05ReportData487 expectedNonrecursiveReport487) := by
  decide +kernel

theorem actual_tagged_scope_reports_both_k2s_without_choosing_the_unresolved_rival487 :
    (readActualTaggedScope487 exactTwoVisited487 [none,some [12],none]).map g05ReportData487 =
      some (g05ReportData487 expectedPriorityReport487) := by
  decide +kernel

theorem wrong_or_missing_local_receipt_is_not_a_rigid_mismatch487 :
    (readActualTaggedScope487 noInspections487 [some [11],none,some [13]]).isNone = true ∧
    (readActualTaggedScope487 noInspections487 [some [11],some [13],some [12]]).isNone = true ∧
    (readActualTaggedScope487 exactTwoVisited487 [some [11],some [12],none]).isNone = true := by
  decide +kernel

theorem generated_actual_tag_requires_every_candidate_and_exact_priority487 :
    ((scopedWireFromActual487 exactTwoVisited487 [none,some [12],none]).map fun w =>
      (checkFlatWithG05Tag487 unchangedFull verifiedGD candidatePositions candidatePairs [0,0]
        exactTwoVisited487 fixtureLocalOutcome487 (.inr expectedPriorityReport487) (.inr w),
       checkFlatWithG05Tag487 unchangedFull verifiedGD candidatePositions candidatePairs [0,0]
        exactTwoVisited487 fixtureLocalOutcome487
        (.inr {expectedPriorityReport487 with priority := .eligible []}) (.inr w),
       checkFlatWithG05Tag487 unchangedFull verifiedGD candidatePositions candidatePairs [0,0]
        exactTwoVisited487 fixtureLocalOutcome487 (.inr expectedPriorityReport487)
        (.inr {w with tape := w.tape.dropLast}))) = some (true,false,false) := by
  decide +kernel

#print axioms actual_tagged_scope_keeps_rigid_match_mismatch_and_unresolved_distinct487
#print axioms actual_tagged_scope_reports_both_k2s_without_choosing_the_unresolved_rival487
#print axioms wrong_or_missing_local_receipt_is_not_a_rigid_mismatch487
#print axioms generated_actual_tag_requires_every_candidate_and_exact_priority487

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485.ActualG05TaggedScope487
