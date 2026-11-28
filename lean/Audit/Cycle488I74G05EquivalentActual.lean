import Yulang.GeneralDeclarativeI65I74G05CoordinateDispatch488
import Yulang.GeneralDeclarativeI65I74ComputedOriginalRoots487
import Yulang.GeneralDeclarativeI65I74RecordEntry412

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485.EquivalentG05TaggedScope488
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

theorem duplicated_observations_preserve_signed_scope_but_missing_and_wrong_keys_do_not488 :
    ((scopedWireFromActual487 exactTwoVisited487 [none,some [12],none]).map fun w =>
      let check := checkFlatWithDemandScopedG05Tag488 unchangedFull verifiedGD candidatePositions candidatePairs
        [0,0] exactTwoVisited487 fixtureLocalOutcome487
      let first : G05CandidateRow487 4 := ⟨1,[exactFirstKey487],.requiredCycle⟩
      let second : G05CandidateRow487 4 := ⟨2,[],.nonrecursive .unresolved⟩
      let third : G05CandidateRow487 4 := ⟨3,[exactSecondKey487],.requiredCycle⟩
      (check (.inr (duplicateEachObservationList487 expectedPriorityReport487)) (.inr w),
       check (.inr {expectedPriorityReport487 with rows := [{first with observed := []},second,third]}) (.inr w),
       check (.inr {expectedPriorityReport487 with rows := [{first with observed := [exactSecondKey487]},second,third]}) (.inr w),
       check (.inr {expectedPriorityReport487 with rows := [third,second,first]}) (.inr w))) =
    some (true,false,false,false) := by
  decide +kernel

def zeroRoster488 : List Declaration := roster.map (fun d => {d with head := []})

def zeroSurface488 : InputBundle :=
  let primitives : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,primitives⟩,⟨.absent,primitives⟩,⟨0,[⟨7,0,[]⟩]⟩,zeroRoster488⟩

def buildZero488 : Option Problem := do
  let program ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile zeroSurface488
  let environment : Environment := ⟨0,0,0,bodies,program,source⟩
  let s : GeneralDeclarativeI65.State := ⟨⟨environment,⟨⟨[],[]⟩,[]⟩,[]⟩,[],[],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[71],⟨7,[],[]⟩⟩⟩

def actualZero488 := liftProblem (buildZero488.get (by decide +kernel))

def zeroGD488 : CheckedTable actualZero488.old.state.core.current :=
  (prepareTable (exampleCertificateProtocol487 actualZero488)
    [({inspectingFirst with head := []},()),({binderOnly with head := []},()),
      ({inspectingSecond with head := []},())]).get (by decide +kernel)

def zeroFixtureWitness488 : G05FiniteWitness487 4 :=
  ⟨[],[(1,⟨0,[]⟩),(2,⟨1,[]⟩),(3,⟨2,[]⟩)],[some [11],some [12],some [13]]⟩

def checkZero488 :=
  checkFlatWithDemandScopedG05Tag488 actualZero488 zeroGD488 candidatePositions candidatePairs
    [] noInspections487 fixtureLocalOutcome487

theorem zero_arguments_still_require_an_exact_finite_receipt_for_each_actual_visible_row488 :
    checkZero488 (.inr expectedNonrecursiveReport487) (.inr zeroFixtureWitness488) = true ∧
    checkZero488 (.inr expectedNonrecursiveReport487)
      (.inr {zeroFixtureWitness488 with localTokens := [some [11],none,some [13]]}) = false ∧
    checkZero488 (.inr expectedNonrecursiveReport487)
      (.inr {zeroFixtureWitness488 with tape := [(1,⟨0,[]⟩),(2,⟨0,[]⟩),(3,⟨2,[]⟩)]}) = false ∧
    checkZero488 (.inr {expectedNonrecursiveReport487 with priority := .recursive [3]})
      (.inr zeroFixtureWitness488) = false := by
  decide +kernel

theorem empty_scope_cannot_be_substituted_for_a_nonempty_original_demand488 :
    checkFlatWithDemandScopedG05Tag488 unchangedFull verifiedGD candidatePositions candidatePairs
      [] noInspections487 fixtureLocalOutcome487 (.inr expectedNonrecursiveReport487)
      (.inr zeroFixtureWitness488) = false := by
  decide +kernel

#print axioms duplicated_observations_preserve_signed_scope_but_missing_and_wrong_keys_do_not488
#print axioms zero_arguments_still_require_an_exact_finite_receipt_for_each_actual_visible_row488
#print axioms empty_scope_cannot_be_substituted_for_a_nonempty_original_demand488

def deepRaw487 : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[recordRow412 0 20 1,recordRow412 1 21 2,recordRow412 2 22 2]⟩

def deepFirstDecl487 : Declaration :=
  { inspectingFirst with head := [
      .record 20 (closedHead412 21 22 9 8) (.app 9 []),
      closedWhere412 20 9 14] }

def deepActual487 : Problem :=
  (build [outsideRole,deepFirstDecl487,binderOnly,inspectingSecond] deepRaw487).get (by decide +kernel)
def deepFull487 := liftProblem deepActual487

def deepPositions487 : Positions 6 :=
  let wireFor := fun n => (⟨[(n,.same)],⟨(List.range 3).map
    (fun j => if j = n then 1 else 0),[1]⟩⟩ : ClassWire)
  ⟨#v[⟨.logical 0,0⟩,⟨.logical 1,1⟩,⟨.logical 2,2⟩,
      ⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩,⟨.rowPos 2 [],2⟩],
    [.record [20],.record [21],.record [22]],
    #v[wireFor 0,wireFor 1,wireFor 2,wireFor 0,wireFor 1,wireFor 2]⟩

def deepPairs487 : List (Fin 6 × Fin 6) :=
  [(0,0),(0,3),(3,0),(3,3),(1,1),(1,4),(4,1),(4,4),(2,2),(2,5),(5,2),(5,5)]

def deepGD487 : CheckedTable deepFull487.old.state.core.current :=
  (prepareTable (exampleCertificateProtocol487 deepFull487) [(deepFirstDecl487,()),(binderOnly,()),(inspectingSecond,())]).get
    (by decide +kernel)


def deepFirstObservation488 : CandidateVisitKey485 6 :=
  ⟨0,[(.field 20,[.payload])],[0,1]⟩

def deepSecondObservation488 : CandidateVisitKey485 6 :=
  ⟨0,[(.field 20,[.payload]),(.field 21,[.payload])],[0,1,2]⟩

def deepPrior488 : Nat → CandidateVisitKey485 6 → Bool := fun ord key =>
  decide (ord = 1 ∧ (key = deepFirstObservation488 ∨ key = deepSecondObservation488))

def deepRebuiltWitness488 : Option (G05FiniteWitness487 6) := do
  let roots ← computedOriginalRootCertificates487 deepFull487.old.state.core deepPositions487 deepPairs487
    (deepFull487.old.root.demand.arguments.map (·.lower))
  let rows ← compileScopedRoster487 deepFull487 deepGD487 deepPositions487 deepPairs487
    (computedOriginalPalette486 deepFull487.old.state.core deepPositions487 deepPairs487)
    (roots.map Checkpoint.which) deepPrior488
  pure ⟨roots,rows.map (fun row => (row.authoredOrdinal,row.packet)),[none,some [12],some [13]]⟩

def deepPermutedReport488 : G05Report487 6 :=
  ⟨[⟨1,[deepSecondObservation488,deepFirstObservation488],.requiredCycle⟩,
    ⟨2,[],.nonrecursive .unresolved⟩,⟨3,[],.nonrecursive .rigidMismatch⟩],.recursive [1]⟩

set_option maxHeartbeats 2400000 in
theorem two_actual_deep_observations_can_change_report_order_but_not_witness_order488 :
    (deepRebuiltWitness488.map fun w =>
      let check := checkFlatWithDemandScopedG05Tag488 deepFull487 deepGD487 deepPositions487 deepPairs487
        [0,0] deepPrior488 fixtureLocalOutcome487
      (check (.inr deepPermutedReport488) (.inr w),
       checkFlatWithG05Tag487 deepFull487 deepGD487 deepPositions487 deepPairs487
         [0,0] deepPrior488 fixtureLocalOutcome487 (.inr deepPermutedReport488) (.inr w),
       check (.inr deepPermutedReport488)
         (.inr {w with tape := w.tape.map (fun pair => (pair.1,{pair.2 with paths := pair.2.paths.reverse}))}))) =
    some (true,false,false) := by
  decide +kernel

#print axioms two_actual_deep_observations_can_change_report_order_but_not_witness_order488

def fixtureRule488 : G05LocalMeaning487 := fun i ord d v =>
  ((i,ord,d.id) = (0,1,57) ∧ v = .rigidMatch) ∨
  ((i,ord,d.id) = (1,2,56) ∧ v = .unresolved) ∨
  ((i,ord,d.id) = (2,3,69) ∧ v = .rigidMismatch)

theorem fixture_local_protocol_is_independently_exact488 :
    G05ExactLocalProtocol487 fixtureLocalOutcome487 fixtureRule488 := by
  let triple := fun x : Nat × Nat × Nat × List Nat => (x.1,x.2.1,x.2.2.1)
  constructor
  · intro i ord d w mark ran
    unfold fixtureLocalOutcome487 at ran
    split at ran
    · exact .inl ⟨congrArg triple (by assumption), (Option.some.inj ran).symm⟩
    · split at ran
      · exact .inr (.inl ⟨congrArg triple (by assumption), (Option.some.inj ran).symm⟩)
      · split at ran
        · exact .inr (.inr ⟨congrArg triple (by assumption), (Option.some.inj ran).symm⟩)
        · cases ran
  · intro i ord d mark rule
    rcases rule with ⟨details,rfl⟩ | ⟨details,rfl⟩ | ⟨details,rfl⟩
    · obtain ⟨rfl,rfl,same⟩ : i = 0 ∧ ord = 1 ∧ d.id = 57 := by
        simpa only [Prod.mk.injEq] using details
      exact ⟨[11],by simp [fixtureLocalOutcome487,same]⟩
    · obtain ⟨rfl,rfl,same⟩ : i = 1 ∧ ord = 2 ∧ d.id = 56 := by
        simpa only [Prod.mk.injEq] using details
      exact ⟨[12],by simp [fixtureLocalOutcome487,same]⟩
    · obtain ⟨rfl,rfl,same⟩ : i = 2 ∧ ord = 3 ∧ d.id = 69 := by
        simpa only [Prod.mk.injEq] using details
      exact ⟨[13],by simp [fixtureLocalOutcome487,same]⟩

theorem zero_argument_fixture_meets_the_independent_original_scope488 :
    G05ExactVisitInputs487 actualZero488 zeroGD488 candidatePositions candidatePairs []
      noInspections487 (fun _ _ => False) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro ord key
    simp [noInspections487]
  · simp [OriginalRosterPermissionIsPrefixCoherent487,originalTerminalPermissionRespectsPrefixes487,noInspections487]
  · change True
    trivial
  · simp
  · simp

def zeroFixtureModel488 : I72.Model :=
  ⟨fun _ => (CommonNominalFullCarrier.record 20 .emptyRecord .emptyRecord,Common.rowEmpty),
    fun _ => none,fun _ => none⟩

theorem every_built_zero_argument_fixture_has_a_fitting_original_model488
    {p : Problem} (made : buildZero488 = some p) : I72.Fits p.state zeroFixtureModel488 := by
  unfold buildZero488 at made
  cases sem : compile bodies with
  | none => simp [sem] at made
  | some graph =>
    cases source : GeneralSourceMetadataBareBundle291.compile zeroSurface488 with
    | none => simp [sem,source] at made
    | some bundle =>
      simp only [sem,source,Option.pure_def] at made
      cases made
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩ <;> (intro _ empty; cases empty)

theorem zero_argument_scope_validation_retains_a_concrete_fitting_model_and_exact_local_evidence488 :
    I72.FitsFull actualZero488.state zeroFixtureModel488 ∧
    G05ExactCandidateReport487 actualZero488 zeroGD488 candidatePositions candidatePairs []
      (fun _ _ => False) fixtureRule488 expectedNonrecursiveReport487 ∧
    G05HasOriginalModelEvidence487 actualZero488 zeroGD488 candidatePositions candidatePairs []
      (fun _ _ => False) (fun _ => fixtureRule488) expectedNonrecursiveReport487 := by
  have original : I72.Fits (buildZero488.get (by decide +kernel)).state zeroFixtureModel488 :=
    every_built_zero_argument_fixture_has_a_fitting_original_model488 (Option.some_get _).symm
  have full : I72.FitsFull actualZero488.state zeroFixtureModel488 :=
    (I72.fits_iff_fitsFull_liftState _ _).mp original
  have accepted := zero_arguments_still_require_an_exact_finite_receipt_for_each_actual_visible_row488.1
  have replay := verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488
    _ zero_argument_fixture_meets_the_independent_original_scope488 fixtureRule488
    fixture_local_protocol_is_independently_exact488 (fun _ => fixtureRule488)
    (fun _ _ _ _ _ _ localMeaning => localMeaning) accepted
  exact ⟨full,replay.2⟩

#print axioms fixture_local_protocol_is_independently_exact488
#print axioms zero_argument_fixture_meets_the_independent_original_scope488
#print axioms zero_argument_scope_validation_retains_a_concrete_fitting_model_and_exact_local_evidence488

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485.EquivalentG05TaggedScope488
