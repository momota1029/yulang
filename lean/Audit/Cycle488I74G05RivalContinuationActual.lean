import Yulang.GeneralDeclarativeI65I74G05Continuation488
import Yulang.GeneralDeclarativeI65I74CheckExplicitPrefixRoster487
import Yulang.GeneralDeclarativeI65I74ComputedOriginalRoots487
import Yulang.GeneralDeclarativeI65I74RecordEntry412

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485.G05RivalContinuationActual488
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

def thirdUnresolved488 : Declaration := { binderOnly with id := 81 }

def rivalActual488 : Problem :=
  (build (roster ++ [thirdUnresolved488])).get (by decide +kernel)
def rivalFull488 := liftProblem rivalActual488

def rivalGD488 : CheckedTable rivalFull488.old.state.core.current :=
  (prepareTable (exampleCertificateProtocol487 rivalFull488)
    [(inspectingFirst,()),(binderOnly,()),(inspectingSecond,()),(thirdUnresolved488,())]).get (by decide +kernel)

def rivalOutcome488 (i ord : Nat) (d : Declaration) (wire : List Nat) : Option G05LocalVerdict487 :=
  if (i,ord,d.id,wire) = (0,1,57,[11]) then some .rigidMismatch
  else if (i,ord,d.id,wire) = (1,2,56,[12]) then some .rigidMatch
  else if (i,ord,d.id,wire) = (2,3,69,[13]) then some .rigidMatch
  else if (i,ord,d.id,wire) = (3,4,81,[14]) then some .unresolved
  else none

def rivalPrior488 (ord : Nat) (key : CandidateVisitKey485 4) : Bool :=
  decide (ord = 1 ∧ key = exactFirstKey487)

def makeRivalWitness488 (permit : Nat → CandidateVisitKey485 4 → Bool)
    (tokens : List (Option (List Nat))) : Option (G05FiniteWitness487 4) := do
  let roots ← computedOriginalRootCertificates487 rivalFull488.old.state.core
    candidatePositions candidatePairs (rivalFull488.old.root.demand.arguments.map (·.lower))
  let rows ← compileScopedRoster487 rivalFull488 rivalGD488 candidatePositions candidatePairs
    (computedOriginalPalette486 rivalFull488.old.state.core candidatePositions candidatePairs)
    (roots.map Checkpoint.which) permit
  pure ⟨roots,rows.map (fun row => (row.authoredOrdinal,row.packet)),tokens⟩

def trueRecursionAndTwoRigidMatches488 : G05Report487 4 :=
  ⟨[⟨1,[exactFirstKey487],.requiredCycle⟩,⟨2,[],.nonrecursive .rigidMatch⟩,
    ⟨3,[],.nonrecursive .rigidMatch⟩,⟨4,[],.nonrecursive .unresolved⟩],.recursive [1]⟩

def noRecursionAndTwoRigidMatches488 : G05Report487 4 :=
  ⟨[⟨1,[],.nonrecursive .rigidMismatch⟩,⟨2,[],.nonrecursive .rigidMatch⟩,
    ⟨3,[],.nonrecursive .rigidMatch⟩,⟨4,[],.nonrecursive .unresolved⟩],
    .eligible [(1,.rigidMismatch),(2,.rigidMatch),(3,.rigidMatch),(4,.unresolved)]⟩

def observableContinuation488 : G05Continuation488 Nat → Nat × List Nat
  | .notReplayed => (0,[])
  | .blockedByK2 ord => (1,ord)
  | .continued value => (2,[value])

set_option maxHeartbeats 2600000 in
theorem actual_k2_blocks_two_rigid_matches_and_an_unresolved_candidate_before_any_continuation488 :
    (makeRivalWitness488 rivalPrior488 [none,some [12],some [13],some [14]]).map
      (fun w =>
        let run := routeFromCheckedG05Report488 rivalFull488 rivalGD488 candidatePositions candidatePairs
          [0,0] rivalPrior488 rivalOutcome488 trueRecursionAndTwoRigidMatches488
        (observableContinuation488 (run w (fun _ => 18)),
         observableContinuation488 (run w (fun _ => 21)),
         observableContinuation488 (run {w with localTokens := w.localTokens.dropLast} (fun _ => 18)))) =
    some ((1,[1]),(1,[1]),(0,[])) := by
  decide +kernel

set_option maxHeartbeats 2600000 in
theorem no_k2_handoff_preserves_an_unresolved_candidate_alongside_both_rigid_matches488 :
    (makeRivalWitness488 noInspections487 [some [11],some [12],some [13],some [14]]).map
      (fun w =>
        observableContinuation488 (routeFromCheckedG05Report488 rivalFull488 rivalGD488 candidatePositions
          candidatePairs [0,0] noInspections487 rivalOutcome488 noRecursionAndTwoRigidMatches488 w
          (fun marks => if marks = [(1,.rigidMismatch),(2,.rigidMatch),(3,.rigidMatch),(4,.unresolved)]
            then 19 else 0))) = some (2,[19]) := by
  decide +kernel

#print axioms actual_k2_blocks_two_rigid_matches_and_an_unresolved_candidate_before_any_continuation488
#print axioms no_k2_handoff_preserves_an_unresolved_candidate_alongside_both_rigid_matches488

def rivalFixtureAllowed488 (ordinal : Nat) (key : CandidateVisitKey485 4) : Prop :=
  ordinal = 1 ∧ key = exactFirstKey487

def originalFixtureRootCertificates488 : List (Checkpoint 4) :=
  (computedOriginalRootCertificates487 rivalFull488.old.state.core candidatePositions candidatePairs
    (rivalFull488.old.root.demand.arguments.map (·.lower))).get (by decide +kernel)

set_option maxHeartbeats 1800000 in
theorem rival_fixture_has_checked_original_roots_and_independent_prior488 :
    G05ExactVisitInputs487 rivalFull488 rivalGD488 candidatePositions candidatePairs [0,0]
      rivalPrior488 rivalFixtureAllowed488 := by
  let source : ExplicitOriginalPermissions487 4 := [(1,exactFirstKey487)]
  have prior : checkExplicitPermission487 source = rivalPrior488 := by
    funext ord key
    simp [checkExplicitPermission487,rivalPrior488,source]
  have good : checkExplicitPermissionTable487 source = true := by decide +kernel
  have checked : TypedRootSafety482.requestRootCheck rivalFull488 candidatePositions
      candidatePairs originalFixtureRootCertificates488 = true := by decide +kernel
  have rooted : originalFixtureRootCertificates488.map Checkpoint.which = [0,0] := by decide +kernel
  have safety := TypedRootSafety482.requestRootCheckSound rivalFull488 candidatePositions candidatePairs
    originalFixtureRootCertificates488 checked
  have full := (all_checked_request_roots_carry_guards_and_exact_list_length487 checked).2
  refine ⟨?_,?_,rooted ▸ safety,rooted ▸ full,?_⟩
  · intro ord key
    simp [rivalPrior488,rivalFixtureAllowed488]
  · rw [←prior]
    exact explicit_table_check_gives_roster_prefix_coherence487 good _ _ _ _ _
  · intro i argument root found
    have route : root = (0 : Fin 4) := by
      have contains := List.mem_of_getElem? found
      simpa using contains
    subst root
    have idBound : i.val < 4 := by
      have count : (visible485 rivalFull488).length = 4 := by decide +kernel
      exact count ▸ i.isLt
    have indexSet : i.val ∈ [0,1,2,3] := by
      have casesByBound : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
      simpa using casesByBound
    have len : argument < 2 := (List.getElem?_eq_some_iff.mp found).1
    have argSet : argument ∈ [0,1] := by
      have both : argument = 0 ∨ argument = 1 := by omega
      simpa using both
    have checkedGrid : ([0,1,2,3] : List Nat).all (fun i =>
        ([0,1] : List Nat).all (fun a =>
          (readOriginalArgumentStart486 rivalFull488 rivalGD488 candidatePositions i a 0).isSome)) = true := by
      decide +kernel
    have atI := List.all_eq_true.mp checkedGrid _ indexSet
    have atArg := List.all_eq_true.mp atI _ argSet
    cases startAt : readOriginalArgumentStart486 rivalFull488 rivalGD488 candidatePositions i.val argument 0 with
    | none => simp [startAt] at atArg
    | some original => exact ⟨original⟩

def muBlock : CommonNominalSyntax.State Common.Row :=
  .block [.record 21 (.inl 0) .emptyRecord] 0
def mu : Ty := .record 21 muBlock .emptyRecord

theorem recursive_record_unfolds487 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth mu =
      CommonNominalFullCarrier.observeTy depth (record 21 mu .emptyRecord) := by
  cases depth <;> rfl

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then record 20 mu .emptyRecord else mu),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (recordInput412 20 1) else none⟩

theorem actual_snapshot_fits487 {p : Problem} {rows : List Declaration} (ready : build rows = some p) :
    I72.Fits p.state model := by
  unfold build at ready
  cases sem : compile bodies with
  | none => simp [sem] at ready
  | some graph =>
    cases source : GeneralSourceMetadataBareBundle291.compile (surface rows) with
    | none => simp [sem,source] at ready
    | some bundle =>
      simp only [sem,source,Option.pure_def] at ready
      cases ready
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ empty; cases empty
      · intro _ empty; cases empty
      · intro e member
        have choices : e = outer ∨ e = cycle := by
          simpa only [ordinary,List.mem_cons,List.not_mem_nil,or_false] using member
        rcases choices with rfl|rfl
        · exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
        · change Equivalent mu (record 21 mu .emptyRecord)
          constructor <;> intro n <;> rw [← recursive_record_unfolds487 n] <;>
            exact CommonNominalFullDemand.producerLe_refl _
      · intro _ empty; cases empty
      · intro o exactOrigin
        obtain rfl := List.mem_singleton.mp exactOrigin
        rfl

theorem the_four_candidate_rival_scope_has_a_concrete_fitting_original_model488 :
    I72.FitsFull rivalFull488.state model := by
  exact (I72.fits_iff_fitsFull_liftState _ _).mp
    (actual_snapshot_fits487 (Option.some_get _).symm)

#print axioms rival_fixture_has_checked_original_roots_and_independent_prior488
#print axioms the_four_candidate_rival_scope_has_a_concrete_fitting_original_model488

def permutedRichActual488 : Problem :=
  (build [thirdUnresolved488,inspectingSecond,outsideRole,inspectingFirst,binderOnly]).get (by decide +kernel)
def permutedRichFull488 := liftProblem permutedRichActual488

def permutedRichGD488 : CheckedTable permutedRichFull488.old.state.core.current :=
  (prepareTable (exampleCertificateProtocol487 permutedRichFull488)
    [(thirdUnresolved488,()),(inspectingSecond,()),(inspectingFirst,()),(binderOnly,())]).get (by decide +kernel)

def permutedRichLocal488 (i ord : Nat) (d : Declaration) (wire : List Nat) : Option G05LocalVerdict487 :=
  if (i,ord,d.id,wire) = (0,0,81,[14]) then some .unresolved
  else if (i,ord,d.id,wire) = (1,1,69,[13]) then some .rigidMatch
  else if (i,ord,d.id,wire) = (3,4,56,[12]) then some .rigidMatch
  else none

def permutedRichPermit488 (ord : Nat) (key : CandidateVisitKey485 4) : Bool :=
  decide (ord = 3 ∧ key = exactFirstKey487)

def permutedRivalWire488 : Option (G05FiniteWitness487 4) := do
  let roots ← computedOriginalRootCertificates487 permutedRichFull488.old.state.core
    candidatePositions candidatePairs (permutedRichFull488.old.root.demand.arguments.map (·.lower))
  let rows ← compileScopedRoster487 permutedRichFull488 permutedRichGD488 candidatePositions candidatePairs
    (computedOriginalPalette486 permutedRichFull488.old.state.core candidatePositions candidatePairs)
    (roots.map Checkpoint.which) permutedRichPermit488
  pure ⟨roots,rows.map (fun row => (row.authoredOrdinal,row.packet)),[some [14],some [13],none,some [12]]⟩

def permutedRivalReport488 : G05Report487 4 :=
  ⟨[⟨0,[],.nonrecursive .unresolved⟩,⟨1,[],.nonrecursive .rigidMatch⟩,
    ⟨3,[exactFirstKey487],.requiredCycle⟩,⟨4,[],.nonrecursive .rigidMatch⟩],.recursive [3]⟩

set_option maxHeartbeats 2200000 in
theorem real_registry_reordering_keeps_k2_before_both_rigid_rivals_at_the_rebased_ordinal488 :
    (permutedRivalWire488.map fun w =>
      observableContinuation488 (routeFromCheckedG05Report488 permutedRichFull488 permutedRichGD488
        candidatePositions candidatePairs [0,0] permutedRichPermit488 permutedRichLocal488
        permutedRivalReport488 w (fun _ => 0))) = some (1,[3]) := by
  decide +kernel

#print axioms real_registry_reordering_keeps_k2_before_both_rigid_rivals_at_the_rebased_ordinal488

def rivalIndependentLocal488 : G05LocalMeaning487 := fun i ordinal d mark =>
  ((i,ordinal,d.id) = (0,1,57) ∧ mark = .rigidMismatch) ∨
  ((i,ordinal,d.id) = (1,2,56) ∧ mark = .rigidMatch) ∨
  ((i,ordinal,d.id) = (2,3,69) ∧ mark = .rigidMatch) ∨
  ((i,ordinal,d.id) = (3,4,81) ∧ mark = .unresolved)

theorem the_rich_fixture_callback_is_exact_for_its_separate_local_rule488 :
    G05ExactLocalProtocol487 rivalOutcome488 rivalIndependentLocal488 := by
  let triple := fun x : Nat × Nat × Nat × List Nat => (x.1,x.2.1,x.2.2.1)
  constructor
  · intro i ord d w mark ran
    unfold rivalOutcome488 at ran
    split at ran
    · exact .inl ⟨congrArg triple (by assumption), (Option.some.inj ran).symm⟩
    · split at ran
      · exact .inr (.inl ⟨congrArg triple (by assumption), (Option.some.inj ran).symm⟩)
      · split at ran
        · exact .inr (.inr (.inl ⟨congrArg triple (by assumption), (Option.some.inj ran).symm⟩))
        · split at ran
          · exact .inr (.inr (.inr ⟨congrArg triple (by assumption), (Option.some.inj ran).symm⟩))
          · cases ran
  · intro i ord d mark rule
    rcases rule with ⟨detail,rfl⟩ | ⟨detail,rfl⟩ | ⟨detail,rfl⟩ | ⟨detail,rfl⟩
    · obtain ⟨rfl,rfl,identifier⟩ : i = 0 ∧ ord = 1 ∧ d.id = 57 := by
        simpa only [Prod.mk.injEq] using detail
      exact ⟨[11],by simp [rivalOutcome488,identifier]⟩
    · obtain ⟨rfl,rfl,identifier⟩ : i = 1 ∧ ord = 2 ∧ d.id = 56 := by
        simpa only [Prod.mk.injEq] using detail
      exact ⟨[12],by simp [rivalOutcome488,identifier]⟩
    · obtain ⟨rfl,rfl,identifier⟩ : i = 2 ∧ ord = 3 ∧ d.id = 69 := by
        simpa only [Prod.mk.injEq] using detail
      exact ⟨[13],by simp [rivalOutcome488,identifier]⟩
    · obtain ⟨rfl,rfl,identifier⟩ : i = 3 ∧ ord = 4 ∧ d.id = 81 := by
        simpa only [Prod.mk.injEq] using detail
      exact ⟨[14],by simp [rivalOutcome488,identifier]⟩

def inspectedRivalWitness488 : G05FiniteWitness487 4 :=
  (makeRivalWitness488 rivalPrior488 [none,some [12],some [13],some [14]]).get (by decide +kernel)

set_option maxHeartbeats 1800000 in
theorem the_nonempty_rival_witness_has_independent_report_and_model_evidence488 :
    G05ExactCandidateReport487 rivalFull488 rivalGD488 candidatePositions candidatePairs [0,0]
      rivalFixtureAllowed488 rivalIndependentLocal488 trueRecursionAndTwoRigidMatches488 ∧
    G05HasOriginalModelEvidence487 rivalFull488 rivalGD488 candidatePositions candidatePairs [0,0]
      rivalFixtureAllowed488 (fun _ => rivalIndependentLocal488) trueRecursionAndTwoRigidMatches488 ∧
    I72.FitsFull rivalFull488.state model := by
  have checked : checkFlatWithDemandScopedG05Tag488 rivalFull488 rivalGD488 candidatePositions candidatePairs
      [0,0] rivalPrior488 rivalOutcome488 (.inr trueRecursionAndTwoRigidMatches488)
      (.inr inspectedRivalWitness488) = true := by decide +kernel
  have beyond := verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488
    rivalFixtureAllowed488 rival_fixture_has_checked_original_roots_and_independent_prior488
    rivalIndependentLocal488 the_rich_fixture_callback_is_exact_for_its_separate_local_rule488
    (fun _ => rivalIndependentLocal488) (fun _ _ _ _ _ _ real => real) checked
  exact ⟨beyond.2.1,beyond.2.2,the_four_candidate_rival_scope_has_a_concrete_fitting_original_model488⟩

#print axioms the_rich_fixture_callback_is_exact_for_its_separate_local_rule488
#print axioms the_nonempty_rival_witness_has_independent_report_and_model_evidence488

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485.G05RivalContinuationActual488
