import Yulang.GeneralDeclarativeI65I74G05DeferredEntry489
import Yulang.GeneralDeclarativeI65I74G05AuthoredOrder489
import Yulang.GeneralDeclarativeI65I74G05SignedReceipt489
import Yulang.GeneralDeclarativeI65I74RecordEntry412

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485.G05PreflightActual489
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

def exampleCertificateProtocol489 (fp : FullProblem) : CertificateProtocol fp.old.state.core.current where
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
  (prepareTable (exampleCertificateProtocol489 unchangedFull) [(inspectingFirst,()),(binderOnly,()),(inspectingSecond,())]).get
    (by decide +kernel)


def exactFirstKey489 : CandidateVisitKey485 4 := ⟨0,[(.field 20,[.payload])],[0,1]⟩
def exactSecondKey489 : CandidateVisitKey485 4 := ⟨1,[(.field 20,[.payload])],[0,1]⟩

def exactTwoVisited489 (ord : Nat) (key : CandidateVisitKey485 4) : Bool :=
  decide (ord = 1 ∧ key = exactFirstKey489 ∨ ord = 3 ∧ key = exactSecondKey489)

def noInspections489 (_ : Nat) (_ : CandidateVisitKey485 4) : Bool := false

def reportResult489 : G05Continuation488 Nat → Nat × List Nat
  | .notReplayed => (0,[])
  | .blockedByK2 hits => (1,hits)
  | .continued value => (2,[value])

/-- Deliberately no local matcher results and no full report or receipt. -/
def onMissing489 (coords : List (Fin 4)) (permit : Nat → CandidateVisitKey485 4 → Bool) :
    Nat × List Nat :=
  reportResult489 <| routeG05WithDeferredLocal489 unchangedFull verifiedGD candidatePositions candidatePairs
    coords permit (fun _ _ _ _ => none) (fun _ => none) (fun _ => 999)

set_option maxHeartbeats 2300000 in
theorem two_actual_original_k2s_preempt_with_no_matcher_or_full_receipts489 :
    onMissing489 [0,0] exactTwoVisited489 = (1,[1,3]) := by
  decide +kernel

def onlyUnvisited489 (ord : Nat) (key : CandidateVisitKey485 4) : Bool :=
  decide (ord = 2 ∧ key = exactFirstKey489 ∨ ord = 1 ∧ key = exactSecondKey489)

/- The same cyclic node occurs on the raw graph; these permissions point
to a binder candidate or to the wrong original argument of a real opener. -/
set_option maxHeartbeats 2300000 in
theorem cyclic_points_at_unvisited_candidate_or_argument_do_not_create_positive_k2_489 :
    readG05Preflight489 unchangedFull verifiedGD candidatePositions candidatePairs [0,0] onlyUnvisited489 =
      some (.allSafe [1,2,3]) ∧
    onMissing489 [0,0] onlyUnvisited489 = (0,[]) := by
  decide +kernel

set_option maxHeartbeats 2300000 in
theorem correct_k2_receipts_cannot_override_a_nonoriginal_root_coordinate489 :
    readG05Preflight489 unchangedFull verifiedGD candidatePositions candidatePairs [0,1] exactTwoVisited489 = none ∧
    onMissing489 [0,1] exactTwoVisited489 = (0,[]) := by
  decide +kernel

def permutedActual489 : Problem :=
  (build [inspectingSecond,outsideRole,binderOnly,inspectingFirst]).get (by decide +kernel)
def permutedFull489 := liftProblem permutedActual489

def permutedGD489 : CheckedTable permutedFull489.old.state.core.current :=
  (prepareTable (exampleCertificateProtocol489 permutedFull489)
    [(inspectingSecond,()),(binderOnly,()),(inspectingFirst,())]).get (by decide +kernel)

def exactPermutedTwo489 (ord : Nat) (key : CandidateVisitKey485 4) : Bool :=
  decide (ord = 3 ∧ key = exactFirstKey489 ∨ ord = 0 ∧ key = exactSecondKey489)

set_option maxHeartbeats 2600000 in
theorem both_genuine_k2s_survive_registry_reordering_at_the_new_authored_ordinals489 :
    readG05Preflight489 permutedFull489 permutedGD489 candidatePositions candidatePairs [0,0]
      exactPermutedTwo489 = some (.recursive [0,3]) ∧
    reportResult489 (routeG05WithDeferredLocal489 permutedFull489 permutedGD489 candidatePositions
      candidatePairs [0,0] exactPermutedTwo489 (fun _ _ _ _ => none) (fun _ => none) (fun _ => 999)) =
      (1,[0,3]) := by
  decide +kernel

def twoAllowed489 (ord : Nat) (key : CandidateVisitKey485 4) : Prop :=
  ord = 1 ∧ key = exactFirstKey489 ∨ ord = 3 ∧ key = exactSecondKey489

theorem two_visited_permissions_are_independent_of_full_report_or_local_check489 :
    ∀ ord key, exactTwoVisited489 ord key = true ↔ twoAllowed489 ord key := by
  intro ord key
  simp only [exactTwoVisited489,twoAllowed489,decide_eq_true_eq]

set_option maxHeartbeats 2500000 in
theorem both_early_k2_hits_have_independent_original_visit_derivations489 :
    IndependentScopedReturn487 unchangedFull verifiedGD candidatePositions candidatePairs [0,0] twoAllowed489 0 ∧
    IndependentScopedReturn487 unchangedFull verifiedGD candidatePositions candidatePairs [0,0] twoAllowed489 2 := by
  have ran : readG05Preflight489 unchangedFull verifiedGD candidatePositions candidatePairs [0,0] exactTwoVisited489 =
      some (.recursive [1,3]) := by decide +kernel
  have exactHits := (a_successful_positive_g05_preflight_lists_every_and_only_the_actual_original_k2_slots489
    ran twoAllowed489 two_visited_permissions_are_independent_of_full_report_or_local_check489).2
  obtain ⟨i,⟨d,atFound⟩,one⟩ := (exactHits 1).mp (by simp)
  obtain ⟨j,⟨e,atAnother⟩,two⟩ := (exactHits 3).mp (by simp)
  have atOne : OriginalRosterCell485 unchangedFull 0 (1,inspectingFirst) :=
    (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp (by decide +kernel)
  have atTwo : OriginalRosterCell485 unchangedFull 2 (3,inspectingSecond) :=
    (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp (by decide +kernel)
  rw [two_visible_slots_cannot_claim_one_original_registry_ordinal485 unchangedFull atFound atOne] at one
  rw [two_visible_slots_cannot_claim_one_original_registry_ordinal485 unchangedFull atAnother atTwo] at two
  exact ⟨one,two⟩

def oneLocalReceipt489 (_i _ord : Nat) (_d : Declaration) (token : List Nat) : Option G05LocalVerdict487 :=
  if token = [12] then some .unresolved else none
def twoHitReport489 : G05Report487 4 :=
  ⟨[⟨1,[exactFirstKey489],.requiredCycle⟩,⟨2,[],.nonrecursive .unresolved⟩,
    ⟨3,[exactSecondKey489],.requiredCycle⟩],.recursive [1,3]⟩
def forgedThirdHitReport489 : G05Report487 4 :=
  ⟨[⟨1,[exactFirstKey489],.requiredCycle⟩,⟨2,[],.requiredCycle⟩,
    ⟨3,[exactSecondKey489],.requiredCycle⟩],.recursive [1,2,3]⟩

def twoHitWire489 : Option (G05FiniteWitness487 4) := do
  let roots ← computedOriginalRootCertificates487 unchangedFull.old.state.core candidatePositions candidatePairs
    (unchangedFull.old.root.demand.arguments.map (·.lower))
  let tape ← compileScopedRoster487 unchangedFull verifiedGD candidatePositions candidatePairs
    (computedOriginalPalette486 unchangedFull.old.state.core candidatePositions candidatePairs)
    (roots.map Checkpoint.which) exactTwoVisited489
  pure ⟨roots,tape.map (fun row => (row.authoredOrdinal,row.packet)),[none,some [12],none]⟩

set_option maxHeartbeats 4300000 in
theorem extra_claimed_k2_on_the_binder_fails_full_replay_and_does_not_change_early_hits489 :
    (twoHitWire489.map fun wire =>
      let full := checkFlatWithDemandScopedG05Tag488 unchangedFull verifiedGD candidatePositions candidatePairs
        [0,0] exactTwoVisited489 oneLocalReceipt489
      (full (.inr twoHitReport489) (.inr wire),
       full (.inr forgedThirdHitReport489) (.inr wire),
       reportResult489 (routeG05WithDeferredLocal489 unchangedFull verifiedGD candidatePositions candidatePairs
         [0,0] exactTwoVisited489 oneLocalReceipt489 (fun _ => some (forgedThirdHitReport489,wire))
         (fun _ => 999)))) = some (true,false,(1,[1,3])) := by
  decide +kernel

def signedFixtureReceipt489 : Option (G05SignedReceipt489 4) :=
  twoHitWire489.map (fun w => ⟨w.roots,w.tape⟩)

def readFixtureReceipt489 :=
  readG05SignedReceipt489 unchangedFull verifiedGD candidatePositions candidatePairs [0,0] exactTwoVisited489

def dropLastVisit489 (tape : List (Nat × PlannedCandidateWire485 4)) :
    List (Nat × PlannedCandidateWire485 4) :=
  tape.modify 2 (fun entry => (entry.1,{entry.2 with paths := []}))

set_option maxHeartbeats 5000000 in
theorem signed_only_receipt_replays_both_original_hits_and_rejects_a_missing_second_hit489 :
    (signedFixtureReceipt489.map fun r =>
      (readFixtureReceipt489 r,
       readFixtureReceipt489 {r with authoredTape := r.authoredTape.take 2},
       readFixtureReceipt489 {r with authoredTape := dropLastVisit489 r.authoredTape})) =
    some (some (.recursive [1,3]),none,none) := by
  decide +kernel

set_option maxHeartbeats 3300000 in
theorem swapping_signed_candidate_packets_is_not_a_registry_reordering489 :
    (signedFixtureReceipt489.map fun r =>
      readFixtureReceipt489 {r with authoredTape := r.authoredTape.reverse}) = some none := by
  decide +kernel

#print axioms signed_only_receipt_replays_both_original_hits_and_rejects_a_missing_second_hit489
#print axioms swapping_signed_candidate_packets_is_not_a_registry_reordering489

def inlineOuter489 : Equation :=
  ⟨0,.record 20 (.record 21 (.variable 1) (.primitive .emptyRecord [])) (.primitive .emptyRecord [])⟩
def inlineRaw489 : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[inlineOuter489,cycle]⟩
def inlineFull489 := liftProblem ((build roster inlineRaw489).get (by decide +kernel))
def inlineGD489 : CheckedTable inlineFull489.old.state.core.current :=
  (prepareTable (exampleCertificateProtocol489 inlineFull489)
    [(inspectingFirst,()),(binderOnly,()),(inspectingSecond,())]).get (by decide +kernel)

def inlinePositions489 : Positions 5 :=
  let certificate := fun raw => (⟨[(raw,.same)],⟨(List.range 2).map
    (fun j => if j = raw then 1 else 0),[1]⟩⟩ : ClassWire)
  ⟨#v[⟨.logical 0,0⟩,⟨.logical 1,1⟩,⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩,
       ⟨.rowPos 0 [.field 20],0⟩],
    [.record [20],.record [21]],#v[certificate 0,certificate 1,certificate 0,certificate 1,certificate 0]⟩

def inlinePairs489 : List (Fin 5 × Fin 5) :=
  [[0,2],[1,3,4]].flatMap (fun cls => (cls : List (Fin 5)).flatMap (fun i => cls.map (i,·)))

def inlineScopedAt489 (argument : Nat) : CandidateVisitKey485 5 :=
  ⟨argument,[(.field 20,[.payload])],[0,4]⟩
def permitInlineTwo489 (ord : Nat) (key : CandidateVisitKey485 5) : Bool :=
  decide (ord = 1 ∧ key = inlineScopedAt489 0 ∨ ord = 3 ∧ key = inlineScopedAt489 1)

set_option maxHeartbeats 4000000 in
theorem actual_unrolled_child_and_named_child_produce_the_same_early_g05_k2_list489 :
    readG05Preflight489 inlineFull489 inlineGD489 inlinePositions489 inlinePairs489 [0,0]
      permitInlineTwo489 =
    readG05Preflight489 unchangedFull verifiedGD candidatePositions candidatePairs [0,0] exactTwoVisited489 ∧
    readG05Preflight489 inlineFull489 inlineGD489 inlinePositions489 inlinePairs489 [0,0]
      permitInlineTwo489 = some (.recursive [1,3]) := by
  decide +kernel

abbrev rawGraph489 := graphOf inlineFull489.old.state.core inlinePositions489
def explicitRawGraph489 : CommonRoleRegularGraph.Graph 5 :=
  fun i => (#v[.structural 0 [4],.structural 1 [1],.structural 0 [4],
    .structural 1 [1],.structural 1 [1]]).get i
set_option maxHeartbeats 3800000 in
theorem concrete_inline_raw_graph_eq489 :
    rawGraph489 = explicitRawGraph489 := by
  funext i
  have casesI : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  rcases casesI with h|h|h|h|h
  · rw [show i = 0 from Fin.ext h]; decide +kernel
  · rw [show i = 1 from Fin.ext h]; decide +kernel
  · rw [show i = 2 from Fin.ext h]; decide +kernel
  · rw [show i = 3 from Fin.ext h]; decide +kernel
  · rw [show i = 4 from Fin.ext h]; decide +kernel
theorem actual_unrolled_observation_graph_is_acyclic_at_the_scanned_position489 :
    QuotientObservation471.checkOnCycle rawGraph489 4 = false := by
  rw [concrete_inline_raw_graph_eq489]
  decide +kernel
#print axioms concrete_inline_raw_graph_eq489
#print axioms actual_unrolled_observation_graph_is_acyclic_at_the_scanned_position489

def unlinkedInlinePairs489 : List (Fin 5 × Fin 5) :=
  [[0,2],[1,3],[4]].flatMap (fun cls => (cls : List (Fin 5)).flatMap (fun i => cls.map (i,·)))

set_option maxHeartbeats 3900000 in
theorem an_optional_relation_edge_is_not_the_computed_quotient_itself489 :
    readG05Preflight489 inlineFull489 inlineGD489 inlinePositions489 unlinkedInlinePairs489 [0,0]
      permitInlineTwo489 = some (.recursive [1,3]) := by
  decide +kernel

set_option maxHeartbeats 3900000 in
theorem a_forged_relation_between_different_constructor_shapes_never_certifies_k2_489 :
    (readG05Preflight489 inlineFull489 inlineGD489 inlinePositions489 ((0,4)::inlinePairs489)
      [0,0] permitInlineTwo489).isSome = false := by
  decide +kernel

#print axioms an_optional_relation_edge_is_not_the_computed_quotient_itself489
#print axioms a_forged_relation_between_different_constructor_shapes_never_certifies_k2_489
#print axioms actual_unrolled_child_and_named_child_produce_the_same_early_g05_k2_list489

#print axioms both_early_k2_hits_have_independent_original_visit_derivations489
#print axioms extra_claimed_k2_on_the_binder_fails_full_replay_and_does_not_change_early_hits489

#print axioms two_actual_original_k2s_preempt_with_no_matcher_or_full_receipts489
#print axioms cyclic_points_at_unvisited_candidate_or_argument_do_not_create_positive_k2_489
#print axioms correct_k2_receipts_cannot_override_a_nonoriginal_root_coordinate489
#print axioms both_genuine_k2s_survive_registry_reordering_at_the_new_authored_ordinals489

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485.G05PreflightActual489
