import Yulang.GeneralDeclarativeI65I74G05LocalChoiceDeterminacy490
import Yulang.GeneralDeclarativeI65I74G05ReceiptOnlyReportReplay490
import Yulang.GeneralDeclarativeI65I74CheckExplicitPrefixRoster487
import Yulang.GeneralDeclarativeI65I74ComputedOriginalRoots487
import Yulang.GeneralDeclarativeI65I74RecordEntry412

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485.G05ExactOutcomesActual490
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem)

open RecordK2412 (closedWhere412 closedHead412 recordInput412 recordRow412)
open RetainedFull445 (FullProblem liftProblem)
open PreparedDeclarations463 (CertificateProtocol CheckedTable prepareTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open ObservationRawAlias471 (ClassWire)

def inspectingFirst : Declaration :=
  ⟨57,7,[closedHead412 20 21 9 8,closedWhere412 20 9 14],[],[],[]⟩
def anotherBinder : Declaration :=
  ⟨69,7,[closedWhere412 20 9 18,closedWhere412 20 9 24],[],[],[]⟩
def binderOnly : Declaration :=
  ⟨56,7,[closedWhere412 20 9 3,closedWhere412 20 9 13],[],[],[]⟩
def outsideRole : Declaration := {binderOnly with id := 71, role := 11}
def roster : List Declaration := [outsideRole,inspectingFirst,binderOnly,anotherBinder]

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def surface (rows : List Declaration) : InputBundle :=
  let primitives : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,primitives⟩,⟨.absent,primitives⟩,⟨0,[⟨7,2,[]⟩]⟩,rows⟩

def outer : Equation := recordRow412 0 20 1
def cycle : Equation := recordRow412 1 21 1
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[outer,cycle]⟩

def build (rows : List Declaration) :
    Option Problem := do
  let program ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile (surface rows)
  let environment : Environment := ⟨0,0,0,bodies,program,source⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨environment,ordinary,[]⟩,[],[⟨0,[22],recordInput412 20 1⟩],[]⟩
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

def fixtureTableProtocol490 (fp : FullProblem) : CertificateProtocol fp.old.state.core.current where
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
  (prepareTable (fixtureTableProtocol490 unchangedFull) [(inspectingFirst,()),(binderOnly,()),(anotherBinder,())]).get
    (by decide +kernel)


def actualKey490 : CandidateVisitKey485 4 := ⟨0,[(.field 20,[.payload])],[0,1]⟩
def candidateOpens490 (ord : Nat) (key : CandidateVisitKey485 4) : Prop :=
  ord = 1 ∧ key = actualKey490
def opens490 (ord : Nat) (key : CandidateVisitKey485 4) : Bool :=
  decide (ord = 1 ∧ key = actualKey490)
def noPrior490 (_ : Nat) (_ : CandidateVisitKey485 4) : Bool := false
def noPermission490 (_ : Nat) (_ : CandidateVisitKey485 4) : Prop := False

def roots490 : List (Checkpoint 4) :=
  (computedOriginalRootCertificates487 unchangedFull.old.state.core candidatePositions candidatePairs
    (unchangedFull.old.root.demand.arguments.map (·.lower))).get (by decide +kernel)

set_option maxHeartbeats 1700000 in
theorem actual_three_candidate_original_demand_has_an_exact_visit_scope490 :
    G05ExactVisitInputs487 unchangedFull verifiedGD candidatePositions candidatePairs [0,0]
      opens490 candidateOpens490 := by
  let declared : ExplicitOriginalPermissions487 4 := [(1,actualKey490)]
  have sameReader : checkExplicitPermission487 declared = opens490 := by
    funext ord key
    simp [checkExplicitPermission487,opens490,declared]
  have finite : checkExplicitPermissionTable487 declared = true := by decide +kernel
  have checked : TypedRootSafety482.requestRootCheck unchangedFull candidatePositions candidatePairs roots490 = true := by
    decide +kernel
  have rooted : roots490.map Checkpoint.which = [0,0] := by decide +kernel
  have safety := TypedRootSafety482.requestRootCheckSound unchangedFull candidatePositions candidatePairs roots490 checked
  have guards := (all_checked_request_roots_carry_guards_and_exact_list_length487 checked).2
  refine ⟨fun _ _ => by simp [opens490,candidateOpens490],?_,rooted ▸ safety,rooted ▸ guards,?_⟩
  · rw [←sameReader]
    exact explicit_table_check_gives_roster_prefix_coherence487 finite _ _ _ _ _
  · intro i argument root original
    have coordinate : root = (0 : Fin 4) := by
      simpa using List.mem_of_getElem? original
    subst root
    have count : (visible485 unchangedFull).length = 3 := by decide +kernel
    have bounded : i.val < 3 := count ▸ i.isLt
    have index : i.val ∈ [0,1,2] := by
      have choices : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      simpa using choices
    have boundedArg : argument < 2 := (List.getElem?_eq_some_iff.mp original).1
    have validArg : argument ∈ [0,1] := by
      have casesArg : argument = 0 ∨ argument = 1 := by omega
      simpa using casesArg
    have matrix : ([0,1,2] : List Nat).all (fun j =>
        ([0,1] : List Nat).all (fun a =>
          (readOriginalArgumentStart486 unchangedFull verifiedGD candidatePositions j a 0).isSome)) = true := by
      decide +kernel
    have row := List.all_eq_true.mp matrix _ index
    have cell := List.all_eq_true.mp row _ validArg
    cases found : readOriginalArgumentStart486 unchangedFull verifiedGD candidatePositions i.val argument 0 with
    | none => simp [found] at cell
    | some start => exact ⟨start⟩

theorem the_same_original_demand_with_no_prior_has_an_exact_visit_scope490 :
    G05ExactVisitInputs487 unchangedFull verifiedGD candidatePositions candidatePairs [0,0]
      noPrior490 noPermission490 := by
  obtain ⟨_,_,root,guard,start⟩ := actual_three_candidate_original_demand_has_an_exact_visit_scope490
  exact ⟨fun _ _ => by simp [noPrior490,noPermission490],
    by intro _ _ _ _ _ _ _ impossible; contradiction,root,guard,start⟩

def fixtureChoicesRule490 : G05LocalMeaning487 := fun i ord d v =>
  ((i,ord,d.id) = (0,1,57) ∧ (v = .rigidMismatch ∨ v = .unresolved)) ∨
  ((i,ord,d.id) = (1,2,56) ∧ v = .rigidMatch) ∨
  ((i,ord,d.id) = (2,3,69) ∧ v = .rigidMatch)

private instance (i ord : Nat) (d : Declaration) (v : G05LocalVerdict487) :
    Decidable (fixtureChoicesRule490 i ord d v) :=
  inferInstanceAs (Decidable
    (((i,ord,d.id) = (0,1,57) ∧ (v = .rigidMismatch ∨ v = .unresolved)) ∨
    ((i,ord,d.id) = (1,2,56) ∧ v = .rigidMatch) ∨
    ((i,ord,d.id) = (2,3,69) ∧ v = .rigidMatch)))

def decodeChoice490 (version : Nat) (token : List Nat) : Option G05LocalVerdict487 :=
  if token = [version,0] then some .rigidMatch
  else if token = [version,1] then some .rigidMismatch
  else if token = [version,2] then some .unresolved
  else none

def local490 (version : Nat) : G05LocalChecker487 := fun i ord d token => do
  let v ← decodeChoice490 version token
  if fixtureChoicesRule490 i ord d v then some v else none

theorem each_version_of_the_fixture_token_codec_realizes_the_same_independent_rule490
    (version : Nat) : G05ExactLocalProtocol487 (local490 version) fixtureChoicesRule490 := by
  constructor
  · intro i ord d token v replay
    unfold local490 at replay
    cases decoded : decodeChoice490 version token with
    | none => simp [decoded] at replay
    | some interpreted =>
      simp only [decoded,bind,Option.bind] at replay
      split at replay
      · rename_i allowed
        exact (Option.some.inj replay) ▸ allowed
      · cases replay
  · intro i ord d v allow
    cases v with
    | rigidMatch => exact ⟨[version,0],by simp [local490,decodeChoice490,allow]⟩
    | rigidMismatch => exact ⟨[version,1],by simp [local490,decodeChoice490,allow]⟩
    | unresolved => exact ⟨[version,2],by simp [local490,decodeChoice490,allow]⟩

def mismatchReport490 : G05Report487 4 :=
  ⟨[⟨1,[],.nonrecursive .rigidMismatch⟩,⟨2,[],.nonrecursive .rigidMatch⟩,⟨3,[],.nonrecursive .rigidMatch⟩],
    .eligible [(1,.rigidMismatch),(2,.rigidMatch),(3,.rigidMatch)]⟩
def unresolvedReport490 : G05Report487 4 :=
  ⟨[⟨1,[],.nonrecursive .unresolved⟩,⟨2,[],.nonrecursive .rigidMatch⟩,⟨3,[],.nonrecursive .rigidMatch⟩],
    .eligible [(1,.unresolved),(2,.rigidMatch),(3,.rigidMatch)]⟩

def fixtureFullWire490 (permits : Nat → CandidateVisitKey485 4 → Bool)
    (localTokens : List (Option (List Nat))) : Option (G05FiniteWitness487 4) := do
  let sources ← compileScopedRoster487 unchangedFull verifiedGD candidatePositions candidatePairs
    (computedOriginalPalette486 unchangedFull.old.state.core candidatePositions candidatePairs)
    (roots490.map Checkpoint.which) permits
  pure ⟨roots490,sources.map (fun row => (row.authoredOrdinal,row.packet)),localTokens⟩

def emit490 : List (Nat × G05LocalVerdict487) → Nat
  | (_, .rigidMismatch)::_ => 10
  | (_, .unresolved)::_ => 20
  | _ => 30

def observe490 : G05Continuation488 Nat → Nat × List Nat
  | .notReplayed => (0,[])
  | .blockedByK2 hits => (1,hits)
  | .continued value => (2,[value])

def fixtureRun490 (version : Nat) (permits : Nat → CandidateVisitKey485 4 → Bool)
    (r : G05Report487 4) (localTokens : List (Option (List Nat))) : Nat × List Nat :=
  observe490 (routeG05WithDeferredLocal489 unchangedFull verifiedGD candidatePositions candidatePairs
    [0,0] permits (local490 version) (fun _ => (fixtureFullWire490 permits localTokens).map (r,·)) emit490)

set_option maxHeartbeats 4400000 in
theorem same_ordered_g05_continuation_replays_with_fresh_tokens_but_stale_tokens_do_not_replay490 :
    fixtureRun490 12 noPrior490 mismatchReport490 [some [12,1],some [12,0],some [12,0]] = (2,[10]) ∧
    fixtureRun490 99 noPrior490 mismatchReport490 [some [99,1],some [99,0],some [99,0]] = (2,[10]) ∧
    fixtureRun490 99 noPrior490 mismatchReport490 [some [12,1],some [12,0],some [12,0]] = (0,[]) := by
  decide +kernel

set_option maxHeartbeats 4400000 in
theorem genuine_k2_preempts_stale_tokens_but_the_same_input_without_that_visit_does_not_replay490 :
    fixtureRun490 99 opens490 mismatchReport490 [some [12,1],some [12,0]] = (1,[1]) ∧
    fixtureRun490 99 noPrior490 mismatchReport490 [some [12,1],some [12,0]] = (0,[]) ∧
    fixtureRun490 99 noPrior490 unresolvedReport490 [some [99,1],some [99,0],some [99,0]] = (0,[]) := by
  decide +kernel

set_option maxHeartbeats 4400000 in
theorem two_genuinely_permitted_local_choices_reach_distinct_ordered_continuations_not_a_default490 :
    fixtureRun490 12 noPrior490 mismatchReport490 [some [12,1],some [12,0],some [12,0]] = (2,[10]) ∧
    fixtureRun490 12 noPrior490 unresolvedReport490 [some [12,2],some [12,0],some [12,0]] = (2,[20]) := by
  decide +kernel

def wireA490 : G05FiniteWitness487 4 :=
  (fixtureFullWire490 noPrior490 [some [12,1],some [12,0],some [12,0]]).get (by decide +kernel)

def wireB490 : G05FiniteWitness487 4 :=
  {wireA490 with localTokens := [some [99,1],some [99,0],some [99,0]]}

def checkFixture490 (codec : Nat) (r : G05Report487 4) (w : G05FiniteWitness487 4) : Bool :=
  checkFlatWithDemandScopedG05Tag488 unchangedFull verifiedGD candidatePositions candidatePairs
    [0,0] noPrior490 (local490 codec) (.inr r) (.inr w)

set_option maxHeartbeats 5000000 in
theorem checked_finite_fixture_replays_identically_after_only_local_token_replacement490 :
    wireA490.roots = wireB490.roots ∧ wireA490.tape = wireB490.tape ∧
    checkFixture490 12 mismatchReport490 wireA490 = true ∧
    checkFixture490 99 mismatchReport490 wireB490 = true ∧
    checkFixture490 99 mismatchReport490 wireA490 = false ∧
    checkFixture490 12 mismatchReport490 wireB490 = false := by
  refine ⟨rfl,rfl,?_⟩
  decide +kernel

set_option maxHeartbeats 3000000 in
theorem the_actual_fixture_instantiates_the_token_only_transport_theorem490 :
    ∃ fresh, checkFixture490 99 mismatchReport490 {wireA490 with localTokens := fresh} = true := by
  have accepted := checked_finite_fixture_replays_identically_after_only_local_token_replacement490.2.2.1
  exact the_accepted_g05_report_rechecks_after_only_local_tokens_change_for_any_actual_arity490
    (two_exact_local_protocols_cover_all_decoded_g05_verdicts490
      (each_version_of_the_fixture_token_codec_realizes_the_same_independent_rule490 12)
      (each_version_of_the_fixture_token_codec_realizes_the_same_independent_rule490 99)) accepted

def toVersion490 (version : Nat) : G05TokenMap490
  | _,_,_,_,.rigidMatch => some [version,0]
  | _,_,_,_,.rigidMismatch => some [version,1]
  | _,_,_,_,.unresolved => some [version,2]

theorem explicit_fixture_token_map_is_lawful_between_every_two_versions490 (a b : Nat) :
    G05TokenMapPreservesDecoded490 (local490 a) (local490 b) (toVersion490 b) := by
  intro i ord d evidence mark checked
  have meaning := (each_version_of_the_fixture_token_codec_realizes_the_same_independent_rule490 a).1 i ord d evidence mark checked
  cases mark with
  | rigidMatch => exact ⟨[b,0],rfl,by simp [local490,decodeChoice490,meaning]⟩
  | rigidMismatch => exact ⟨[b,1],rfl,by simp [local490,decodeChoice490,meaning]⟩
  | unresolved => exact ⟨[b,2],rfl,by simp [local490,decodeChoice490,meaning]⟩

set_option maxHeartbeats 4000000 in
theorem explicit_fixture_token_map_computes_fresh_receipts_without_rebuilding_the_source_wire490 :
    (translateG05WitnessTokens490 unchangedFull (local490 12) (toVersion490 99) wireA490).map
        G05FiniteWitness487.localTokens = some [some [99,1],some [99,0],some [99,0]] ∧
    (translateG05WitnessTokens490 unchangedFull (local490 12) (toVersion490 99) wireA490).map
        (checkFixture490 99 mismatchReport490) = some true ∧
    (translateG05WitnessTokens490 unchangedFull (local490 12)
      (fun _ _ _ _ _ => some [99,2]) wireA490).map
        (checkFixture490 99 mismatchReport490) = some false := by
  decide +kernel

#print axioms actual_three_candidate_original_demand_has_an_exact_visit_scope490
#print axioms the_same_original_demand_with_no_prior_has_an_exact_visit_scope490
#print axioms each_version_of_the_fixture_token_codec_realizes_the_same_independent_rule490
#print axioms same_ordered_g05_continuation_replays_with_fresh_tokens_but_stale_tokens_do_not_replay490
#print axioms genuine_k2_preempts_stale_tokens_but_the_same_input_without_that_visit_does_not_replay490
#print axioms two_genuinely_permitted_local_choices_reach_distinct_ordered_continuations_not_a_default490
#print axioms checked_finite_fixture_replays_identically_after_only_local_token_replacement490
#print axioms the_actual_fixture_instantiates_the_token_only_transport_theorem490
#print axioms explicit_fixture_token_map_is_lawful_between_every_two_versions490
#print axioms explicit_fixture_token_map_computes_fresh_receipts_without_rebuilding_the_source_wire490

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485.G05ExactOutcomesActual490
