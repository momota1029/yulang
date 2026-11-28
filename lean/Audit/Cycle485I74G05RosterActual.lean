import Yulang.GeneralDeclarativeI65I74MixedRecordEntry413
import Yulang.GeneralDeclarativeI65I74ElectionAfterTape485
import Yulang.GeneralDeclarativeI65I74CandidateSignedPath485

namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413.ExactRosterActual485
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible SourceHead)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty Equivalent record)
open RecordK2412 (closedWhere412 closedHead412 recordInput412 recordRow412)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def bindingOnly : Declaration := ⟨56,7,[closedWhere412 20 9 3],[],[],[]⟩
def bindingOther : Declaration := ⟨58,7,[closedWhere412 20 9 13],[],[],[]⟩
def inspecting : Declaration := ⟨57,7,[closedHead412 20 21 9 8],[],[],[]⟩

def surface (rows : List Declaration) : InputBundle :=
  let primitives : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,primitives⟩,⟨.absent,primitives⟩,⟨0,[⟨7,1,[]⟩]⟩,rows⟩

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
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩],[]⟩⟩⟩

def wire : MixedWire := ⟨⟨0,0,⟨[0,1],[0,1]⟩⟩,⟨⟨1,.same,1⟩,[],.same⟩⟩
def report : Result := Check408.rawReport
def checkOpt (p : Option Problem) (r : Result := report) (w : Witness := .mixedHead wire) : Bool :=
  (p.map fun data => check data r w).getD false


open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

def outsideRole : Declaration := {bindingOnly with id := 71, role := 11}
def unsupportedVisible : Declaration := {bindingOther with id := 73, head := [.var 29]}
def actual := build [outsideRole,inspecting,bindingOnly,bindingOther]
def permuted := build [outsideRole,bindingOther,bindingOnly,inspecting]
def actualExtra := build [outsideRole,inspecting,bindingOnly,bindingOther,unsupportedVisible]

def actualRegistryCells (op : Option Problem) : Option (List Nat × List Nat × List Nat) := do
  let p ← op
  let registry := (authoredRegistry p.state.core.current).declarations
  let entries := visible p.state.core p.root
  let source ← (List.range entries.length).mapM fun i =>
    unfilterOrdinal395 (fun d : Declaration => d.role == p.root.demand.role) registry i
  pure (registry.map Declaration.id,entries.map Declaration.id,source)

theorem wrong_role_registry_cell_is_filtered_without_renumbering_original_source :
    actualRegistryCells actual = some ([71,57,56,58],[57,56,58],[1,2,3]) ∧
    actualRegistryCells permuted = some ([71,58,56,57],[58,56,57],[1,2,3]) ∧
    actualRegistryCells actualExtra = some ([71,57,56,58,73],[57,56,58,73],[1,2,3,4]) := by
  decide +kernel

def actualOldOpening (op : Option Problem) : Option (Nat × Nat × Nat) := do
  let p ← op
  let hit ← replayMixed413 p wire
  let openAt := hit.rejection.tape.opening
  let selected ← unfilterOrdinal395 (fun d : Declaration => d.role == p.root.demand.role)
    (authoredRegistry p.state.core.current).declarations openAt.ordinal
  pure (openAt.ordinal,selected,openAt.decl.id)

theorem genuine_original_nested_visit_moves_both_ordinals_when_the_actual_roster_changes :
    actualOldOpening actual = some (0,1,57) ∧
    actualOldOpening permuted = some (2,3,57) ∧
    checkOpt actual = true ∧ checkOpt permuted = true ∧
    checkOpt actualExtra = false := by
  decide +kernel


open CandidateTape485 (rosterCell485)
open RetainedFull445 (liftProblem)

def expectedCells (op : Option Problem) : Option (List (Nat × Nat)) := do
  let p ← op
  (List.range (visible p.state.core p.root).length).mapM fun i =>
    (rosterCell485 (liftProblem p) i).map fun x => (x.1,x.2.id)

theorem actual_new_roster_cells_are_original_registry_ordinals_in_visible_order :
    expectedCells actual = some [(1,57),(2,56),(3,58)] ∧
    expectedCells permuted = some [(1,58),(2,56),(3,57)] ∧
    expectedCells actualExtra = some [(1,57),(2,56),(3,58),(4,73)] := by
  decide +kernel

def pastEnd : Option Nat := do
  let p ← actual
  (rosterCell485 (liftProblem p) 3).map Prod.fst

theorem a_nonvisible_slot_after_the_whole_roster_does_not_reuse_the_hidden_prefix :
    pastEnd = none := by decide +kernel

#print axioms actual_new_roster_cells_are_original_registry_ordinals_in_visible_order
#print axioms a_nonvisible_slot_after_the_whole_roster_does_not_reuse_the_hidden_prefix


def secondInspecting : Declaration := ⟨69,7,[closedHead412 20 21 9 18],[],[],[]⟩
def actualMultiple := build [outsideRole,inspecting,bindingOnly,secondInspecting,bindingOther]
def multiProblem : Problem := actualMultiple.get (by decide +kernel)
def multiRoot : VerifiedOuter multiProblem := (rootRead413 multiProblem wire.root).get (by decide +kernel)

def genuinelyNested {p : Problem} (root : VerifiedOuter p) (d : Declaration) :
    Option (NestedCandidate root.actual d) := do
  match ← readRow413 root.actual d with
  | .binding _ => none
  | .nested nested => some nested

def firstNested : NestedCandidate multiRoot.actual inspecting :=
  (genuinelyNested multiRoot inspecting).get (by decide +kernel)
def secondNested : NestedCandidate multiRoot.actual secondInspecting :=
  (genuinelyNested multiRoot secondInspecting).get (by decide +kernel)

open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeGraphRows321 (structural observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open RecordK2412 (query412 checkCycleAt412 cycle_at_sound412)

theorem two_original_nested_candidates_really_visit_one_cyclic_field_in_the_same_old_roster :
    (visible multiProblem.state.core multiProblem.root)[0]? = some inspecting ∧
    (visible multiProblem.state.core multiProblem.root)[2]? = some secondInspecting ∧
    firstNested.nextField = 21 ∧ secondNested.nextField = 21 ∧
    Visit (structural multiProblem.state.core.current.ordinary) multiRoot.actual.root
      (query412 multiRoot.actual.box firstNested.nextField firstNested.binder) multiRoot.actual.site ∧
    Visit (structural multiProblem.state.core.current.ordinary) multiRoot.actual.root
      (query412 multiRoot.actual.box secondNested.nextField secondNested.binder) multiRoot.actual.site ∧
    AliasCycle multiProblem.state.core.current.ordinary
      (observed multiProblem.state.core.current.ordinary) multiRoot.actual.site ∧
    checkOpt actualMultiple = false := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    actual_nested_candidate_enters413 firstNested,actual_nested_candidate_enters413 secondNested,?_,
    by decide +kernel⟩
  exact cycle_at_sound412 (show checkCycleAt412 multiProblem.state.core.current.ordinary
    multiRoot.actual.site wire.path = true by decide +kernel)

#print axioms two_original_nested_candidates_really_visit_one_cyclic_field_in_the_same_old_roster


open CandidateTape485 (readTape485)

def localOldCase {p : Problem} (atRoot : VerifiedOuter p)
    (_ordinal : Nat) (d : Declaration) (expectedId : Nat) : Option Bool := do
  if expectedId = d.id then
    match ← readRow413 atRoot.actual d with
    | .binding _ => some false
    | .nested _ =>
      if checkCycleAt412 p.state.core.current.ordinary atRoot.actual.site wire.path then some true
      else none
  else none

theorem local_old_true_has_an_actual_selected_visit_and_real_raw_cycle
    {p : Problem} {seen : VerifiedOuter p} {ord expected : Nat} {d : Declaration}
    (ran : localOldCase seen ord d expected = some true) :
    expected = d.id ∧ ∃ hit : NestedCandidate seen.actual d,
      Visit (structural p.state.core.current.ordinary) seen.actual.root
        (query412 seen.actual.box hit.nextField hit.binder) seen.actual.site ∧
      AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) seen.actual.site := by
  unfold localOldCase at ran
  split at ran
  · rename_i pin
    refine ⟨pin,?_⟩
    cases cell : readRow413 seen.actual d with
    | none => simp [cell] at ran
    | some caseData =>
      cases caseData with
      | binding _ => simp [cell] at ran
      | nested exactVisit =>
        simp only [cell,bind,Option.bind] at ran
        split at ran
        · rename_i found
          exact ⟨exactVisit,actual_nested_candidate_enters413 exactVisit,cycle_at_sound412 found⟩
        · cases ran
  · cases ran

def checkedOldWholeTape (op : Option Problem) (packets : List (Nat × Nat)) :
    Option (List (Nat × Bool)) := do
  let p ← op
  let outer ← rootRead413 p wire.root
  readTape485 (liftProblem p) (localOldCase outer) packets

def actualPackets : List (Nat × Nat) := [(1,57),(2,56),(3,58)]
def multiPackets : List (Nat × Nat) := [(1,57),(2,56),(3,69),(4,58)]
def permutedPackets : List (Nat × Nat) := [(1,58),(2,56),(3,57)]

theorem whole_tape_reads_both_genuine_nested_visits_and_never_rebinds_a_stale_ordinal :
    checkedOldWholeTape actual actualPackets = some [(1,true),(2,false),(3,false)] ∧
    checkedOldWholeTape actualMultiple multiPackets = some [(1,true),(2,false),(3,true),(4,false)] ∧
    checkedOldWholeTape permuted permutedPackets = some [(1,false),(2,false),(3,true)] ∧
    checkedOldWholeTape permuted actualPackets = none ∧
    checkedOldWholeTape actual [(0,57),(2,56),(3,58)] = none ∧
    checkedOldWholeTape actual [(1,57),(2,56),(2,56)] = none ∧
    checkedOldWholeTape actualExtra actualPackets = none ∧
    checkedOldWholeTape actualExtra (actualPackets ++ [(4,73)]) = none := by
  decide +kernel

#print axioms local_old_true_has_an_actual_selected_visit_and_real_raw_cycle
#print axioms whole_tape_reads_both_genuine_nested_visits_and_never_rebinds_a_stale_ordinal

def muBlock : CommonNominalSyntax.State Common.Row :=
  .block [.record 21 (.inl 0) .emptyRecord] 0
def mu : Ty := .record 21 muBlock .emptyRecord

theorem recursive_record_unfolds485 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth mu =
      CommonNominalFullCarrier.observeTy depth (record 21 mu .emptyRecord) := by
  cases depth <;> rfl

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then record 20 mu .emptyRecord else mu),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (recordInput412 20 1) else none⟩

theorem actual_X11_snapshot_fits485 {p : Problem} {rows : List Declaration} (ready : build rows = some p) :
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
          constructor <;> intro n <;> rw [← recursive_record_unfolds485 n] <;>
            exact CommonNominalFullDemand.producerLe_refl _
      · intro _ empty; cases empty
      · intro o exactOrigin
        obtain rfl := List.mem_singleton.mp exactOrigin
        rfl



open CandidateTape485 (PreElection485 beforeElection485)

def checkedOldPreElection (op : Option Problem) (packets : List (Nat × Nat)) :
    Option PreElection485 := do
  let p ← op
  let old ← rootRead413 p wire.root
  beforeElection485 (liftProblem p) (localOldCase old) packets

def bindingOnlyRoster := build [outsideRole,bindingOnly,bindingOther]

theorem both_owned_nested_hits_are_preserved_before_election_without_opening_binder_children :
    checkedOldPreElection actual actualPackets = some (.recursive [1]) ∧
    checkedOldPreElection actualMultiple multiPackets = some (.recursive [1,3]) ∧
    checkedOldPreElection permuted permutedPackets = some (.recursive [3]) ∧
    checkedOldPreElection bindingOnlyRoster [(1,56),(2,58)] = some (.allSafe [1,2]) ∧
    checkedOldPreElection actualExtra (actualPackets ++ [(4,73)]) = none := by
  decide +kernel

theorem multiple_original_nested_reads_are_on_an_inhabited_old_snapshot :
    I72.Fits multiProblem.state model :=
  actual_X11_snapshot_fits485 (Option.some_get _).symm

#print axioms both_owned_nested_hits_are_preserved_before_election_without_opening_binder_children
#print axioms multiple_original_nested_reads_are_on_an_inhabited_old_snapshot


open CandidateTape485 (routeAfterVerifiedTape485)

def routeWithSuppliedElection (op : Option Problem) (packets : List (Nat × Nat))
    (elect : List Nat → Option Nat) : Option (Sum (List Nat) Nat) := do
  let p ← op
  let prior ← rootRead413 p wire.root
  routeAfterVerifiedTape485 (liftProblem p) (localOldCase prior) packets elect

/-- The example callback is only a probe of the control transfer. It is
not a source match or election proof for the two safe candidates. -/
theorem actual_multi_visit_never_passes_the_supplied_election_even_if_it_returns_a_value :
    routeWithSuppliedElection actualMultiple multiPackets (fun _ => some 700) = some (.inl [1,3]) ∧
    routeWithSuppliedElection actualMultiple multiPackets (fun _ => none) = some (.inl [1,3]) ∧
    routeWithSuppliedElection bindingOnlyRoster [(1,56),(2,58)] (fun received =>
      if received = [1,2] then some 701 else none) = some (.inr 701) ∧
    routeWithSuppliedElection actualExtra actualPackets (fun _ => some 700) = none := by
  decide +kernel

#print axioms actual_multi_visit_never_passes_the_supplied_election_even_if_it_returns_a_value


open ObservationAlternatives473 (Positions graphOf oldPosition)
open ObservationRawAlias471 (ClassWire)
open LiteralVisits473 (Checkpoint StepWire readCheck read_checkpoint_guards)
open Producer479 (Site Hop readHop reified_hop_keeps_the_same_old_place479)
open QuotientObservation471 (ReturnsUpToEquality)

def candidatePositions : Positions 4 :=
  let wireFor := fun n => (⟨[(n,.same)],⟨(List.range 2).map
    (fun j => if j = n then 1 else 0),[1]⟩⟩ : ClassWire)
  ⟨#v[⟨.logical 0,0⟩,⟨.logical 1,1⟩,⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩],
    [.record [20],.record [21]],#v[wireFor 0,wireFor 1,wireFor 0,wireFor 1]⟩

def candidatePairs : List (Fin 4 × Fin 4) :=
  [(0,0),(0,2),(2,0),(2,2),(1,1),(1,3),(3,1),(3,3)]

def beforeNamedField : Checkpoint 4 :=
  ⟨0,2,2,⟨#v[0,1],#v[.structural 0 [1],.structural 1 [1]],0⟩,
    ⟨#v[0,1],#v[.structural 0 [1],.structural 1 [1]]⟩⟩

def selectedNamedField : Checkpoint 4 :=
  ⟨1,1,1,⟨#v[1],#v[.structural 1 [0]],0⟩,⟨#v[0],#v[.structural 1 [0]]⟩⟩

def originalRootSite (binder : Nat) : Site multiProblem.state.core candidatePositions :=
  ⟨0,closedHead412 20 21 9 binder,query412 20 21 binder,outer.right,rfl⟩

def selectBox : StepWire := ⟨.field 20,[.payload]⟩

def firstSelected : Site multiProblem.state.core candidatePositions :=
  (readHop (originalRootSite 8) selectBox 1).get (by decide +kernel)
def secondSelected : Site multiProblem.state.core candidatePositions :=
  (readHop (originalRootSite 18) selectBox 1).get (by decide +kernel)

theorem actual_two_head_hops_reach_the_same_old_positive_quotient_after_a_safe_root :
    Nonempty (Hop (originalRootSite 8) firstSelected selectBox) ∧
    Nonempty (Hop (originalRootSite 18) secondSelected selectBox) ∧
    oldPosition candidatePositions firstSelected.index = .logical 1 ∧
    oldPosition candidatePositions secondSelected.index = .logical 1 ∧
    ¬ ReturnsUpToEquality (graphOf multiProblem.state.core candidatePositions) 0 ∧
    ReturnsUpToEquality (graphOf multiProblem.state.core candidatePositions) 1 := by
  have exactBefore : readCheck multiProblem.state.core candidatePositions candidatePairs (.logical 0)
      beforeNamedField = some false := by decide +kernel
  have exactAfter : readCheck multiProblem.state.core candidatePositions candidatePairs (.logical 1)
      selectedNamedField = some true := by decide +kernel
  have stepOne : readHop (originalRootSite 8) selectBox 1 = some firstSelected :=
    (Option.some_get _).symm
  have stepTwo : readHop (originalRootSite 18) selectBox 1 = some secondSelected :=
    (Option.some_get _).symm
  exact ⟨(reified_hop_keeps_the_same_old_place479 stepOne).2,
    (reified_hop_keeps_the_same_old_place479 stepTwo).2,by decide +kernel,by decide +kernel,
    fun found => Bool.false_ne_true ((read_checkpoint_guards exactBefore).2.2.mpr found),
    (read_checkpoint_guards exactAfter).2.2.mp rfl⟩

#print axioms actual_two_head_hops_reach_the_same_old_positive_quotient_after_a_safe_root


open PreparedDeclarations463
open CandidateTape485 (CandidatePathWire485 CandidatePath485 readCandidatePath485
  reported_candidate_positive_owns_the_exact_original_ordinal_and_site485)

def unchangedFull := liftProblem multiProblem

def realGDResult : CertificateProtocol unchangedFull.old.state.core.current where
  Data := Unit
  verify d _ := RecordTrail455.localAuthorBits unchangedFull.old.state.core.current.environment d &&
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
  (prepareTable realGDResult [(inspecting,()),(bindingOnly,()),(secondInspecting,()),(bindingOther,())]).get
    (by decide +kernel)

def candidatePathWire : CandidatePathWire485 4 :=
  ⟨0,⟨beforeNamedField,[(selectBox,selectedNamedField)]⟩⟩

def fixturePath (i : Nat) :=
  readCandidatePath485 unchangedFull verifiedGD candidatePositions candidatePairs i candidatePathWire

def inspectSummary (i : Nat) : Option (Nat × Nat × Nat × Bool) :=
  (fixturePath i).map fun out =>
    (out.authoredOrdinal,out.head.orig.declaration.id,out.last.index.val,out.terminalBit)

theorem both_real_checked_candidate_heads_keep_own_authored_ordinal_and_live_quotient_terminal :
    inspectSummary 0 = some (1,57,1,true) ∧
    inspectSummary 2 = some (3,69,1,true) ∧
    inspectSummary 1 = none ∧
    inspectSummary 3 = none ∧
    inspectSummary 4 = none := by decide +kernel

theorem the_two_signed_checks_replay_two_actual_staged_geometries_not_a_made_up_singleton :
    ∃ (first : CandidatePath485 unchangedFull verifiedGD candidatePositions candidatePairs 0 candidatePathWire)
      (second : CandidatePath485 unchangedFull verifiedGD candidatePositions candidatePairs 2 candidatePathWire),
      fixturePath 0 = some first ∧ fixturePath 2 = some second ∧
      (CandidateTape485.declared485 unchangedFull)[first.authoredOrdinal]? = some inspecting ∧
      (CandidateTape485.declared485 unchangedFull)[second.authoredOrdinal]? = some secondInspecting ∧
      ReturnsUpToEquality (graphOf unchangedFull.old.state.core candidatePositions) first.last.index ∧
      ReturnsUpToEquality (graphOf unchangedFull.old.state.core candidatePositions) second.last.index := by
  let first := (fixturePath 0).get (by decide +kernel)
  let second := (fixturePath 2).get (by decide +kernel)
  have a := reported_candidate_positive_owns_the_exact_original_ordinal_and_site485 first
    (by decide +kernel) (by intro no; cases no)
  have b := reported_candidate_positive_owns_the_exact_original_ordinal_and_site485 second
    (by decide +kernel) (by intro no; cases no)
  refine ⟨first,second,(Option.some_get _).symm,(Option.some_get _).symm,?_,?_,a.2.2.1,b.2.2.1⟩
  · exact (show first.head.orig.declaration = inspecting by decide +kernel) ▸ a.1
  · exact (show second.head.orig.declaration = secondInspecting by decide +kernel) ▸ b.1

#print axioms both_real_checked_candidate_heads_keep_own_authored_ordinal_and_live_quotient_terminal
#print axioms the_two_signed_checks_replay_two_actual_staged_geometries_not_a_made_up_singleton

#print axioms wrong_role_registry_cell_is_filtered_without_renumbering_original_source
#print axioms genuine_original_nested_visit_moves_both_ordinals_when_the_actual_roster_changes

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413.ExactRosterActual485
