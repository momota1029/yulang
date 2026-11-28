import Yulang.GeneralDeclarativeI65I74CheckExplicitPrefixRoster487
import Yulang.GeneralDeclarativeI65I74RecordEntry412

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485.ScopedOriginalArgumentsActual487
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


def actualPalette : SignedPalette486 4 :=
  fun i => if i = 0 then some beforeNamedField else if i = 1 then some selectedNamedField else none

def permitExact (ordinal : Nat) (key : CandidateVisitKey485 4) : Bool :=
  decide ((ordinal = 1 ∧ key.argument = 0 ∨ ordinal = 3 ∧ key.argument = 1) ∧
    key.original = [(.field 20,[.payload])] ∧ key.points = [0,1])

def computedScopedReceipts487 :=
  computedOriginalRootCertificates487 unchangedFull.old.state.core candidatePositions candidatePairs
    (unchangedFull.old.root.demand.arguments.map (·.lower))

theorem repeated_actual_demands_keep_two_checked_receipts_in_order487 :
    computedScopedReceipts487.map (List.map Checkpoint.which) = some [0,0] := by
  decide +kernel

theorem the_two_argument_old_snapshot_is_real_and_fitting487 :
    I72.Fits actual.state model :=
  actual_snapshot_fits487 (Option.some_get _).symm

theorem automatic_scoped_roster_reaches_both_original_authored_positions487 :
    readAutomaticScopedPreElection487 unchangedFull verifiedGD candidatePositions candidatePairs permitExact =
      some (.recursive [1,3]) := by
  decide +kernel

theorem automatic_scoped_compiler_keeps_both_original_argument_numbers_and_omits_the_hidden_role487 :
    ((computedScopedReceipts487.bind fun roots =>
      compileScopedRoster487 unchangedFull verifiedGD candidatePositions candidatePairs
        (computedOriginalPalette486 unchangedFull.old.state.core candidatePositions candidatePairs)
        (roots.map Checkpoint.which) permitExact).map fun rows =>
      rows.map fun row => (row.authoredOrdinal,row.packet.visibleOrdinal,row.keys.map (·.argument),
        row.packet.paths.length)) = some [(1,0,[0],1),(2,1,[],0),(3,2,[1],1)] := by
  decide +kernel

def onlyOldRootCheckpoint487 (i : Fin 4) : Option (Checkpoint 4) :=
  if i = 0 then some beforeNamedField else none

def noPriorOpening487 (_ : Nat) (_ : CandidateVisitKey485 4) : Bool := false

theorem denied_prefix_needs_no_unused_sign_whilst_approved_missing_sign_declines487 :
    readScopedPreElection487 unchangedFull verifiedGD candidatePositions candidatePairs onlyOldRootCheckpoint487
      [beforeNamedField,beforeNamedField] noPriorOpening487 = some (.allSafe [1,2,3]) ∧
    readScopedPreElection487 unchangedFull verifiedGD candidatePositions candidatePairs onlyOldRootCheckpoint487
      [beforeNamedField,beforeNamedField] permitExact = none ∧
    readPaletteCoveredPreElection486 unchangedFull verifiedGD candidatePositions candidatePairs onlyOldRootCheckpoint487
      [beforeNamedField,beforeNamedField] noPriorOpening487 = none := by
  decide +kernel

theorem unsafe_or_unavailable_requested_root_cannot_generate_a_safe_receipt487 :
    computedOriginalRootCertificates487 unchangedFull.old.state.core candidatePositions candidatePairs [0,1] = none ∧
    computedOriginalRootCertificates487 unchangedFull.old.state.core candidatePositions candidatePairs [0,100] = none ∧
    readAutomaticScopedPreElection487 unchangedFull verifiedGD candidatePositions [(0,1)] permitExact = none := by
  decide +kernel

#print axioms repeated_actual_demands_keep_two_checked_receipts_in_order487
#print axioms the_two_argument_old_snapshot_is_real_and_fitting487
#print axioms automatic_scoped_roster_reaches_both_original_authored_positions487
#print axioms automatic_scoped_compiler_keeps_both_original_argument_numbers_and_omits_the_hidden_role487
#print axioms denied_prefix_needs_no_unused_sign_whilst_approved_missing_sign_declines487
#print axioms unsafe_or_unavailable_requested_root_cannot_generate_a_safe_receipt487

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

abbrev deepPrefix487 (key : CandidateVisitKey485 6) : Prop :=
  key.original = [(.field 20,[.payload])] ∧ key.points = [0,1]

abbrev deepTerminal487 (key : CandidateVisitKey485 6) : Prop :=
  key.original = [(.field 20,[.payload]),(.field 21,[.payload])] ∧ key.points = [0,1,2]

def deepTerminalOnly487 (ordinal : Nat) (key : CandidateVisitKey485 6) : Bool :=
  decide (ordinal = 1 ∧ key.argument = 0 ∧ deepTerminal487 key)

def deepAllPrefixes487 (ordinal : Nat) (key : CandidateVisitKey485 6) : Bool :=
  decide (ordinal = 1 ∧ key.argument = 0 ∧ (deepPrefix487 key ∨ deepTerminal487 key))

def deepReceipts487 :=
  computedOriginalRootCertificates487 deepFull487.old.state.core deepPositions487 deepPairs487
    (deepFull487.old.root.demand.arguments.map (·.lower))

theorem terminal_permission_without_ancestor_does_not_open_the_original_grandchild487 :
    (deepReceipts487.bind fun checks =>
      readAutomaticPalettePreElection486 deepFull487 deepGD487 deepPositions487 deepPairs487 checks
        deepTerminalOnly487) = some (.recursive [1]) ∧
    readAutomaticScopedPreElection487 deepFull487 deepGD487 deepPositions487 deepPairs487 deepTerminalOnly487 =
      some (.allSafe [1,2,3]) ∧
    readAutomaticScopedPreElection487 deepFull487 deepGD487 deepPositions487 deepPairs487 deepAllPrefixes487 =
      some (.recursive [1]) := by
  decide +kernel

#print axioms terminal_permission_without_ancestor_does_not_open_the_original_grandchild487

def suppliedShort487 : CandidateVisitKey485 6 :=
  ⟨0,[(.field 20,[.payload])],[0,1]⟩

def suppliedDeep487 : CandidateVisitKey485 6 :=
  ⟨0,[(.field 20,[.payload]),(.field 21,[.payload])],[0,1,2]⟩

def backedTable487 : ExplicitOriginalPermissions487 6 := [(1,suppliedShort487),(1,suppliedDeep487)]

theorem explicit_table_checks_proper_prefix_on_the_exact_candidate_argument_and_position487 :
    checkExplicitPermissionTable487 backedTable487 = true ∧
    checkExplicitPermissionTable487 [(1,suppliedDeep487)] = false ∧
    checkExplicitPermissionTable487 [(3,suppliedShort487),(1,suppliedDeep487)] = false ∧
    checkExplicitPermissionTable487 [(1,{suppliedShort487 with argument := 1}),(1,suppliedDeep487)] = false ∧
    checkExplicitPermissionTable487 [(1,{suppliedShort487 with points := [0,2]}),(1,suppliedDeep487)] = false := by
  decide +kernel

theorem safe_explicit_entry_declines_a_terminal_without_exact_prefix_instead_of_reporting_all_safe487 :
    readExplicitPrefixPreElection487 deepFull487 deepGD487 deepPositions487 deepPairs487
      [(1,suppliedDeep487)] = none := by
  decide +kernel

theorem backed_explicit_entries_replay_through_the_unchanged_checker_on_the_actual_deep_head487 :
    readExplicitPrefixPreElection487 deepFull487 deepGD487 deepPositions487 deepPairs487
      backedTable487 = some (.recursive [1]) := by
  decide +kernel

#print axioms explicit_table_checks_proper_prefix_on_the_exact_candidate_argument_and_position487
#print axioms safe_explicit_entry_declines_a_terminal_without_exact_prefix_instead_of_reporting_all_safe487
#print axioms backed_explicit_entries_replay_through_the_unchanged_checker_on_the_actual_deep_head487

def movedRoster487 : List Declaration :=
  [inspectingSecond,outsideRole,binderOnly,inspectingFirst]

def movedFull487 : FullProblem := liftProblem ((build movedRoster487).get (by decide +kernel))
def movedGD487 : CheckedTable movedFull487.old.state.core.current :=
  (prepareTable (exampleCertificateProtocol487 movedFull487)
    [(inspectingSecond,()),(binderOnly,()),(inspectingFirst,())]).get (by decide +kernel)

def movedTable487 : ExplicitOriginalPermissions487 4 :=
  [(0,⟨1,[(.field 20,[.payload])],[0,1]⟩),
   (3,⟨0,[(.field 20,[.payload])],[0,1]⟩)]

theorem reordering_the_actual_candidate_registry_rebases_ordinals_but_not_k2_priority487 :
    readExplicitPrefixPreElection487 movedFull487 movedGD487 candidatePositions candidatePairs movedTable487 =
      some (.recursive [0,3]) := by
  decide +kernel

#print axioms reordering_the_actual_candidate_registry_rebases_ordinals_but_not_k2_priority487

def possibleButUnvisitedTable487 : ExplicitOriginalPermissions487 4 :=
  [(2,⟨0,[(.field 20,[.payload])],[0,1]⟩),
   (1,⟨1,[(.field 20,[.payload])],[0,1]⟩)]

theorem a_structurally_valid_table_cannot_turn_an_unvisited_cycle_into_k2487 :
    checkExplicitPermissionTable487 possibleButUnvisitedTable487 = true ∧
    oldObservedSign486 unchangedFull.old.state.core candidatePositions candidatePairs
      (computedOriginalPalette486 unchangedFull.old.state.core candidatePositions candidatePairs) 1 = some true ∧
    readExplicitPrefixPreElection487 unchangedFull verifiedGD candidatePositions candidatePairs
      possibleButUnvisitedTable487 = some (.allSafe [1,2,3]) := by
  decide +kernel

#print axioms a_structurally_valid_table_cannot_turn_an_unvisited_cycle_into_k2487

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485.ScopedOriginalArgumentsActual487
