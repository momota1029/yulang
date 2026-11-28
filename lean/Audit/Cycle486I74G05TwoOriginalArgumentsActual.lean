import Yulang.GeneralDeclarativeI65I74AutomaticPaletteEntry486
import Yulang.GeneralDeclarativeI65I74RecordEntry412

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485.TwoOriginalArgumentsActual486
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

theorem recursive_record_unfolds486 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth mu =
      CommonNominalFullCarrier.observeTy depth (record 21 mu .emptyRecord) := by
  cases depth <;> rfl

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then record 20 mu .emptyRecord else mu),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (recordInput412 20 1) else none⟩

theorem actual_snapshot_fits486 {p : Problem} {rows : List Declaration} (ready : build rows = some p) :
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
          constructor <;> intro n <;> rw [← recursive_record_unfolds486 n] <;>
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
  (prepareTable realGDResult [(inspectingFirst,()),(binderOnly,()),(inspectingSecond,())]).get
    (by decide +kernel)


def actualPalette : SignedPalette486 4 :=
  fun i => if i = 0 then some beforeNamedField else if i = 1 then some selectedNamedField else none

def permitExact (ordinal : Nat) (key : CandidateVisitKey485 4) : Bool :=
  decide ((ordinal = 1 ∧ key.argument = 0 ∨ ordinal = 3 ∧ key.argument = 1) ∧
    key.original = [(.field 20,[.payload])] ∧ key.points = [0,1])

def actualCompile :=
  compileWholeOriginalRoster486 unchangedFull verifiedGD candidatePositions candidatePairs actualPalette [0,0] permitExact

def computedRead (roots : List (Checkpoint 4)) :=
  readComputedPreElection486 unchangedFull verifiedGD candidatePositions candidatePairs actualPalette roots permitExact

theorem same_raw_root_keeps_each_distinct_original_head_argument_and_ordinal486 :
    (actualCompile.map fun rows => rows.map fun row =>
      (row.authoredOrdinal,row.packet.visibleOrdinal,row.keys.map (·.argument),row.packet.paths.length)) =
      some [(1,0,[0],1),(2,1,[],0),(3,2,[1],1)] := by
  decide +kernel

theorem independently_compiled_tape_prefers_both_visits_only_after_all_real_roots486 :
    computedRead [beforeNamedField,beforeNamedField] = some (.recursive [1,3]) ∧
    computedRead [beforeNamedField] = none ∧
    computedRead [beforeNamedField,selectedNamedField] = none ∧
    computedRead [beforeNamedField,beforeNamedField,beforeNamedField] = none := by
  decide +kernel

theorem exact_actual_independent_multiarg_snapshot_is_inhabited486 :
    I72.Fits actual.state model :=
  actual_snapshot_fits486 (Option.some_get _).symm

def incompletePalette (i : Fin 4) : Option (Checkpoint 4) :=
  if i = 0 then some beforeNamedField else none

theorem reachable_missing_terminal_is_unknown_not_an_all_safe_language_answer486 :
    readComputedPreElection486 unchangedFull verifiedGD candidatePositions candidatePairs incompletePalette
      [beforeNamedField,beforeNamedField] permitExact = some (.allSafe [1,2,3]) ∧
    readPaletteCoveredPreElection486 unchangedFull verifiedGD candidatePositions candidatePairs incompletePalette
      [beforeNamedField,beforeNamedField] permitExact = none ∧
    readPaletteCoveredPreElection486 unchangedFull verifiedGD candidatePositions candidatePairs actualPalette
      [beforeNamedField,beforeNamedField] permitExact = some (.recursive [1,3]) := by
  decide +kernel

#print axioms reachable_missing_terminal_is_unknown_not_an_all_safe_language_answer486
#print axioms same_raw_root_keeps_each_distinct_original_head_argument_and_ordinal486
#print axioms independently_compiled_tape_prefers_both_visits_only_after_all_real_roots486
#print axioms exact_actual_independent_multiarg_snapshot_is_inhabited486
def automaticallyComputedPalette486 : SignedPalette486 4 :=
  computedOriginalPalette486 unchangedFull.old.state.core candidatePositions candidatePairs

theorem actual_old_graph_computes_both_signed_certificates_without_external_palette486 :
    oldObservedSign486 unchangedFull.old.state.core candidatePositions candidatePairs
      automaticallyComputedPalette486 0 = some false ∧
    oldObservedSign486 unchangedFull.old.state.core candidatePositions candidatePairs
      automaticallyComputedPalette486 1 = some true := by
  decide +kernel

theorem same_two_argument_candidate_case_needs_no_external_palette_or_paths486 :
    readAutomaticPalettePreElection486 unchangedFull verifiedGD candidatePositions candidatePairs
      [beforeNamedField,beforeNamedField] permitExact =
        some (.recursive [1,3]) := by
  decide +kernel

theorem false_alternative_relation_cannot_build_a_checkpoint486 :
    (computeOldObservationCheckpoint486 unchangedFull.old.state.core candidatePositions
      [(0,1)] 0).isNone = true := by
  decide +kernel

#print axioms actual_old_graph_computes_both_signed_certificates_without_external_palette486
#print axioms same_two_argument_candidate_case_needs_no_external_palette_or_paths486
#print axioms false_alternative_relation_cannot_build_a_checkpoint486

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485.TwoOriginalArgumentsActual486
