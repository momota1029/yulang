import Yulang.GeneralDeclarativeI65I74CompletedInterior484
import Yulang.GeneralDeclarativeI65I74ExactIndependentSourceEvent484
import Yulang.GeneralDeclarativeI65I74RootedInteriorReport483
import Yulang.GeneralDeclarativeI65I74MarkedRootOrigin475
import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.CompletedInteriorActual484
open Yulang.GeneralDeclarativeI65
open WrittenPattern460 (CoreState)
open RetainedFull445
open ObservationSyntax471
open RecordTraversal455.MixedQA
open AuthenticatedHop458 (Wire)
open InlineStructuralPolicy458 (Ticket emptyPolicy)
open RoutedNominalPoint456
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open CommonNominalFullCarrier (Ty Equivalent record)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Core.PresenceGeneration (TyTerm)
open List410 (ExactEscapeWire)
open RecordK2412 (FieldCycleWire)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open PreparedDeclarations463
open PhysicalVisit463.IssuedProjection464
open NativeProducer465 (CheckedPhase)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessTypedRelease354 (Stamp)
open GeneralDeclarativeWitnessNativeOrder362 (node)

def stamped : Stamp := ⟨[33,1],19,410,3⟩
def address : GeneralDeclarativeWitnessNativeValue360.Address := ⟨stamped,0,0,0,4,0⟩
def placed : Write := ⟨address,.leaf 4⟩

def bodies := GeneralDeclarativeWitnessVarianceFixtures357.source
def empty : Expr := .primitive .emptyRecord []
def buildProblem (decl : Declaration) (physicalState : GeneralDeclarativeHead320.State) : Option FullProblem := do
  let graph ← compile bodies
  let auth ← GeneralSourceMetadataBareBundle291.compile
    (let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
      ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
     ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[decl]⟩)
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,physicalState,[]⟩,List.replicate 20 [] ++ [[cov]],
    [originalOfWrite placed],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 4],[]⟩⟩⟩)


open InputCoordinates475
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open ObservationAlternatives473 (Positions Place)
open ObservationRawAlias471 (ClassWire)
open LiteralVisits473 (Checkpoint)
open ObservationSyntax471 (CheckedFieldBit)
open Yulang.GeneralDeclarativeI65.I72.Producer479
open LiteralVisits473 (readCheck read_checkpoint_guards pathEndsWithField)
open ObservationAlternatives473 (graphOf oldPosition readTermAt)
open QuotientObservation471 (ReturnsUpToEquality)
open GeneralDeclarativeWitnessOrigins350 (support)
open LiteralFold471 (inputSourceOnly)


open SourceExposure481.ClosedBank
open WrittenPattern460.PhysicalOrigin (Pose)
open LiteralVisits473 (StepWire)

def queryPattern : Pattern :=
  .record 30 (.record 40 (.record 50 (.var 3) (.app 9 [])) (.app 9 [])) (.app 9 [])
def declaration : Declaration := ⟨218,19,[queryPattern],[],[],[]⟩
def rootRaw : Equation := ⟨4,.record 30 (.variable 6) empty⟩
def wrap (e : Expr) : Expr := .record 50 e empty
def authoredRaw : Equation := ⟨6,.record 40 (wrap (.variable 7)) empty⟩
def ambientRaw : Equation := ⟨6,.record 40 (wrap (wrap (.variable 7))) empty⟩
def recurrence : Equation := ⟨7,wrap (.variable 7)⟩
def rawOriginal : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[rootRaw,authoredRaw,ambientRaw,recurrence]⟩
def problem : FullProblem := (buildProblem declaration rawOriginal).get (by decide +kernel)

def cert : CertificateProtocol problem.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = declaration)
  sound := by
    intro d _ yes
    obtain rfl : d = declaration := of_decide_eq_true yes
    have test : RecordTrail455.localAuthorBits problem.old.state.core.current.environment declaration = true := by decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp test
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c h; cases h

def gd := (prepareTable cert [(declaration,())]).get (by decide +kernel)
def table : Table := ⟨[authoredRaw],[(rootRaw,77),(ambientRaw,99),(recurrence,99)],[77]⟩

def clazz (n : Nat) : ClassWire :=
  ⟨[(n,.same)],⟨(List.range 8).map (fun i => if i = n then 1 else 0),[1]⟩⟩

def positions : Positions 10 :=
  ⟨#v[⟨.logical 4,0⟩,⟨.logical 6,2⟩,⟨.logical 7,3⟩,
      ⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩,⟨.rowPos 2 [],2⟩,
      ⟨.rowPos 1 [.field 40],1⟩,⟨.rowPos 2 [.field 40],2⟩,
      ⟨.rowPos 2 [.field 40,.field 50],2⟩,⟨.rowPos 3 [],3⟩],
    [.record [30],.record [40],.record [50]],
    #v[clazz 4,clazz 6,clazz 7,clazz 4,clazz 6,clazz 6,clazz 6,clazz 6,clazz 6,clazz 7]⟩
def pairs : List (Fin 10 × Fin 10) :=
  ([[0,3],[1,4,5],[2,6,7,8,9]] : List (List (Fin 10))).flatMap
    fun block => block.flatMap fun i => block.map fun j => (i,j)

def before : Checkpoint 10 :=
  ⟨1,4,2,⟨#v[1,7,8,2],#v[.structural 1 [1],.structural 2 [2],.structural 2 [3],.structural 2 [3]],0⟩,
    ⟨#v[0,1,1,1],#v[.structural 1 [1],.structural 2 [1]]⟩⟩
def finish : Checkpoint 10 :=
  ⟨7,3,1,⟨#v[7,8,2],#v[.structural 2 [1],.structural 2 [2],.structural 2 [2]],0⟩,
    ⟨#v[0,0,0],#v[.structural 2 [0]]⟩⟩

def head : PrecheckedHead (p := problem.old) gd :=
  (readPrecheckedHead (p := problem.old) gd ⟨0,0⟩).get (by decide +kernel)
def root : Site problem.old.state.core positions :=
  ⟨0,head.orig.original,head.orig.code,rootRaw.right,rfl⟩
def ambient : Site problem.old.state.core positions :=
  (readHop root ⟨.field 30,[.payload]⟩ 1).get (by decide +kernel)

def card (raw : Nat) : ReadCard :=
  .record [⟨⟨raw,0⟩,[]⟩] [40] [(40,wrap (.variable 3))] empty
    (.cons (.record [] [50] [(50,.variable 3)] empty
      (.cons .capture .nil) (.primitive .nil)) .nil) (.primitive .nil)


def outer : Checkpoint 10 :=
  ⟨0,5,3,⟨#v[0,1,7,8,2],#v[.structural 0 [1],.structural 1 [2],.structural 2 [3],.structural 2 [4],.structural 2 [4]],0⟩,
    ⟨#v[0,1,2,2,2],#v[.structural 0 [1],.structural 1 [2],.structural 2 [2]]⟩⟩
def association : CompletedAssociation := ⟨77,0,rootRaw,placed,0⟩
def prior : PriorPhase := ⟨table,[association],none⟩
def phase : CheckedPhase problem.old.state.core :=
  ⟨⟨rawAt problem,⟨[stamped],[placed]⟩⟩,rfl,⟨[address]⟩⟩
def rootCard : ReadCard :=
  .record [⟨⟨0,1⟩,[]⟩] [30] [(30,.record 40 (wrap (.variable 3)) empty)] empty
    (.cons (card 1) .nil) (.primitive .nil)
def approachWire : NamedTerminalWire 10 :=
  ⟨0,0,outer,[],⟨.field 30,[.payload]⟩,before,rootCard,1,[outer]⟩
def phrase : RootedInteriorWire 10 :=
  ⟨approachWire,[(6,finish,⟨.field 40,[.payload]⟩)]⟩
def initial : CompletedInteriorWire 10 := ⟨phrase,77,0,⟨placed,0⟩⟩
def readAt := readCompletedInterior problem gd positions pairs prior
def sameReport := (readAt phase initial).map (·.output.outcome)
def olderPlacement : Write := {placed with address := {address with owner := {stamped with version := 2}}}
def bothGrants : CheckedPhase problem.old.state.core := {phase with gate := ⟨[address,olderPlacement.address]⟩}
def tested := [
  sameReport == some ([.payload,.payload],[.field 30,.field 40],.rowPos 2 [.field 40],true),
  (readAt {phase with gate := ⟨[]⟩} initial).isNone,
  (readCompletedInterior problem gd positions pairs {prior with completed := []} phase initial).isNone,
  (readAt phase {initial with producedOrdinal := 1}).isNone,
  (readCompletedInterior problem gd positions pairs {prior with
    completed := [{association with write := olderPlacement}]} bothGrants
      {initial with release := ⟨olderPlacement,0⟩}).isNone,
  (readRootedInterior problem gd positions pairs prior phrase).isNone]

/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval tested

def recursiveTy : Ty := .record 50 (.block [.record 50 (.inl 0) .emptyRecord] 0) .emptyRecord

theorem recursiveTy_unfolds : Equivalent recursiveTy (record 50 recursiveTy .emptyRecord) := by
  have eq (k : Nat) : CommonNominalFullCarrier.observeTy k recursiveTy =
      CommonNominalFullCarrier.observeTy k (record 50 recursiveTy .emptyRecord) := by cases k <;> rfl
  constructor
  · intro k; rw [←eq k]; exact CommonNominalFullDemand.producerLe_refl _
  · intro k; rw [eq k]; exact CommonNominalFullDemand.producerLe_refl _

def beforeTy : Ty := record 40 recursiveTy .emptyRecord

def sameFit : I72.Model :=
  ⟨fun n => ((if n = 4 then record 30 beforeTy .emptyRecord
      else if n = 6 then beforeTy
      else if n = 7 then recursiveTy else .emptyRecord),Common.rowEmpty),fun _ => none,fun n => if n = 4 then some (node placed.code) else none⟩

theorem actual_rooted_interior_has_an_original_fit :
    FitsFull problem.state sameFit ∧ problem.old.root.demand.outputs = [] ∧
      ambientRaw ∉ table.authored ∧ (ambientRaw,99) ∈ table.produced ∧ 99 ∉ table.released := by
  refine ⟨?_,rfl,by decide +kernel,by decide +kernel,by decide⟩
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [rootRaw,authoredRaw,ambientRaw,recurrence] at h
    have found : row = rootRaw ∨ row = authoredRaw ∨ row = ambientRaw ∨ row = recurrence := by
      simpa using h
    rcases found with rfl | rfl | rfl | rfl
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr _
        recursiveTy_unfolds (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
    · exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr _
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans recursiveTy_unfolds
          (GeneralNominalCenteredHeadMatPatternSemantics.record_congr _
            recursiveTy_unfolds (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)))
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
    · exact recursiveTy_unfolds
  · intro _ h; cases h
  · intro orig hit
    change orig ∈ [originalOfWrite placed] at hit
    obtain rfl := List.mem_singleton.mp hit
    rfl
  · intro _ h; cases h


#print axioms actual_rooted_interior_has_an_original_fit
def previousSource : PriorPhase :=
  ⟨⟨[rootRaw,authoredRaw],[(ambientRaw,99),(recurrence,99)],[]⟩,[],some [⟨0,0⟩,⟨1,1⟩]⟩
def previousSourceCard : ReadCard :=
  .record [⟨⟨0,0⟩,[]⟩] [30] [(30,.record 40 (wrap (.variable 3)) empty)] empty
    (.cons (.record [⟨⟨1,1⟩,[]⟩] [40] [(40,wrap (.variable 3))] empty
      (.cons (.record [] [50] [(50,.variable 3)] empty
        (.cons .capture .nil) (.primitive .nil)) .nil) (.primitive .nil)) .nil) (.primitive .nil)
def previousSourceWire : RootedInteriorWire 10 :=
  {phrase with approach := {phrase.approach with source := previousSourceCard, initialAuthor := 0}}
def previousSourceAnswer :=
  (readRootedInterior problem gd positions pairs previousSource previousSourceWire).map (·.report.outcome)

theorem identical_old_problem_can_keep_separate_accepted_source_and_release_receipts :
    previousSourceWire.route = phrase.route ∧
    previousSourceAnswer = some ([.payload,.payload],[.field 30,.field 40],.rowPos 2 [.field 40],true) ∧
    sameReport = some ([.payload,.payload],[.field 30,.field 40],.rowPos 2 [.field 40],true) ∧
    FitsFull problem.state sameFit ∧
    rootRaw ∈ previousSource.authors.authored ∧ rootRaw ∉ prior.authors.authored := by
  exact ⟨rfl,by decide +kernel,by decide +kernel,actual_rooted_interior_has_an_original_fit.1,
    by decide +kernel,by decide +kernel⟩

#print axioms identical_old_problem_can_keep_separate_accepted_source_and_release_receipts

theorem full_signed_report_erases_which_prior_authority_was_used :
    ∃ a : RootedInteriorReceipt problem gd positions pairs previousSource previousSourceWire,
      ∃ b : CompletedInterior problem gd positions pairs prior phase initial,
        readRootedInterior problem gd positions pairs previousSource previousSourceWire = some a ∧
        readAt phase initial = some b ∧ a.report = b.output ∧
        ∀ identify : SamePhaseInputObservation478 → Bool,
          ¬ (identify a.report = true ∧ identify b.output = false) := by
  have known := identical_old_problem_can_keep_separate_accepted_source_and_release_receipts
  cases a : readRootedInterior problem gd positions pairs previousSource previousSourceWire with
  | none => simp [previousSourceAnswer,a] at known
  | some author =>
    cases b : readAt phase initial with
    | none => simp [sameReport,b] at known
    | some released =>
      have originEq := completed_interior_keeps_original_release_and_scoped_report released
      have sameFrames := Option.some.inj (author.exactReport.symm.trans released.focused.exactReport)
      have same : author.report = released.output := sameFrames.trans originEq.1.symm
      refine ⟨author,released,rfl,rfl,same,?_⟩
      intro f disagree
      rw [same,disagree.2] at disagree
      exact Bool.false_ne_true disagree.1

#print axioms full_signed_report_erases_which_prior_authority_was_used

open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeWitnessOrigins350 (Attached)
open SourceExposure481 (authoredView)
open NativeProducer465 (checkPhaseOrigin finite_phase_origin_check_iff_literal_placed_active_row)

def sourceAttached : Attached (rawAt problem) previousSource.authors :=
  (attach (rawAt problem) previousSource.authors).get (by decide +kernel)
def releasedAttached : Attached (rawAt problem) prior.authors :=
  (attach (rawAt problem) prior.authors).get (by decide +kernel)

def sourceReplay := runReadCard (rawAt problem) previousSource.authors .actual (.variable 4)
  head.orig.code previousSourceCard
def releaseReplay := runReadCard (rawAt problem) (visibleReadView prior.authors) .actual (.variable 4)
  head.orig.code rootCard
def sourceUses : List Occurrence := sourceReplay.get (by decide +kernel)
def releaseUses : List Occurrence := releaseReplay.get (by decide +kernel)

theorem sourceTypeBeforeGeometry :
    Read (authoredView (rawAt problem) previousSource.authors) .actual
      (.variable 4) head.orig.code sourceUses := by
  exact runReadCard_sound (Option.some_get _).symm

theorem releasedTypeBeforeGeometry :
    Read (restriction (support releasedAttached)) .actual (.variable 4) head.orig.code releaseUses := by
  exact (read_with_genuine_completed_and_source_support_iff_finite_visible_read releasedAttached).mp
    ⟨rootCard,(Option.some_get _).symm⟩

def selectedFirst : StepWire := ⟨.field 30,[.payload]⟩
def selectedSecond : StepWire := ⟨.field 40,[.payload]⟩
def terminal : Site problem.old.state.core positions :=
  (readHop ambient selectedSecond 7).get (by decide +kernel)

noncomputable def independentFirstHop : Hop root ambient selectedFirst :=
  Classical.choice (reified_hop_keeps_the_same_old_place479 (i := 1)
    (by exact (Option.some_get _).symm :
      readHop root selectedFirst 1 = some ambient)).2
noncomputable def independentSecondHop : Hop ambient terminal selectedSecond :=
  Classical.choice (reified_hop_keeps_the_same_old_place479 (i := 7)
    (by exact (Option.some_get _).symm :
      readHop ambient selectedSecond 7 = some terminal)).2

theorem rootSafeCheck : readCheck problem.old.state.core positions pairs (.logical 4) outer = some false := by
  decide +kernel
theorem middleSafeCheck : readCheck problem.old.state.core positions pairs (.logical 6) before = some false := by
  decide +kernel
theorem terminalCycleCheck :
    readCheck problem.old.state.core positions pairs (.rowPos 2 [.field 40]) finish = some true := by
  decide +kernel

/-- Build the independent event before invoking either signed receipt
consumer. Its origin and finite typing evidence remain separate arguments. -/
noncomputable def originalInput
    {settled : Nat → Prop} (ready : Supported (rawAt problem) settled)
    (origin : Backing problem ready rootRaw) (uses : List Occurrence)
    (typing : Read (restriction ready) .actual (.variable 4) head.orig.code uses) :
    TypedInput problem gd positions pairs := by
  let checked := read_checkpoint_guards rootSafeCheck
  let mid := read_checkpoint_guards middleSafeCheck
  let endAt := read_checkpoint_guards terminalCycleCheck
  have atMid : ambient.index = before.which := by decide +kernel
  have atLast : terminal.index = finish.which := by decide +kernel
  exact {
    head := head
    single := by decide +kernel
    declarationOrdinal := 0
    registered := by decide +kernel
    root := root
    atHead := ⟨rfl,rfl⟩
    atPoint := rfl
    rawOrdinal := 0
    physicalRow := rfl
    rootRow := rootRaw
    existingRoot := rfl
    rootOwns := ⟨rfl,rfl⟩
    settled := settled
    support := ready
    backing := origin
    uses := uses
    typed := typing
    firstLabel := 30
    firstPose := [.payload]
    first := ambient
    enters := independentFirstHop
    rootGuard := checked.1
    rootSafe := fun cycle => Bool.false_ne_true (checked.2.2.mpr cycle)
    tail := [selectedSecond]
    tailPoints := [terminal.index]
    final := terminal
    bit := true
    visits := .step independentSecondHop (atMid.symm ▸ mid.1)
      (fun cycle => Bool.false_ne_true (mid.2.2.mpr (atMid ▸ cycle)))
      (.stop (atLast.symm ▸ endAt.1) (atLast.symm ▸ endAt.2.2))
    endsInField := ⟨40,rfl⟩ }

theorem originalSourceWasAuthored :
    (support sourceAttached).derivesFrom rootRaw .source := by
  simp [support,GeneralDeclarativeWitnessOrigins350.origin,previousSource]

theorem originalReleaseWasActive :
    NativeProducer465.PhaseOriginAt phase placed 4 0 :=
  (finite_phase_origin_check_iff_literal_placed_active_row phase placed 4 0).mp (by decide +kernel)

theorem exactSourceTypeBeforeGeometry :
    Read (restriction (support sourceAttached)) .actual (.variable 4) head.orig.code sourceUses := by
  exact SourceExposure481.genuine_authored_reads_transport_into_same_support481
    (fun row present => by
      simpa [support,GeneralDeclarativeWitnessOrigins350.origin] using present) sourceTypeBeforeGeometry

noncomputable def actualSourceEvent : TypedInput problem gd positions pairs :=
  originalInput (support sourceAttached) (.source originalSourceWasAuthored) sourceUses exactSourceTypeBeforeGeometry

noncomputable def actualReleaseEvent : TypedInput problem gd positions pairs :=
  originalInput (support releasedAttached)
    (.released 77 phase placed 0 (by simp [support,GeneralDeclarativeWitnessOrigins350.origin,prior,table])
      (by decide) originalReleaseWasActive) releaseUses releasedTypeBeforeGeometry

theorem actualSourceEvent_has_exact_prior : previousSource.ExactFor actualSourceEvent := by
  change Nonempty _ ∧ (∀ row, row ∈ previousSource.authors.authored ↔ _) ∧
    Read (authoredView (rawAt problem) previousSource.authors) .actual (.variable 4) head.orig.code sourceUses ∧ _
  refine ⟨⟨sourceAttached⟩,?_,sourceTypeBeforeGeometry,?_⟩
  · intro row; rfl
  · intro chosen chosenExact
    have actual : chosen = [⟨0,0⟩,⟨1,1⟩] := (Option.some.inj chosenExact).symm
    subst chosen
    refine ⟨[⟨0,0,rootRaw⟩,⟨1,1,authoredRaw⟩],?_,
      ⟨⟨0,0,rootRaw⟩,⟨by decide +kernel,[],[⟨1,1,authoredRaw⟩],rfl,by simp⟩,rfl⟩,
      sourceTypeBeforeGeometry⟩
    apply ordered_old_stamp_recovery_has_independent_exact_replay478.mpr
    exact .cons rfl rfl rfl (.cons rfl rfl rfl .nil)

theorem actualReleaseEvent_has_exact_prior : prior.ExactFor actualReleaseEvent := by
  change association ∈ prior.completed
  exact List.mem_cons_self ..

theorem same_fitting_problem_two_independent_exact_events_one_full_report :
    previousSource.ExactFor actualSourceEvent ∧ prior.ExactFor actualReleaseEvent ∧
    IsAuthoredInput actualSourceEvent ∧ ¬ IsAuthoredInput actualReleaseEvent ∧
    actualSourceEvent.report = actualReleaseEvent.report ∧
    actualSourceEvent.report.outcome =
      ([.payload,.payload],[.field 30,.field 40],.rowPos 2 [.field 40],true) ∧
    FitsFull problem.state sameFit := by
  refine ⟨actualSourceEvent_has_exact_prior,actualReleaseEvent_has_exact_prior,trivial,id,rfl,
    ?_,actual_rooted_interior_has_an_original_fit.1⟩
  have exactLoc : oldPosition positions terminal.index = .rowPos 2 [.field 40] := by decide +kernel
  change ([Pose.payload,Pose.payload],[QueryStep476.field 30,QueryStep476.field 40],oldPosition positions terminal.index,true) = _
  rw [exactLoc]

#print axioms same_fitting_problem_two_independent_exact_events_one_full_report
#print axioms actualSourceEvent_has_exact_prior
#print axioms actualReleaseEvent_has_exact_prior

theorem actual_authored_wire_pins_the_independent_event :
    ExactSelectedRoute actualSourceEvent previousSourceWire.route := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  have endIndex : terminal.index = 7 := by decide +kernel
  have begins : ambient.index = 1 := by decide +kernel
  change [1,7] = [ambient.index,terminal.index]
  rw [endIndex,begins]

theorem actual_released_wire_pins_the_independent_event :
    ExactSelectedRoute actualReleaseEvent phrase.route := by
  change ExactSelectedRoute actualSourceEvent previousSourceWire.route
  exact actual_authored_wire_pins_the_independent_event

theorem two_separate_finite_readers_return_their_own_independent_original_event :
    ∃ a : RootedInteriorReceipt problem gd positions pairs previousSource previousSourceWire,
      ∃ b : CompletedInterior problem gd positions pairs prior phase initial,
        readRootedInterior problem gd positions pairs previousSource previousSourceWire = some a ∧
        readAt phase initial = some b ∧
        a.report = actualSourceEvent.report ∧ b.output = actualReleaseEvent.report := by
  obtain ⟨a,b,ra,rb,_,_⟩ := full_signed_report_erases_which_prior_authority_was_used
  have native := completed_interior_keeps_original_release_and_scoped_report b
  exact ⟨a,b,ra,rb,
    every_accepted_wire_at_the_independent_event_coordinates_reports_the_same_event
      actualSourceEvent actual_authored_wire_pins_the_independent_event a.exactReport,
    native.1.trans (every_accepted_wire_at_the_independent_event_coordinates_reports_the_same_event
      actualReleaseEvent actual_released_wire_pins_the_independent_event b.focused.exactReport)⟩

theorem independent_exact_prior_class_is_not_decodable_from_unchanged_problem_and_signed_report
    (guess : FullProblem → SamePhaseInputObservation478 → Bool) :
    ¬ (guess problem actualSourceEvent.report = true ∧
       guess problem actualReleaseEvent.report = false) := by
  intro incompatible
  have same := same_fitting_problem_two_independent_exact_events_one_full_report.2.2.2.2.1
  rw [same,incompatible.2] at incompatible
  exact Bool.false_ne_true incompatible.1

#print axioms two_separate_finite_readers_return_their_own_independent_original_event
#print axioms independent_exact_prior_class_is_not_decodable_from_unchanged_problem_and_signed_report


open Producer479
open SourceExposure481 (authoredView genuine_authored_reads_transport_into_same_support481)
open SourceExposure481.ClosedBank
open GeneralDeclarativeWitnessOrigins350 (Attached attach support origin)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeInlineTrace331 (Read)
open InputCoordinates475 (rawAt SamePhaseInputObservation478)
open RetainedFull445 (FullProblem)

def mixedPrior : PriorPhase := { previousSource with completed := [association] }

/-- The legacy event-specific contract does not globally cross-check ledgers.
Exact qualification for this source arm ignores the completion list; exact
qualification for this release arm uses just its completed association. -/
theorem the_same_separate_ledger_can_qualify_two_different_arms :
    mixedPrior.ExactFor actualSourceEvent ∧ mixedPrior.ExactFor actualReleaseEvent ∧
    actualSourceEvent.report = actualReleaseEvent.report :=
  ⟨actualSourceEvent_has_exact_prior,actualReleaseEvent_has_exact_prior,
    same_fitting_problem_two_independent_exact_events_one_full_report.2.2.2.2.1⟩

theorem the_old_association_only_reader_accepts_the_same_report_with_no_ordinary_release :
    readBoundReleasedIssue problem gd positions pairs mixedPrior phase 77 phrase.route ⟨placed,0⟩ =
      some actualReleaseEvent.report ∧ 77 ∉ mixedPrior.authors.released := by
  refine ⟨?_,by decide +kernel⟩
  apply exact_output_association_and_current_release_replay479.mpr
  refine ⟨rootRaw,rfl,by decide +kernel,originalReleaseWasActive,?_⟩
  obtain ⟨_,completed,_,_,_,_⟩ := full_signed_report_erases_which_prior_authority_was_used
  have checked : readRoute problem gd positions pairs phrase.route = some completed.focused.report :=
    completed.focused.exactReport
  have selected := actual_released_wire_pins_the_independent_event
  exact (every_accepted_wire_at_the_independent_event_coordinates_reports_the_same_event
    actualReleaseEvent selected checked) ▸ checked

theorem the_checked_interior_never_treats_that_association_as_ordinary_release :
    readCompletedInterior problem gd positions pairs mixedPrior phase initial = none := by
  cases e : readCompletedInterior problem gd positions pairs mixedPrior phase initial with
  | none => rfl
  | some accepted =>
    have origin := (completed_interior_keeps_original_release_and_scoped_report accepted).2.2.1
    change 77 ∈ ([] : List Nat) at origin
    cases origin

#print axioms the_same_separate_ledger_can_qualify_two_different_arms
#print axioms the_old_association_only_reader_accepts_the_same_report_with_no_ordinary_release
#print axioms the_checked_interior_never_treats_that_association_as_ordinary_release

def overlapPrior : PriorPhase :=
  ⟨⟨[rootRaw,authoredRaw],table.produced,[77]⟩,[association],previousSource.recordedReads⟩

def overlapAttached : Attached (rawAt problem) overlapPrior.authors :=
  (attach (rawAt problem) overlapPrior.authors).get (by decide +kernel)

theorem overlapType :
    Read (restriction (support overlapAttached)) .actual (.variable 4) head.orig.code sourceUses :=
  genuine_authored_reads_transport_into_same_support481
    (fun row present => by simpa [support,origin,overlapPrior,previousSource] using present)
    sourceTypeBeforeGeometry

noncomputable def overlapSourceEvent :=
  originalInput (support overlapAttached)
    (.source (by simp [support,origin,overlapPrior])) sourceUses overlapType

noncomputable def overlapReleaseEvent :=
  originalInput (support overlapAttached)
    (.released 77 phase placed 0 (by simp [support,origin,overlapPrior,table])
      (by decide) originalReleaseWasActive) sourceUses overlapType

theorem exact_overlap_prior : overlapPrior.ExactFor overlapSourceEvent ∧
    overlapPrior.ExactFor overlapReleaseEvent ∧ IsAuthoredInput overlapSourceEvent ∧
    ¬ IsAuthoredInput overlapReleaseEvent ∧ overlapSourceEvent.report = overlapReleaseEvent.report := by
  refine ⟨?_, ?_, trivial,id,rfl⟩
  · change Nonempty _ ∧ (∀ row, row ∈ overlapPrior.authors.authored ↔ _) ∧
      Read (authoredView (rawAt problem) overlapPrior.authors) .actual (.variable 4) head.orig.code sourceUses ∧ _
    refine ⟨⟨overlapAttached⟩,fun _ => Iff.rfl,sourceTypeBeforeGeometry,?_⟩
    exact actualSourceEvent_has_exact_prior.2.2.2
  · exact actualReleaseEvent_has_exact_prior

def overlapCard : ReadCard :=
  .record [⟨⟨0,2⟩,[]⟩] [30] [(30,.record 40 (wrap (.variable 3)) empty)] empty
    (.cons (.record [⟨⟨1,1⟩,[]⟩] [40] [(40,wrap (.variable 3))] empty
      (.cons (.record [] [50] [(50,.variable 3)] empty
        (.cons .capture .nil) (.primitive .nil)) .nil) (.primitive .nil)) .nil) (.primitive .nil)

def overlapReleaseWire : CompletedInteriorWire 10 :=
  {initial with route := {phrase with approach := {phrase.approach with source := overlapCard, initialAuthor := 2}}}

theorem even_a_single_attached_ledger_and_two_exact_slot_checks_preserve_distinct_origins :
    ∃ a : RootedInteriorReceipt problem gd positions pairs overlapPrior previousSourceWire,
      ∃ b : CompletedInterior problem gd positions pairs overlapPrior phase overlapReleaseWire,
        readRootedInterior problem gd positions pairs overlapPrior previousSourceWire = some a ∧
        readCompletedInterior problem gd positions pairs overlapPrior phase overlapReleaseWire = some b ∧
        a.report = overlapSourceEvent.report ∧ b.output = overlapReleaseEvent.report ∧
        a.approach.initial.initialIndices.author = 0 ∧
        b.focused.approach.initial.initialIndices.author = 2 := by
  have first : (readRootedInterior problem gd positions pairs overlapPrior previousSourceWire).isSome = true := by
    decide +kernel
  have second : (readCompletedInterior problem gd positions pairs overlapPrior phase overlapReleaseWire).isSome = true := by
    decide +kernel
  let a := (readRootedInterior problem gd positions pairs overlapPrior previousSourceWire).get first
  let b := (readCompletedInterior problem gd positions pairs overlapPrior phase overlapReleaseWire).get second
  have selectedA : ExactSelectedRoute overlapSourceEvent previousSourceWire.route :=
    actual_authored_wire_pins_the_independent_event
  have selectedB : ExactSelectedRoute overlapReleaseEvent overlapReleaseWire.route.route :=
    actual_released_wire_pins_the_independent_event
  refine ⟨a,b,(Option.some_get first).symm,(Option.some_get second).symm,
    every_accepted_wire_at_the_independent_event_coordinates_reports_the_same_event overlapSourceEvent selectedA a.exactReport,
    (completed_interior_keeps_original_release_and_scoped_report b).1.trans
      (every_accepted_wire_at_the_independent_event_coordinates_reports_the_same_event overlapReleaseEvent selectedB b.focused.exactReport),
    ?_,?_⟩
  · obtain ⟨_,_,_,_,_,_,_,_,_,author,_,_,_⟩ := actual_root_pinned_read_iff.mp a.approach.bound
    exact author
  · obtain ⟨_,_,_,_,_,_,_,_,_,author,_,_,_⟩ := actual_root_pinned_read_iff.mp b.focused.approach.bound
    exact author

#print axioms exact_overlap_prior
#print axioms even_a_single_attached_ledger_and_two_exact_slot_checks_preserve_distinct_origins
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.CompletedInteriorActual484
