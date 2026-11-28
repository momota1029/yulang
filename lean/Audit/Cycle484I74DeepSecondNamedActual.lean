import Yulang.GeneralDeclarativeI65I74RootedInteriorReport483
import Yulang.GeneralDeclarativeI65I74NamedArrivalBoundary484
import Yulang.GeneralDeclarativeI65I74LiteralRecordAlignment484
import Yulang.GeneralDeclarativeI65I74MarkedRootOrigin475
import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.DeepSecondNamedActual484
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
    [],[]⟩
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
  .record 30 (.record 40 (.record 50 (.record 61 (.var 3) (.app 9 [])) (.app 9 [])) (.app 9 [])) (.app 9 [])
def declaration : Declaration := ⟨218,19,[queryPattern],[],[],[]⟩
def rootRaw : Equation := ⟨4,.record 30 (.variable 6) empty⟩
def wrap (e : Expr) : Expr := .record 61 e empty
def middle (e : Expr) : Expr := .record 50 e empty
def namedFirst : Equation := ⟨6,.record 40 (.variable 7) empty⟩
def namedSource : Equation := ⟨7,middle (wrap (.variable 8))⟩
def namedPending : Equation := ⟨7,middle (wrap (wrap (.variable 8)))⟩
def recurrence : Equation := ⟨8,wrap (.variable 8)⟩
def rawOriginal : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[rootRaw,namedFirst,namedSource,namedPending,recurrence]⟩
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
def table : Table := ⟨[rootRaw,namedFirst,namedSource],[(namedPending,99),(recurrence,99)],[]⟩

def clazz (n : Nat) : ClassWire :=
  ⟨[(n,.same)],⟨(List.range 9).map (fun i => if i = n then 1 else 0),[1]⟩⟩

def positions : Positions 12 :=
  ⟨#v[⟨.logical 4,0⟩,⟨.logical 6,1⟩,⟨.logical 7,3⟩,⟨.logical 8,4⟩,
      ⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩,⟨.rowPos 2 [],2⟩,⟨.rowPos 3 [],3⟩,
      ⟨.rowPos 2 [.field 50],2⟩,⟨.rowPos 3 [.field 50],3⟩,
      ⟨.rowPos 3 [.field 50,.field 61],3⟩,⟨.rowPos 4 [],4⟩],
    [.record [30],.record [40],.record [50],.record [61]],
    #v[clazz 4,clazz 6,clazz 7,clazz 8,clazz 4,clazz 6,clazz 7,clazz 7,clazz 7,clazz 7,clazz 7,clazz 8]⟩
def pairs : List (Fin 12 × Fin 12) :=
  ([[0,4],[1,5],[2,6,7],[3,8,9,10,11]] : List (List (Fin 12))).flatMap
    fun block => block.flatMap fun i => block.map fun j => (i,j)

def firstCheckpoint : Checkpoint 12 :=
  ⟨0,6,4,⟨#v[0,1,2,9,10,3],#v[.structural 0 [1],.structural 1 [2],.structural 2 [3],.structural 3 [4],.structural 3 [5],.structural 3 [5]],0⟩,
    ⟨#v[0,1,2,3,3,3],#v[.structural 0 [1],.structural 1 [2],.structural 2 [3],.structural 3 [3]]⟩⟩
def firstNamed : Checkpoint 12 :=
  ⟨1,5,3,⟨#v[1,2,9,10,3],#v[.structural 1 [1],.structural 2 [2],.structural 3 [3],.structural 3 [4],.structural 3 [4]],0⟩,
    ⟨#v[0,1,2,2,2],#v[.structural 1 [1],.structural 2 [2],.structural 3 [2]]⟩⟩
def secondNamed : Checkpoint 12 :=
  ⟨2,4,2,⟨#v[2,9,10,3],#v[.structural 2 [1],.structural 3 [2],.structural 3 [3],.structural 3 [3]],0⟩,
    ⟨#v[0,1,1,1],#v[.structural 2 [1],.structural 3 [1]]⟩⟩
def finish : Checkpoint 12 :=
  ⟨9,3,1,⟨#v[9,10,3],#v[.structural 3 [1],.structural 3 [2],.structural 3 [2]],0⟩,
    ⟨#v[0,0,0],#v[.structural 3 [0]]⟩⟩

def head : PrecheckedHead (p := problem.old) gd :=
  (readPrecheckedHead (p := problem.old) gd ⟨0,0⟩).get (by decide +kernel)
def root : Site problem.old.state.core positions :=
  ⟨0,head.orig.original,head.orig.code,rootRaw.right,rfl⟩
def select30 : StepWire := ⟨.field 30,[.payload]⟩
def select40 : StepWire := ⟨.field 40,[.payload]⟩
def select50 : StepWire := ⟨.field 50,[.payload]⟩

def firstSite : Site problem.old.state.core positions :=
  (readHop root select30 1).get (by decide +kernel)
def secondSite : Site problem.old.state.core positions :=
  (readHop firstSite select40 2).get (by decide +kernel)
def lexical : Site problem.old.state.core positions :=
  (siteAt 6 secondSite.pattern secondSite.query).get (by decide +kernel)
def terminal : Site problem.old.state.core positions :=
  (readHop secondSite select50 9).get (by decide +kernel)
def authorEnd : Site problem.old.state.core positions :=
  (readHop lexical select50 8).get (by decide +kernel)

def card7 : ReadCard :=
  .record [⟨⟨2,2⟩,[]⟩] [50] [(50,wrap (.variable 3))] empty
    (.cons (.record [] [61] [(61,.variable 3)] empty
      (.cons .capture .nil) (.primitive .nil)) .nil) (.primitive .nil)
def card6 : ReadCard :=
  .record [⟨⟨1,1⟩,[]⟩] [40] [(40,middle (wrap (.variable 3)))] empty
    (.cons card7 .nil) (.primitive .nil)
def cardRoot : ReadCard :=
  .record [⟨⟨0,0⟩,[]⟩] [30] [(30,.record 40 (middle (wrap (.variable 3))) empty)] empty
    (.cons card6 .nil) (.primitive .nil)
def before40 :=
  readLiteralVisitStep problem.old.state.core firstSite.pattern firstSite.query firstSite.term select40
def oldWire : RouteWire 12 :=
  ⟨0,0,⟨firstCheckpoint,[(select30,firstNamed),(select40,secondNamed),(select50,finish)]⟩⟩
def namedCompare := readAuthoredTerminalCompare problem table positions pairs secondNamed 7 secondSite.query card7
def control : List Bool :=
  [(readRoute problem gd positions pairs oldWire).map (·.outcome) ==
      some ([.payload,.payload,.payload],[.field 30,.field 40,.field 50],.rowPos 3 [.field 50],true),
    (runReadCard (rawAt problem) table .actual (.variable 7) secondSite.query card7).isSome,
    (readFocusedCardHop (p := problem) table firstSite select40 card6 2).isNone,
    (namedCompare.map (fun c => (c.author.ordinals.raw,c.lexical.val,c.sign))) == some (2,6,false),
    (readHop lexical select50 8).isSome,(readHop secondSite select50 9).isSome]

/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval control

theorem the_later_named_pending_arrival_never_passes_old_same_site_focus (anyCard : ReadCard) :
    readFocusedCardHop (p := problem) table firstSite select40 anyCard 2 = none := by
  let step := before40.get (by decide +kernel)
  apply pending_named_geometry_does_not_construct_a_focused_old_child
    (step := step) (v := 7) (pending := namedPending) (next := secondSite)
  · exact (Option.some_get _).symm
  · exact (GeneralDeclarativeWitnessLiteral349.eq_expr ..).mp (by decide +kernel)
  · exact (Option.some_get _).symm
  · decide +kernel
  · decide +kernel

def recursiveTy : Ty := .record 61 (.block [.record 61 (.inl 0) .emptyRecord] 0) .emptyRecord
theorem recursiveTy_unfolds : Equivalent recursiveTy (record 61 recursiveTy .emptyRecord) := by
  have p (k : Nat) : CommonNominalFullCarrier.observeTy k recursiveTy =
      CommonNominalFullCarrier.observeTy k (record 61 recursiveTy .emptyRecord) := by cases k <;> rfl
  constructor
  · intro k; rw [←p k]; exact CommonNominalFullDemand.producerLe_refl _
  · intro k; rw [p k]; exact CommonNominalFullDemand.producerLe_refl _

def ty7 : Ty := record 50 recursiveTy .emptyRecord
def ty6 : Ty := record 40 ty7 .emptyRecord

def model : I72.Model :=
  ⟨fun n => (if n = 4 then record 30 ty6 .emptyRecord else if n = 6 then ty6 else if n = 7 then ty7
    else if n = 8 then recursiveTy else .emptyRecord, Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem there_is_an_original_fit_with_an_unreleased_second_named_representation :
    FitsFull problem.state model ∧ problem.old.root.demand.outputs = [] ∧
      namedPending ∉ table.authored ∧ (namedPending,99) ∈ table.produced ∧ 99 ∉ table.released := by
  refine ⟨?_,rfl,by decide +kernel,by decide +kernel,by decide⟩
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [rootRaw,namedFirst,namedSource,namedPending,recurrence] at h
    have found : row = rootRaw ∨ row = namedFirst ∨ row = namedSource ∨ row = namedPending ∨ row = recurrence := by
      simpa using h
    rcases found with rfl | rfl | rfl | rfl | rfl
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr _ recursiveTy_unfolds
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
    · exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr _
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans recursiveTy_unfolds
          (GeneralNominalCenteredHeadMatPatternSemantics.record_congr _ recursiveTy_unfolds
            (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)))
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
    · exact recursiveTy_unfolds
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h


open CommonRoleGraphBisimulation (ObservationallyEqual)
open CommonRoleRegularGraph (successors)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeWitnessOrigins350 (Attached)
open SourceExposure481 (authoredView)

theorem exact_safe_second_cut_reanchors_without_changing_terminal_sign :
    ∃ c, namedCompare = some c ∧
      c.author.ordinals.raw = 2 ∧ c.lexical = lexical.index ∧ c.sign = false ∧
      oldPosition positions authorEnd.index = .rowPos 2 [.field 50] ∧
      oldPosition positions terminal.index = .rowPos 3 [.field 50] ∧
      ReturnsUpToEquality (graphOf problem.old.state.core positions) authorEnd.index ∧
      ReturnsUpToEquality (graphOf problem.old.state.core positions) terminal.index := by
  let c := namedCompare.get (by decide +kernel)
  have built : namedCompare = some c := (Option.some_get _).symm
  have rooted : c.author.ordinals.raw = 2 := by decide +kernel
  have atLex : c.lexical = lexical.index := by decide +kernel
  have safe : c.sign = false := by decide +kernel
  have atSecond : secondNamed.which = secondSite.index := by decide +kernel
  have atEnd : finish.which = terminal.index := by decide +kernel
  have terminalRead : readCheck problem.old.state.core positions pairs (.rowPos 3 [.field 50]) finish =
      some true := by decide +kernel
  have isCycle := (read_checkpoint_guards terminalRead).2.2.mp rfl
  have stage := read_checkpoint_guards c.checkedSign
  let graph := graphOf problem.old.state.core positions
  have same : ObservationallyEqual graph secondSite.index lexical.index := by
    rw [←atSecond,←atLex]
    exact c.agrees
  have knownB : graph secondSite.index ≠ .unresolved := by
    rw [←atSecond]
    exact stage.1.2.2.2.2.2 _ (.nil _)
  have knownA : graph lexical.index ≠ .unresolved :=
    ObservationAlternatives473.proved_same_observation_cannot_replace_a_resolved_alternative_with_unknown
      _ _ _ same knownB
  obtain ⟨_,⟨sourceHop⟩⟩ := reified_hop_keeps_the_same_old_place479
    (by exact (Option.some_get _).symm : readHop lexical select50 8 = some authorEnd)
  obtain ⟨_,⟨oldHop⟩⟩ := reified_hop_keeps_the_same_old_place479
    (by exact (Option.some_get _).symm : readHop secondSite select50 9 = some terminal)
  have sameEnd := InteriorCorrespondence483.paired_selected_children_have_equal_regular_observations
    stage.1.2.1 knownA knownB (fun d => (same d).symm) sourceHop oldHop rfl
  have cycleEnd : ReturnsUpToEquality graph terminal.index := atEnd ▸ isCycle
  exact ⟨c,built,rooted,atLex,safe,by decide +kernel,by decide +kernel,
    (QuotientObservation471.quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation sameEnd).mpr
      cycleEnd,cycleEnd⟩

def literalCard7 : ReadCard :=
  .record [] [50] [(50,wrap (.variable 3))] empty
    (.cons (.record [] [61] [(61,.variable 3)] empty
      (.cons .capture .nil) (.primitive .nil)) .nil) (.primitive .nil)

theorem after_the_second_reanchor_the_original_selected_literal_operand_has_its_own_typed_card :
    ∃ step : ReadStep problem.old.state.core select50 lexical.pattern lexical.query lexical.term,
      ∃ uses card, readLiteralVisitStep problem.old.state.core lexical.pattern lexical.query lexical.term select50 =
        some step ∧ runReadCard (rawAt problem) table .actual step.actualRawChild step.childQuery card = some uses ∧
        Read (authoredView (rawAt problem) table) .actual step.actualRawChild step.childQuery uses := by
  let literal := readLiteralVisitStep problem.old.state.core lexical.pattern lexical.query lexical.term select50
  let step := literal.get (by decide +kernel)
  have wire : literal = some step := (Option.some_get _).symm
  let lookup := attach (rawAt problem) table
  let attached := lookup.get (by decide +kernel)
  let priorRead := runReadCard (rawAt problem) table .actual lexical.term lexical.query literalCard7
  let uses := priorRead.get (by decide +kernel)
  have verified : priorRead = some uses := (Option.some_get _).symm
  obtain ⟨childUses,childCard,computed,independent⟩ :=
    original_field_proof_and_actual_old_step_supply_one_independent_typed_child attached
      (runReadCard_sound verified) step rfl
  exact ⟨step,childUses,childCard,wire,computed,independent⟩

#print axioms exact_safe_second_cut_reanchors_without_changing_terminal_sign
#print axioms after_the_second_reanchor_the_original_selected_literal_operand_has_its_own_typed_card

#print axioms the_later_named_pending_arrival_never_passes_old_same_site_focus
#print axioms there_is_an_original_fit_with_an_unreleased_second_named_representation

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.DeepSecondNamedActual484
