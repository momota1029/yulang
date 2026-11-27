import Yulang.GeneralDeclarativeI65I74PaletteIndependentObservation474
import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464
import Yulang.GeneralDeclarativeI65Heads367
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeI65I74RecordTraversal455
import Yulang.GeneralDeclarativeI65I74RecordEntry412
import Yulang.GeneralDeclarativeWitnessLiteral349
import Yulang.GeneralDeclarativeI65I74FullState444
import Yulang.GeneralDeclarativeEntailment320

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473.ComparedActual474
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
def oneRow (i field child : Nat) : Equation := ⟨i,.record field (.variable child) empty⟩
def terminalTerm : TyTerm Nat := .record 40 (.var 5) .emptyRecord
def lastOpened : TyTerm Nat := .record 30 (.record 40 (.var 6) .emptyRecord) .emptyRecord
def escape (here : Nat) (atSame reached : List Nat) : ExactEscapeWire :=
  ⟨List.range 12,(List.range 12).map fun i =>
    if i = here || atSame.contains i then 0 else if reached.contains i then 1 else 2⟩
def recState (field : Nat) : CommonNominalSyntax.State Common.Row :=
  .block [.record field (.inl 0) .emptyRecord] 0
def mu (field : Nat) : Ty := .record field (recState field) .emptyRecord
theorem unfold_mu455 (f : Nat) :
    Equivalent (mu f) (record f (mu f) .emptyRecord) := by
  have each (k : Nat) : CommonNominalFullCarrier.observeTy k (mu f) =
      CommonNominalFullCarrier.observeTy k (record f (mu f) .emptyRecord) := by
    cases k <;> rfl
  constructor
  · intro k
    rw [←each k]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro k
    rw [each k]
    exact CommonNominalFullDemand.producerLe_refl _

def written : Pattern :=
  .record 30 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])
def writtenCode : Expr := .record 30 (.record 40 (.variable 3) empty) empty
def physicallyInline : Equation := ⟨4,.record 30 (.record 40 (.variable 6) empty) empty⟩
def terminalRow : Equation := oneRow 5 40 5
def secondDefinition : Equation := ⟨6,.record 40 (.record 40 (.variable 6) empty) empty⟩
def rawLink : Equation := ⟨6,.variable 5⟩
def inlineRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[physicallyInline,terminalRow,secondDefinition,rawLink]⟩
def onlyDecl : Declaration := ⟨218,19,[written],[],[],[]⟩

def sourceOnlyInline : Option FullProblem := do
  let graph ← compile bodies
  let auth ← GeneralSourceMetadataBareBundle291.compile
    (let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
      ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
     ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[onlyDecl]⟩)
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,inlineRaw,[]⟩,List.replicate 20 [] ++ [[cov]],
    [⟨4,[402],.ordinary lastOpened⟩,⟨5,[402],.ordinary terminalTerm⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 4],[]⟩⟩⟩)

def inlined : FullProblem := sourceOnlyInline.get (by decide +kernel)
def actualCap : Nat → GeneralDeclarativeWhere319.Capture := fun _ => point 6

theorem actual_written_closed_record_is_an_ordinary_source_head463 :
    Nonempty (SourceHead inlined.old.state.core inlined.old.root onlyDecl) := by
  refine ⟨.ordered actualCap (.cons (.ordinary ?_) .nil)⟩
  refine ⟨⟨Bound.refl _,Bound.refl _⟩,writtenCode,?_,.direct (.whole ?_)⟩
  · rfl
  · exact List.mem_cons_self

def model : I72.Model :=
  ⟨fun n => (if n = 4 then record 30 (record 40 (mu 40) .emptyRecord) .emptyRecord else mu 40,Common.rowEmpty),
    fun _ => none,fun n => if n = 4 then some (.ordinary lastOpened)
      else if n = 5 then some (.ordinary terminalTerm) else none⟩

theorem actual_inline_source_model_fits_without_named_parent_row464 :
    FitsFull inlined.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro row present
    change row ∈ [physicallyInline,terminalRow,secondDefinition,rawLink] at present
    rcases List.mem_cons.mp present with rfl | rest
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    rcases List.mem_cons.mp rest with rfl | rest
    · exact unfold_mu455 40
    rcases List.mem_cons.mp rest with rfl | rest
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans (unfold_mu455 40)
        (GeneralNominalCenteredHeadMatPatternSemantics.record_congr 40 (unfold_mu455 40)
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _))
    · obtain rfl := List.mem_singleton.mp rest
      exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ bad; cases bad
  · intro src present
    change src ∈ [⟨4,[402],.ordinary lastOpened⟩,⟨5,[402],.ordinary terminalTerm⟩] at present
    rcases List.mem_cons.mp present with rfl | present
    · rfl
    · obtain rfl := List.mem_singleton.mp present
      rfl
  · intro _ bad; cases bad

theorem actual_checked_declaration_is_ready_even_in_inline_only_state463 :
    DeclarationReady (authoredRegistry inlined.old.state.core.current) onlyDecl := by
  have exact : RecordTrail455.localAuthorBits inlined.old.state.core.current.environment onlyDecl = true := by
    decide +kernel
  obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp exact
  refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
  intro c appears
  cases appears

def inlinePreparedProtocol : CertificateProtocol inlined.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = onlyDecl)
  sound := fun _ _ chosen => (of_decide_eq_true chosen).symm ▸
    actual_checked_declaration_is_ready_even_in_inline_only_state463

def preparedInlineTable := (prepareTable inlinePreparedProtocol [(onlyDecl,())]).get (by decide +kernel)

theorem exact_inline_candidate_is_really_prechecked463 :
    (readPrecheckedHead (p := inlined.old) preparedInlineTable ⟨0,0⟩).isSome = true := by
  decide +kernel

open Yulang.GeneralDeclarativeI65.I72.LiteralFold471

def wire : HeadWire := ⟨⟨0,0⟩,[.payload],⟨0,1,⟨⟨1,.same,5⟩,[],.same⟩⟩,40,3⟩

def exactReport : Report := ⟨[71,2],218,19,⟨0,0⟩,[.payload],4,30,5⟩

open QuotientObservation471
open GeneralDeclarativeWitnessOrigins350 (Table)
open ObservationRawAlias471 (ClassWire)
open List410 (ExactEscapeWire)

def cut4 : ExactEscapeWire := ⟨(List.range 9).map (fun k => if k = 4 then 1 else 0),[1,0]⟩
def group4 : ClassWire := ⟨[(4,.same)],cut4⟩
def group5 : ClassWire := ⟨[(5,.same),(6,.backward 3)],cut4⟩
def group6 : ClassWire := ⟨[(6,.same),(5,.forward 3)],cut4⟩

open ObservationAliasHead472 (readExactOwner)
open ObservationAlternatives473
def positions (select : Nat) : Positions 7 := ⟨#v[
  ⟨.logical 4,0⟩,⟨.rowPos 0 [.field 30],0⟩,⟨.logical 6,select⟩,⟨.logical 5,1⟩,
  ⟨.rowPos 1 [],1⟩,⟨.rowPos 2 [],2⟩,⟨.rowPos 2 [.field 40],2⟩],
  [.record [30],.record [40]],#v[group4,group4,group6,group5,group5,group6,group6]⟩
def pairs : List (Fin 7 × Fin 7) :=
  (List.finRange 7).flatMap (fun i => (List.finRange 7).filterMap (fun j =>
      if i != 0 && j != 0 then some (i,j) else none))
def alongFive : ConeWire 7 3 := ⟨#v[1,2,3],
  #v[.structural 1 [1],.structural 1 [2],.structural 1 [2]],0⟩
def alongSix : ConeWire 7 3 := ⟨#v[1,2,6],
  #v[.structural 1 [1],.structural 1 [2],.structural 1 [1]],0⟩
def quotient : QuotientObservation471.Wire 3 1 := ⟨#v[0,0,0],#v[.structural 1 [0]]⟩
def source : Table := ⟨[terminalRow,physicallyInline],[],[]⟩
def exactOrigin : AttachedFieldWire472 := ⟨⟨0,0⟩,0,30,[.payload],0,1⟩

def precise (p : Positions 7) (walk : ConeWire 7 3) (r : List (Fin 7 × Fin 7)) : Option CheckedFieldBit :=
  readAlternativeInputField inlined source preparedInlineTable exactOrigin p r 1 walk quotient


def widerSix : ConeWire 7 4 := ⟨#v[1,2,6,5],
  #v[.structural 1 [1],.structural 1 [2],.structural 1 [1],.structural 1 [2]],0⟩
def widerSixAtNamed : ConeWire 7 4 := { widerSix with site := 1 }
def quotientWide : QuotientObservation471.Wire 4 1 := ⟨#v[0,0,0,0],#v[.structural 1 [0]]⟩

def finiteAcross : CommonRoleGraphBisimulation.Relation 7 :=
  ([0,1,2] : List (Fin 7)).flatMap (fun i => ([3,4,5,6] : List (Fin 7)).map (i,·))

theorem same_actual_input_and_distinct_completely_checked_unrollings_have_equal_type_and_bit :
    (∀ m : GeneralDeclarativeI65.Model, FitsFull inlined.state m →
      Equivalent (interpretedAt inlined.old.state.core (positions 1) m.assignment 1)
        (interpretedAt inlined.old.state.core (positions 2) m.assignment 2)) ∧
    FitsFull inlined.state model := by
  have a : readAlternatives inlined.old.state.core (positions 1) pairs 1 alongFive quotient = some true := by
    decide +kernel
  have b : readAlternatives inlined.old.state.core (positions 2) pairs 2 widerSixAtNamed quotientWide = some true := by
    decide +kernel
  have comparison : checkAcrossWitness (cone alongFive) (cone widerSixAtNamed) alongFive.site widerSixAtNamed.site finiteAcross = true := by
    decide +kernel
  have same := two_checked_observations_in_one_input_agree_in_bit_and_regular_type (p := inlined) (a := positions 1) (b := positions 2) rfl a b comparison
  exact ⟨same.2,actual_inline_source_model_fits_without_named_parent_row464⟩

def preciseWide : Option CheckedFieldBit :=
  readAlternativeInputField inlined source preparedInlineTable exactOrigin (positions 2) pairs 1 widerSix quotientWide

/-- info: [true, false, true, true] -/
#guard_msgs in
#eval [
  checkAcrossWitness (cone alongFive) (cone widerSix) alongFive.site widerSix.site finiteAcross,
  checkAcrossWitness (cone alongFive) (cone widerSix) alongFive.site widerSix.site [(0,3)],
  (precise (positions 1) alongFive pairs).map CheckedFieldBit.checked == some true,
  preciseWide.map CheckedFieldBit.checked == some true]

#print axioms same_actual_input_and_distinct_completely_checked_unrollings_have_equal_type_and_bit


def reversedPositions : Positions 7 := { positions 2 with signs := [.record [40],.record [30]] }
def reversedAtNamed : ConeWire 7 4 := ⟨#v[1,2,6,5],
  #v[.structural 0 [1],.structural 0 [2],.structural 0 [1],.structural 0 [2]],1⟩
def reversedPartition : QuotientObservation471.Wire 4 1 := ⟨#v[0,0,0,0],#v[.structural 0 [0]]⟩

def sharedShapes := commonPalette (positions 1).signs reversedPositions.signs
def firstColored := recolorGraph (cone alongFive) (mappedIndex (positions 1).signs sharedShapes)
def lastColored := recolorGraph (cone reversedAtNamed) (mappedIndex reversedPositions.signs sharedShapes)

theorem two_reversed_actual_signature_palettes_still_give_equal_carrier_types_and_bit :
    (∀ m : GeneralDeclarativeI65.Model, FitsFull inlined.state m →
      Equivalent (interpretedAt inlined.old.state.core (positions 1) m.assignment 1)
        (interpretedAt inlined.old.state.core reversedPositions m.assignment 2)) ∧
    FitsFull inlined.state model := by
  have left : readAlternatives inlined.old.state.core (positions 1) pairs 1 alongFive quotient = some true := by
    decide +kernel
  have right : readAlternatives inlined.old.state.core reversedPositions pairs 2 reversedAtNamed reversedPartition =
      some true := by
    decide +kernel
  have compared : checkAcrossWitness firstColored lastColored alongFive.site reversedAtNamed.site finiteAcross = true := by
    decide +kernel
  have sound := exact_checked_presentations_can_use_separately_ordered_constructor_palettes
    (p := inlined) left right compared
  exact ⟨sound.2,actual_inline_source_model_fits_without_named_parent_row464⟩

def preciseReversed : Option CheckedFieldBit :=
  readAlternativeInputField inlined source preparedInlineTable exactOrigin reversedPositions pairs 1
    { reversedAtNamed with site := 0 } reversedPartition

/-- info: [true, false, true, true] -/
#guard_msgs in
#eval [((positions 1).signs != reversedPositions.signs),
  checkAcrossWitness (cone alongFive) (cone reversedAtNamed) alongFive.site reversedAtNamed.site finiteAcross,
  checkAcrossWitness firstColored lastColored alongFive.site reversedAtNamed.site finiteAcross,
  preciseReversed.map CheckedFieldBit.checked == some true]

#print axioms two_reversed_actual_signature_palettes_still_give_equal_carrier_types_and_bit

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473.ComparedActual474
