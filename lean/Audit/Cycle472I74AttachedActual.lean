import Yulang.CommonRoleGraphBisimulation
import Yulang.GeneralDeclarativeI65I74AttachedInputField472
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
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471.AttachedActual472
open Yulang.GeneralDeclarativeI65
open WrittenPattern460 (CoreState)
open RetainedFull445
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
def lastOpened : TyTerm Nat := .record 30 (.record 40 (.var 5) .emptyRecord) .emptyRecord
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
def physicallyInline : Equation := ⟨4,.record 30 (.record 40 (.variable 5) empty) empty⟩
def terminalRow : Equation := oneRow 5 40 5
def inlineRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[physicallyInline,terminalRow]⟩
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
def actualCap : Nat → GeneralDeclarativeWhere319.Capture := fun _ => point 5

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
    change row ∈ [physicallyInline,terminalRow] at present
    rcases List.mem_cons.mp present with rfl | present
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · obtain rfl := List.mem_singleton.mp present
      exact unfold_mu455 40
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
open GeneralDeclarativeWitnessOrigins350 (Table attach)

def sourceRoster : Table := ⟨[terminalRow,physicallyInline],[],[]⟩
def outputPending : Table := ⟨[terminalRow],[(physicallyInline,12)],[]⟩
def outputReleased : Table := ⟨[terminalRow],[(physicallyInline,12)],[12]⟩

def actualWire472 : AttachedFieldWire472 := ⟨⟨0,0⟩,0,30,[.payload],0,1⟩

def pointTable : GraphTicket 3 := ⟨
  #v[⟨.named 4,0⟩,⟨.inline 0 [.field 30],0⟩,⟨.named 5,1⟩],[.record [30],.record [40]]⟩

def observedScope : ConeWire 3 2 := ⟨#v[1,2],#v[.structural 1 [1],.structural 1 [1]],0⟩
def minimalField : QuotientObservation471.Wire 2 1 := ⟨#v[0,0],#v[.structural 1 [0]]⟩

def actualReport472 (t : Table) (w : AttachedFieldWire472) : Option CheckedFieldBit :=
  readAttachedAuthorField472 inlined t preparedInlineTable w pointTable 1 observedScope minimalField

theorem actual_inline_field_has_the_same_positional_K2_with_an_attached_old_source_manifest472 :
    actualReport472 sourceRoster actualWire472 = some ⟨[71,2],218,0,[.payload],30,true⟩ ∧
      FitsFull inlined.state model ∧ Nonempty (SourceHead inlined.old.state.core inlined.old.root onlyDecl) :=
  ⟨by decide +kernel,actual_inline_source_model_fits_without_named_parent_row464,
    actual_written_closed_record_is_an_ordinary_source_head463⟩

theorem same_exact_raw_and_source_only_distinction_is_not_a_release_check472 :
    (attach inlined.state.base.core.current.ordinary outputPending).isSome = true ∧
    (attach inlined.state.base.core.current.ordinary outputReleased).isSome = true ∧
    (actualReport472 outputPending actualWire472).isNone = true ∧
    (actualReport472 outputReleased actualWire472).isNone = true :=
  ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- info: [some true, none, none, none, none, none] -/
#guard_msgs in
#eval [(actualReport472 sourceRoster actualWire472).map CheckedFieldBit.checked,
  (actualReport472 sourceRoster {actualWire472 with authorOrdinal := 0}).map CheckedFieldBit.checked,
  (actualReport472 sourceRoster {actualWire472 with rawOrdinal := 1}).map CheckedFieldBit.checked,
  (actualReport472 outputPending actualWire472).map CheckedFieldBit.checked,
  (actualReport472 outputReleased actualWire472).map CheckedFieldBit.checked,
  (actualReport472 sourceRoster {actualWire472 with path := [.tail]}).map CheckedFieldBit.checked]

#print axioms actual_inline_field_has_the_same_positional_K2_with_an_attached_old_source_manifest472
#print axioms same_exact_raw_and_source_only_distinction_is_not_a_release_check472
end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471.AttachedActual472
