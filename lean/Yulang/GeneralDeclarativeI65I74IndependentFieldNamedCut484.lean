import Yulang.GeneralDeclarativeI65I74LiteralRecordAlignment484
import Yulang.GeneralDeclarativeI65I74DirectAuthoredNamedAnchor484

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open ObservationAlternatives473 (Positions oldPosition)
open LiteralVisits473 (StepWire ReadStep Checkpoint readCheck)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open InputCoordinates475 (rawAt)
open SourceExposure481 (authoredView notBinder_exact)
open WrittenPattern460.PhysicalOrigin (atSource literal_occurrence)

theorem independently_typed_literal_field_yields_its_authored_named_cut_without_relabeling_geometry
    {n : Nat} {p : FullProblem} {t : Table} {pos : Positions n} {rel}
    {source : GeneralDeclarationPatterns.Pattern} {wire : StepWire} {raw code : Expr} {uses}
    {label name : Nat} {geom : Checkpoint n} {bit : Bool}
    (attached : Attached (rawAt p) t)
    (independent : Read (authoredView (rawAt p) t) .actual raw code uses)
    (literal : ReadStep p.old.state.core wire source code raw)
    (field : wire.action = .field label)
    (named : literal.actualRawChild = .variable name)
    (fixedGeometry : readCheck p.old.state.core pos rel (.logical name) geom = some bit) :
    ∃ childUses card exposure residual anchor,
      atSource source wire.written = some literal.writtenChild ∧
      runReadCard (rawAt p) t .actual (.variable name) literal.childQuery card = some childUses ∧
      Read (authoredView (rawAt p) t) .actual (.variable name) literal.childQuery childUses ∧
      readDirectNamedAnchor p t pos rel geom name literal.childQuery exposure residual = some anchor ∧
      oldPosition pos anchor.comparison.lexical = .rowPos exposure.ordinals.raw [] ∧
      anchor.comparison.marks = childUses ∧ anchor.comparison.sign = bit ∧
      (rawAt p).equations[exposure.ordinals.raw]? = some anchor.comparison.row ∧
      t.authored[exposure.ordinals.author]? = some anchor.comparison.row := by
  obtain ⟨childUses,card,run,read⟩ :=
    original_field_proof_and_actual_old_step_supply_one_independent_typed_child attached independent literal field
  rw [named] at run read
  have nonBinder : SourceExposure481.notBinder literal.childQuery = true := by
    apply (notBinder_exact _).mpr
    intro bad eq
    have inspected := (RecordTraversal455.term_inspects_exact455 _).mpr literal.childInspected
    rw [eq] at inspected
    cases inspected
  obtain ⟨exposure,residual,anchor,replay,marks,sign,place,stored,sourceRow⟩ :=
    independent_named_read_reifies_an_exact_existing_author_anchor_without_any_raw_hop attached nonBinder read fixedGeometry
  exact ⟨childUses,card,exposure,residual,anchor,literal_occurrence literal.writtenFrom,
    run,read,replay,place,marks,sign,stored,sourceRow⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
