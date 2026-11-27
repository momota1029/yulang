import Yulang.GeneralDeclarativeI65I74OriginalReportAnchor460
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.OriginalAnchorSpec
open Yulang.GeneralDeclarativeI65
open Yulang.GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeWitnessVarianceFixtures357 (source)
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataRows291 (Row)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeHead320 (Equation)
open RecordTraversal455 (RawSnapshot)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Core.PresenceGeneration (TyTerm)
open List410 (ExactEscapeWire)
open InlineStructuralPolicy458 (Ticket)
open RetainedFull445

private def empty : Pattern := .app 9 []
private def c0 : Clause := ⟨60,19,[.var 3],[]⟩
private def c1 : Clause := ⟨81,19,[.record 10 (.var 3) empty],[]⟩
private def impl : Declaration :=
  ⟨218,19,[.record 10 (.record 30 (.var 3) empty) empty],[c0,c1],[],[]⟩
private def authored : InputBundle :=
  let keys : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,keys⟩,⟨.absent,keys⟩,⟨0,[⟨19,1,[]⟩]⟩,[impl]⟩

private def ordinary : RawSnapshot :=
  ⟨⟨[],[]⟩,[⟨0,.record 10 (.variable 1) (.primitive .emptyRecord [])⟩,
             ⟨1,.record 30 (.variable 1) (.primitive .emptyRecord [])⟩]⟩
private def nativeRoot : TyTerm Nat := .record 10 (.var 1) .emptyRecord
private def original : Origin := ⟨0,[21,4],.ordinary nativeRoot⟩
private def fixture : Option FullProblem := do
  let graph ← compile source
  let bundle ← GeneralSourceMetadataBareBundle291.compile authored
  let env : Environment := ⟨3,2,0,source,graph,bundle⟩
  let state : CoreState := ⟨⟨env,ordinary,[]⟩,[],[original],[]⟩
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨state,atlas⟩,⟨[31,7],⟨19,[point 0],[]⟩⟩⟩)

private def p : FullProblem := fixture.get (by decide +kernel)
private def escape : ExactEscapeWire := ⟨[0,1],[0,1]⟩
private def witnessAt (v h w : Nat) : AnchoredFieldWire p.old :=
  ⟨⟨v,h,w⟩,⟨.down () ⟨0,.same,.field 0 0,(.older (.old 0) : Ticket)⟩ escape (.stop ()),
    ⟨⟨1,.same,1⟩,[],.same⟩⟩⟩
private def r0 : RoutedReadyMixed457.ReportAtField := ⟨[31,7],218,0,60,[(.field 10,1)],1⟩
private def r1 : RoutedReadyMixed457.ReportAtField := ⟨[31,7],218,1,81,[(.field 10,1)],1⟩

/-- info: [true, true, true, true, true, true, true] -/
#guard_msgs in
#eval [decide (readAnchoredField p.old (witnessAt 0 0 0) = some r0),
       decide (readAnchoredField p.old (witnessAt 0 0 1) = some r1),
       (readAnchoredField p.old (witnessAt 0 0 2)).isNone,
       (readAnchoredField p.old (witnessAt 1 0 0)).isNone,
       (readAnchoredField p.old (witnessAt 0 1 0)).isNone,
       decide (readAnchoredField p.old (witnessAt 0 0 0) ≠ some {r0 with occurrence := [31,8]}),
       decide (readAnchoredField p.old (witnessAt 0 0 0) ≠ some r1)]

theorem actual_original_where_indices_are_checked_but_not_elected460 :
    readAnchoredField p.old (witnessAt 0 0 0) = some r0 ∧
      readAnchoredField p.old (witnessAt 0 0 1) = some r1 ∧
      r0.path = r1.path ∧ r0.terminal = r1.terminal ∧ r0 ≠ r1 := by
  decide +kernel

theorem actual_both_addresses_satisfy_independent_path_receipt460 :
    anchored p.old r0 ∧ anchored p.old r1 :=
  ⟨attained_exact_report_iff_finite_anchored_read.mp ⟨_,actual_original_where_indices_are_checked_but_not_elected460.1⟩,
   attained_exact_report_iff_finite_anchored_read.mp ⟨_,actual_original_where_indices_are_checked_but_not_elected460.2.1⟩⟩

open CommonNominalFullCarrier (Ty Equivalent record)
private def recursiveCell : Ty :=
  .record 30 (.block [.record 30 (.inl 0) .emptyRecord] 0) .emptyRecord
private theorem unroll_fixture_field :
    Equivalent recursiveCell (record 30 recursiveCell .emptyRecord) := by
  have same (k : Nat) : CommonNominalFullCarrier.observeTy k recursiveCell =
      CommonNominalFullCarrier.observeTy k (record 30 recursiveCell .emptyRecord) := by
    cases k <;> rfl
  constructor
  · intro k
    rw [← same]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro k
    rw [same]
    exact CommonNominalFullDemand.producerLe_refl _

private def model : I72.Model :=
  ⟨fun n => (if n = 0 then record 10 recursiveCell .emptyRecord else recursiveCell,Common.rowEmpty),
   fun _ => none, fun n => if n = 0 then some (.ordinary nativeRoot) else none⟩

theorem actual_original_anchor_same_state_is_fitting460 : I72.FitsFull p.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ nope; cases nope
  · intro _ nope; cases nope
  · intro row seen
    change row ∈ ordinary.equations at seen
    simp only [ordinary,List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with rfl|rfl
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact unroll_fixture_field
  · intro _ nope; cases nope
  · intro found seen
    change found ∈ [original] at seen
    cases List.mem_singleton.mp seen
    rfl
  · intro _ nope; cases nope

theorem first_source_path_holds_in_same_actual_fit460 :
    (∃ (a : OriginalAnchor p.old) (last : Term) (used : Bool),
      exactReport a r0.path r0.terminal = r0 ∧
      RoutedInlineStructural458.ModelTrail p.state.base.core model a.capture.lower a.code
        r0.path r0.terminal used ∧
      CoordinateWalk (fun _ => queryKeys p.state.base.core) a.capture.lower
        (normalized (readTerm a.original)) r0.path r0.terminal last ∧
      GeneralDeclarativeK2Alias321.AliasCycle p.state.base.core.current.ordinary
        (GeneralDeclarativeGraphRows321.observed p.state.base.core.current.ordinary) r0.terminal) :=
  addressed_field_holds_in_every_same_fit (p := p)
    actual_both_addresses_satisfy_independent_path_receipt460.1 model
    actual_original_anchor_same_state_is_fitting460

#print axioms actual_original_anchor_same_state_is_fitting460
#print axioms first_source_path_holds_in_same_actual_fit460
#print axioms actual_original_where_indices_are_checked_but_not_elected460
#print axioms actual_both_addresses_satisfy_independent_path_receipt460

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.OriginalAnchorSpec
