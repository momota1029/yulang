import Yulang.GeneralDeclarativeI65I74RefPositionEntry441

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)
open CommonRecursiveNominalIntervals (Endpoint Bounds Argument)
open Core.PresenceGeneration (RowTerm TyTerm)
open Checker408 (Problem Result)

theorem same_visible_ref_occurrence441 {s q d e} (a : Original s q d) (b : Original s q e) :
    d = e ∧ a.arg = b.arg ∧ a.key = b.key ∧
    a.rowBinder = b.rowBinder ∧ a.valueBinder = b.valueBinder := by
  have declaration := (List.cons.inj (a.only.symm.trans b.only)).1
  have input := (List.cons.inj (a.asked.symm.trans b.asked)).1
  cases declaration
  have rendered := (List.cons.inj (a.written.symm.trans b.written)).1
  have both := Pattern.app.inj rendered
  have rowAndRest := List.cons.inj both.2
  exact ⟨rfl,input,both.1,Pattern.var.inj rowAndRest.1,
    Pattern.var.inj (List.cons.inj rowAndRest.2).1⟩

/-- Exact row and value names agree in a single fitting State.
This stronger ref result uses authored typed positions (not a model
equating differently named payloads, nor substituting a value for a row). -/
theorem same_fitting_ref_names441 {s q d e} (a : Original s q d)
    (b : Original s q e) (m : I72.Model) (fit : I72.Fits s m) :
    a.rowName = b.rowName ∧ a.valueName = b.valueName := by
  have same := (same_visible_ref_occurrence441 a b).2.1
  have lo := a.actualOrigin m fit
  have hi := b.actualOrigin m fit
  rw [same] at lo
  have exactEndpoint := Option.some.inj (lo.symm.trans hi)
  have positions := List.cons.inj (Endpoint.nominal.inj exactEndpoint).2
  have row := RowTerm.var.inj (Bounds.point.inj (Sum.inr.inj positions.1))
  have val := TyTerm.var.inj (Endpoint.ordinary.inj
    (Bounds.point.inj (Sum.inl.inj (List.cons.inj positions.2).1)))
  exact ⟨row,val⟩

theorem two_verified_ref_wires_preserve_each_original_channel441
    {p : Problem} {r t : Result} {w v : Wire}
    (left : check p r (.reference w) = true) (right : check p t (.reference v) = true) :
    r = t ∧
    ∃ (d e : Declaration) (a : Original p.state p.root d) (b : Original p.state p.root e),
      a.rowBinder = b.rowBinder ∧ a.valueBinder = b.valueBinder ∧
      ∀ (m : I72.Model), I72.Fits p.state m →
        a.capture a.rowBinder = b.capture b.rowBinder ∧
        a.capture a.valueBinder = b.capture b.valueBinder := by
  obtain ⟨d,_,a,_,exactR⟩ := checked_ref_returns_original_report441 left
  obtain ⟨e,_,b,_,exactT⟩ := checked_ref_returns_original_report441 right
  have same := same_visible_ref_occurrence441 a b
  refine ⟨exactR.trans ((congrArg leafReport same.1).trans exactT.symm),
    ⟨d,e,a,b,same.2.2.2.1,same.2.2.2.2,?_⟩⟩
  intro m fit
  have names := same_fitting_ref_names441 a b m fit
  exact ⟨by rw [a.rowCapture,b.rowCapture,names.1],
    by rw [a.valueCapture,b.valueCapture,names.2]⟩


/-- A genuine row/value nominal is not equivalent to a nominal containing
only values, even if the tags and the number of arguments happen to agree.
This is a limitation of the legacy Expr encoder, not a rejection rule. -/
theorem typed_ref_cannot_be_flattened_to_legacy_value_arguments441
    (key other : Nat) (row : Common.Row) (value : CommonNominalFullCarrier.Ty)
    (before : List CommonNominalFullCarrier.Ty) :
    ¬CommonNominalFullCarrier.Equivalent
      (CommonNominalFullCarrier.nominal key [.inr row,.inl value])
      (CommonNominalFullCarrier.nominal other (before.map Sum.inl)) := by
  intro h
  have shapes := (CommonNominalFullCarrier.nominal_regular_invariant_exact _ _ _ _).mp h.1
  cases before with
  | nil => simp at shapes
  | cons head _ =>
    have opposed := shapes.2.2 0 (.inr row) (.inl head) rfl rfl
    exact opposed

theorem legacy_raw_encoder_has_no_mixed_row_value_image441
    (key other : Nat) (row : Common.Row) (value : CommonNominalFullCarrier.Ty)
    (terms : List GeneralNominalCenteredHeadMatExpressions.Expr)
    (variables : GeneralNominalMaterialization.Mode → Nat → CommonNominalFullCarrier.Ty)
    (mode : GeneralNominalMaterialization.Mode) :
    ¬CommonNominalFullCarrier.Equivalent
      (CommonNominalFullCarrier.nominal key [.inr row,.inl value])
      (GeneralNominalCenteredHeadMatExpressions.value variables mode (.nominal other terms)) :=
  typed_ref_cannot_be_flattened_to_legacy_value_arguments441 key other row value
    (GeneralNominalCenteredHeadMatExpressions.values variables .actual terms)

end Yulang.GeneralDeclarativeI65.I72.RefPositions441
