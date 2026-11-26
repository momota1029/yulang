import Yulang.GeneralDeclarativeI65I74SelectedEntry447

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem Result)
open RetainedFull445
open MixedFixed442
open WhereAssociated432 (matches_associated_report_exact432)

theorem all_C446_Bool_unchanged447 (p : FullProblem) (r : Result)
    (w : RetainedSplit446.Witness446) :
    check_full447 p r (.previous w) = RetainedSplit446.check_full446 p r w := rfl

theorem all_R21_Bool_unchanged447 (p : Problem) (r : Result)
    (w : RefPositions441.Witness) :
    check_full447 (liftProblem p) r (.previous (.previous (.previous w))) =
      RefPositions441.check p r w :=
  RetainedSplit446.all_R21_Bool_unchanged446 p r w

/-- Exact sound reflection for an accepted new wire. No report-only
classification, reordered write, or replay of a different source. -/
theorem accepted_wire_reflects_same_local_source447 {p : FullProblem} {r : Result}
    {w : RefPositions441.Wire} (yes : check_full447 p r (.localSplitOutput w) = true) :
    ∃ a : LocalSelection p.state p.root,
      readLocalSource p.old w = some a.source ∧ r = a.report := by
  simp only [check_full447] at yes
  cases got : readLocalSource p.old w with
  | none => simp [got] at yes
  | some source =>
    rw [got] at yes
    obtain ⟨matched,reported⟩ := Bool.and_eq_true_iff.mp yes
    obtain ⟨a,exactSource⟩ := matches_selection_exact445 matched
    have exactReport := (matches_associated_report_exact432 _ _).mp reported
    exact ⟨a,by rw [←exactSource],by
      change r = sourceReport a.source
      rw [exactSource]
      exact exactReport⟩

/-- Recognition and concretization use the SAME independent local source
relation, unchanged FullState, and the original full report (including
dictionary and ordered typed writes). This is scoped, not full R_full. -/
theorem selected_wire_iff_exact_local_report447 (p : FullProblem) (r : Result) :
    (∃ w : RefPositions441.Wire, check_full447 p r (.localSplitOutput w) = true) ↔
    ∃ a : LocalSelection p.state p.root, r = a.report := by
  constructor
  · rintro ⟨w,yes⟩
    obtain ⟨a,_,report⟩ := accepted_wire_reflects_same_local_source447 yes
    exact ⟨a,report⟩
  · rintro ⟨a,rfl⟩
    exact independent_selected_report_has_finite_witness447 p a

/-- The original writer creates the canonical local state from the actual
authored event and independently checked fresh target. Reification is
not furnished externally as a solver function. -/
theorem writer_result_has_exact_selected_witness447 {p : Problem}
    (a : SourceSelection p) (fresh : FreshOutput a) :
    ∃ w : RefPositions441.Wire, check_full447
        ⟨retainSelected (liftState p.state) a,p.root⟩ (sourceReport a) (.localSplitOutput w) = true := by
  exact independent_selected_report_has_finite_witness447
    ⟨retainSelected (liftState p.state) a,p.root⟩ (selectedIntoEmptyBecomesLocal445 a fresh)

theorem empty_store_rejects_every_selected_wire447 {p : FullProblem}
    (empty : p.state.retained = []) (r : Result) (w : RefPositions441.Wire) :
    check_full447 p r (.localSplitOutput w) = false := by
  cases accepted : check_full447 p r (.localSplitOutput w) with
  | false => rfl
  | true =>
    obtain ⟨a,_,_⟩ := accepted_wire_reflects_same_local_source447 accepted
    have one := a.single
    rw [empty] at one
    cases one

theorem wrong_fixed_slot_rejects_every_selected_wire447 {p : FullProblem} {r : Result}
    (wrong : ∀ i : Fin p.root.demand.outputs.length,
      ∀ row ∈ p.state.retained, row.target ≠ p.root.demand.outputs[i].target)
    (w : RefPositions441.Wire) :
    check_full447 p r (.localSplitOutput w) = false := by
  cases accepted : check_full447 p r (.localSplitOutput w) with
  | false => rfl
  | true =>
    obtain ⟨a,_,_⟩ := accepted_wire_reflects_same_local_source447 accepted
    have key := congrArg (fun k : RowKey => k.output.target) a.kept.exactKey
    exact (wrong a.source.origin.i0 a.kept.row a.kept.member key).elim

theorem loaded_old_slot_rejects_every_selected_wire447 {p : FullProblem} {r : Result}
    (loaded : ∀ i : Fin p.root.demand.outputs.length,
      OldModelReads p.state.base.core p.root.demand.outputs[i].target)
    (w : RefPositions441.Wire) :
    check_full447 p r (.localSplitOutput w) = false := by
  cases accepted : check_full447 p r (.localSplitOutput w) with
  | false => rfl
  | true =>
    obtain ⟨a,_,_⟩ := accepted_wire_reflects_same_local_source447 accepted
    exact (a.fresh.1 (every_old_read_is_covered445 (loaded a.source.origin.i0))).elim

end Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
