import Yulang.GeneralDeclarativeI65I74FullEntry445

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedFull445
open Yulang.GeneralDeclarativeI65
open MixedFixed442
open Checker408 (Problem Result)

/-- Source-generated row corresponds to the original output, not a
different row merely storing a semantically equal value. -/
def writerStored445 (s : FullState) {q : I72.Request}
    (source : SourceSelection ⟨s.base,q⟩) :
    StoredSelection (retainSelected s source) source := by
  let r := source.origin
  let a := source.own.2.out
  have exactOutput := original_replayed_ref_equates_same_event_output442 r a
  let certify (out : NamedMixedOutput401 s.base.b6 r.event.frame r.i0)
      (eq : a.named = out) :
      {shape : RefShape out.rhs // storedKey ⟨q,r.event.frame,r.i0,out⟩ shape = eventKey source} := by
    subst out
    exact ⟨.intro a.use a.mode a.table rfl (by decide) rfl rfl ⟨a.rowCap,a.row⟩
      ⟨a.valueCap,a.value⟩,rfl⟩
  let row := eventRow r.event r.i0
  let checked := certify (r.event.outputs r.i0) exactOutput
  exact ⟨row,List.mem_append_right _ (List.mem_ofFn.mpr ⟨r.i0,rfl⟩),checked.val,checked.property⟩

def selectedIntoEmptyBecomesLocal445 {p : Problem} (source : SourceSelection p)
    (fresh : FreshOutput source) :
    LocalSelection (retainSelected (liftState p.state) source) p.root :=
  ⟨source,fresh,writerStored445 (liftState p.state) source,by
    simp [retainSelected,liftState,selectedRows,source.origin.onlyOutput]⟩

theorem no_stored_row_is_no_new_selection445 {p : FullProblem} {r : Result}
    {w : RefPositions441.Wire} (empty : p.state.retained = []) :
    check_full p r (.mixedOutput w) = false := by
  unfold check_full
  cases h : readSource p.old w with
  | none => simp [h]
  | some a => simp [h,matchesSelection,empty]

theorem no_exact_target_is_no_new_selection445 {p : FullProblem} {r : Result}
    {w : RefPositions441.Wire} {s : SourceSelection p.old}
    (read : readSource p.old w = some s)
    (wrong : ∀ row ∈ p.state.retained, row.target ≠ p.old.root.demand.outputs[s.origin.i0].target) :
    check_full p r (.mixedOutput w) = false := by
  cases verdict : check_full p r (.mixedOutput w) with
  | false => rfl
  | true =>
    simp only [check_full,read] at verdict
    obtain ⟨actual,eq⟩ := matches_selection_exact445 (Bool.and_eq_true_iff.mp verdict).1
    have key := congrArg (fun k : RowKey => k.output.target) actual.kept.exactKey
    change actual.kept.row.target = p.root.demand.outputs[actual.source.origin.i0].target at key
    apply False.elim
    let targetOf (src : SourceSelection p.old) : Nat := p.old.root.demand.outputs[src.origin.i0].target
    exact wrong actual.kept.row actual.kept.member (key.trans (congrArg targetOf eq))

theorem old_target_read_forbids_new_selection445 {p : FullProblem} {r : Result}
    {w : RefPositions441.Wire} {s : SourceSelection p.old}
    (read : readSource p.old w = some s)
    (blocked : OldModelReads p.state.base.core p.old.root.demand.outputs[s.origin.i0].target) :
    check_full p r (.mixedOutput w) = false := by
  have missing : checkFresh s = false := by
    cases fresh : checkFresh s with
    | false => rfl
    | true => exact (((check_fresh_exact445 _).mp fresh).1 (every_old_read_is_covered445 blocked)).elim
  simp [check_full,read,matchesSelection,missing]

end Yulang.GeneralDeclarativeI65.I72.RetainedFull445
