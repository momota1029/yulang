import Yulang.GeneralDeclarativeI65I74WhereCohortMarks451

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)

theorem original_statuses_are_unique_at_every_position451 {s qs l r}
    (a : RawStatuses s qs l) (b : RawStatuses s qs r) : l = r := by
  induction a generalizing r with
  | nil =>
    cases b
    rfl
  | @cons q qs x xs first rest ih =>
    cases b with
    | @cons _ _ y ys there tail =>
      have truth : x = true ↔ y = true := first.exact.trans there.exact.symm
      have same : x = y := by cases x <;> cases y <;> simp_all
      rw [same,ih tail]

theorem ordered_source_point_tags_do_not_depend_on_class_numbers451 {p : Problem}
    {a : ParentSelection p} (d e : OriginalCohort a) :
    d.labelled.map Prod.fst = e.labelled.map Prod.fst := by
  have p := Option.some.inj ((readPoints_replays_all_exactly451 d.points).symm.trans
    (readPoints_replays_all_exactly451 e.points))
  rw [d.literal,e.literal,p]

theorem exact_original_class_equivalence_is_invariant_under_witness_renaming451 {p : Problem}
    {a : ParentSelection p} (d e : OriginalCohort a) {i j : Nat} {x y x' y' : Labeled}
    (dI : d.labelled[i]? = some x) (dJ : d.labelled[j]? = some y)
    (eI : e.labelled[i]? = some x') (eJ : e.labelled[j]? = some y') :
    x.2 = y.2 ↔ x'.2 = y'.2 := by
  let same := ordered_source_point_tags_do_not_depend_on_class_numbers451 d e
  have exactX : x.1 = x'.1 := by
    have both := congrArg (fun t : List RolePoint => t[i]?) same
    simpa only [List.getElem?_map,dI,eI,Option.map_some,Option.some.injEq] using both
  have exactY : y.1 = y'.1 := by
    have both := congrArg (fun t : List RolePoint => t[j]?) same
    simpa only [List.getElem?_map,dJ,eJ,Option.map_some,Option.some.injEq] using both
  have old := d.exactSame _ (List.mem_of_getElem? dI) _ (List.mem_of_getElem? dJ)
  have new := e.exactSame _ (List.mem_of_getElem? eI) _ (List.mem_of_getElem? eJ)
  exact old.trans ((by simpa only [exactX,exactY] using new.symm : _))

def OriginalMark.literal (m : OriginalMark) : Nat × Nat × List Nat × Nat × Nat × Bool :=
  (m.ordinal,m.writtenId,m.request.occurrence,m.request.demand.role,m.actualCenter,m.rawK2)

/-- Erasing the arbitrary labels could be used to compare independent
certificate choices; no chosen occurrence/representative is exposed. -/
theorem exact_all_original_literal_marks_independent_of_wires451 {p : Problem}
    {a : ParentSelection p} (d e : OriginalDiagnostic a) :
    d.marks.map OriginalMark.literal = e.marks.map OriginalMark.literal := by
  have shape : d.cohorts.labelled.map Prod.fst = e.cohorts.labelled.map Prod.fst :=
    ordered_source_point_tags_do_not_depend_on_class_numbers451 d.cohorts e.cohorts
  have values : d.bits = e.bits := original_statuses_are_unique_at_every_position451 d.status e.status
  apply List.ext_getElem?
  intro i
  unfold OriginalDiagnostic.marks
  simp only [List.getElem?_map,List.getElem?_zipWith,List.getElem?_zipIdx,values]
  have same := congrArg (fun xs : List RolePoint => xs[i]?) shape
  simp only [List.getElem?_map] at same
  cases lhs : d.cohorts.labelled[i]? with
  | none =>
    cases rhs : e.cohorts.labelled[i]? with
    | none => rfl
    | some xx => simp [lhs,rhs] at same
  | some xx =>
    cases rhs : e.cohorts.labelled[i]? with
    | none => simp [lhs,rhs] at same
    | some yy =>
      have sameTags : xx.1 = yy.1 := by simpa only [lhs,rhs,Option.map_some,Option.some.injEq] using same
      obtain ⟨⟨roleX,centerX⟩,l1⟩ := xx
      obtain ⟨⟨roleY,centerY⟩,l2⟩ := yy
      cases sameTags
      cases a.children[i]? <;> cases a.decl.requirements[i]? <;> cases e.bits[i]? <;> rfl

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
