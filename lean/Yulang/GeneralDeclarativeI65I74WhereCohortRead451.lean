import Yulang.GeneralDeclarativeI65I74WhereCohortPoints451

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open GeneralDeclarations (Clause Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeK2Alias321 (AliasCycle alias_cycle_iff)
open GeneralDeclarativeGraphRows321 (observed)

def attachLabels : List RolePoint → List Nat → Option (List Labeled)
  | [],[] => some []
  | a::as,l::ls => (attachLabels as ls).map fun tail => (a,l)::tail
  | _,_ => none

theorem attached_labels_preserve_entire_original_order451 {pts keys cells}
    (ok : attachLabels pts keys = some cells) :
    cells.map Prod.fst = pts ∧ cells.map Prod.snd = keys := by
  induction pts generalizing keys cells with
  | nil =>
    cases keys with
    | nil => cases Option.some.inj ok; exact ⟨rfl,rfl⟩
    | cons _ _ => cases ok
  | cons p ps ih =>
    cases keys with
    | nil => cases ok
    | cons l ls =>
      cases tail : attachLabels ps ls with
      | none => simp [attachLabels,tail] at ok
      | some out =>
        have exactOut : (p,l)::out = cells := by simpa [attachLabels,tail] using ok
        subst cells
        obtain ⟨fst,snd⟩ := ih tail
        simp [fst,snd]

theorem attached_labels_reflect_exact_list451 (cells : List Labeled) :
    attachLabels (cells.map Prod.fst) (cells.map Prod.snd) = some cells := by
  induction cells with
  | nil => rfl
  | cons a rest ih =>
    cases a
    simp [attachLabels,ih]

structure CohortWire where
  labels : List Nat
  cells : List (List ExactPairWire)

structure OriginalCohort {p : Problem} (a : ParentSelection p) where
  points : Points a.children
  labelled : List Labeled
  literal : labelled.map Prod.fst = points.tags
  exactSame : RawMatrix p.state.core.current.ordinary labelled labelled

def readCohort {p : Problem} (a : ParentSelection p) (w : CohortWire) :
    Option (OriginalCohort a) := do
  let orig ← readPoints a.children
  match attached : attachLabels orig.tags w.labels with
  | none => none
  | some cells =>
    if yes : readRawMatrix p.state.core.current.ordinary cells cells w.cells = true then
      some ⟨orig,cells,(attached_labels_preserve_entire_original_order451 attached).1,
        (all_raw_classes_have_exact_finite_matrix450 ..).mp ⟨_,yes⟩⟩
    else none

theorem actually_selected_parent_has_exact_finite_cohort_wire451 {p : Problem} (a : ParentSelection p)
    (r : OriginalCohort a) : ∃ w, readCohort a w = some r := by
  obtain ⟨cells,accepted⟩ := (all_raw_classes_have_exact_finite_matrix450 ..).mpr r.exactSame
  refine ⟨⟨r.labelled.map Prod.snd,cells⟩,?_⟩
  have entire : attachLabels r.points.tags (r.labelled.map Prod.snd) = some r.labelled := by
    rw [←r.literal]
    exact attached_labels_reflect_exact_list451 _
  unfold readCohort
  rw [readPoints_replays_all_exactly451 r.points]
  simp only [Bind.bind,Option.bind]
  split
  · rename_i missing
    rw [entire] at missing
    cases missing
  · rename_i out seen
    have eq := Option.some.inj (seen.symm.trans entire)
    subst out
    simp [accepted]

theorem source_has_finite_exact_raw_cohort451 {p : Problem} (a : ParentSelection p) :
    ∃ w r, readCohort a w = some r := by
  obtain ⟨points,_⟩ := source_replayed_points_are_total451 a
  obtain ⟨lab,rawPoints,classes,_⟩ := finite_whole_raw_class_table450
    p.state.core.current.ordinary points.tags
  let out : OriginalCohort a := ⟨points,lab,rawPoints,classes⟩
  obtain ⟨w,h⟩ := actually_selected_parent_has_exact_finite_cohort_wire451 a out
  exact ⟨w,out,h⟩

theorem OriginalCohort.indexed {p : Problem} {a : ParentSelection p} (r : OriginalCohort a)
    (i : Nat) {q : I72.Request} (actual : a.children[i]? = some q) :
    ∃ (point : ActualPoint q) (label : Nat), r.labelled[i]? = some (point.tag,label) := by
  obtain ⟨given,real⟩ := indexed_point_from_ordered_actual_requests451 r.points i actual
  have fst := congrArg (fun list : List RolePoint => list[i]?) r.literal
  rw [real,List.getElem?_map] at fst
  cases h : r.labelled[i]? with
  | none => simp [h] at fst
  | some pair =>
    obtain ⟨pt,l⟩ := pair
    have tagEq : pt = given.tag := by simpa [h] using fst
    exact ⟨given,l,by rw [tagEq]⟩

theorem root_cycle_exact_named_point451 {s : I72.State} {q : I72.Request} (a : ActualPoint q) :
    RootCycle s q ↔ AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) a.center := by
  constructor
  · rintro ⟨x,whereArg,cycle⟩
    rw [a.literal] at whereArg
    cases List.mem_singleton.mp whereArg
    exact cycle
  · intro yes
    exact ⟨point a.center,a.literal ▸ List.mem_cons_self,yes⟩

theorem equal_label_links_actual_child_roots451 {p : Problem} {a : ParentSelection p} (r : OriginalCohort a)
    {i j : Nat} {q v : I72.Request} (first : a.children[i]? = some q) (last : a.children[j]? = some v) :
    ∃ (x : ActualPoint q) (y : ActualPoint v) (li lj : Nat),
      r.labelled[i]? = some (x.tag,li) ∧ r.labelled[j]? = some (y.tag,lj) ∧
      (li = lj ↔ q.demand.role = v.demand.role ∧ Al p.state.core.current.ordinary x.center y.center) ∧
      (li = lj → (RootCycle p.state q ↔ RootCycle p.state v)) := by
  obtain ⟨x,li,left⟩ := r.indexed i first
  obtain ⟨y,lj,right⟩ := r.indexed j last
  have related := r.exactSame _ (List.mem_of_getElem? left) _ (List.mem_of_getElem? right)
  refine ⟨x,y,li,lj,left,right,related,?_⟩
  intro same
  have alias := (related.mp same).2
  exact (root_cycle_exact_named_point451 x).trans
    ((alias_cycle_iff alias).trans (root_cycle_exact_named_point451 y).symm)

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
