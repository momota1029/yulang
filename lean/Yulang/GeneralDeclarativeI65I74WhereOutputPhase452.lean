import Yulang.GeneralDeclarativeI65I74WhereCohortGroups451
import Yulang.GeneralDeclarativeI65I74WhereCohortFullFit451

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.OutputPhase452
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open GeneralDeclarations (Clause)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralNominalDemandMerging (SameInputs outputAtoms)
open GeneralDeclarativeCaptureClosure320 (withOrdinary)
open PresenceNormalForm (Atom)

theorem source_site_has_no_child_output_specification452 {p : Checker408.Problem}
    {a : ParentSelection p} {i : Nat} (x : SourcePointAt a i) :
    x.site.occurrence.demand.outputs = [] := rfl

theorem original_mark_has_exact_actual_source_site452 {p : Checker408.Problem}
    {a : ParentSelection p} (d : OriginalDiagnostic a) {m : OriginalMark}
    (seen : m ∈ d.marks) :
    ∃ x : SourcePointAt a m.ordinal,
      x.original.id = m.writtenId ∧ x.capture = m.actualCenter ∧ x.request = m.request := by
  obtain ⟨i,index⟩ := List.mem_iff_getElem?.mp seen
  have inside : i < a.decl.requirements.length :=
    (ordered_marks_no_fewer_and_no_extra_original_clauses451 d) ▸
      (List.getElem?_eq_some_iff.mp index).choose
  let original := a.decl.requirements[i]
  have present : a.decl.requirements[i]? = some original := List.getElem?_eq_getElem inside
  obtain ⟨b,n,l,k,_,_,mark,_⟩ := every_actual_clause_has_a_preserved_location_mark451 d present
  have eq := Option.some.inj (index.symm.trans mark)
  subst m
  obtain ⟨x,stored⟩ := original_clause_projected_as_same_input_site451 a present
  have req : x.request = ⟨p.root.occurrence ++ [i],⟨original.role,[point n],[]⟩⟩ := by
    apply Option.some.inj
    -- Read the mark's actual indexed request (the reconstructed payload).
    have indexed := (any_mark_is_actual_original_diagnostic451 d (List.mem_of_getElem? mark)).1
    exact x.sameRequest.symm.trans indexed
  have center : x.capture = n := by
    have h := congrArg (fun q : I72.Request => q.demand.arguments) req
    exact congrArg GeneralDeclarativeWhere319.Capture.center (List.singleton_inj.mp h)
  exact ⟨x,congrArg Clause.id stored,center,req⟩

theorem exact_class_sites_are_same_input_with_empty_output_rows452 {p : FullProblem}
    {a : ParentSelection p.old} (d : OriginalDiagnostic a) {g : CohortOrigins}
    (group : g ∈ d.cohortsWithOrigins) {m n : OriginalMark}
    (left : m ∈ g.marks) (right : n ∈ g.marks)
    (x : SourcePointAt a m.ordinal) (y : SourcePointAt a n.ordinal)
    (xCenter : x.capture = m.actualCenter) (yCenter : y.capture = n.actualCenter)
    (xReq : x.request = m.request) (yReq : y.request = n.request) :
    SameInputs (allAssignments p.state) x.site y.site ∧ outputAtoms x.site y.site = [] := by
  have marks := (generated_group_has_exact_source_order451 d group).1
  rw [marks] at left right
  obtain ⟨lm,lk⟩ := (only_marks_of_selected_class451 d _ _).mp left
  obtain ⟨rm,rk⟩ := (only_marks_of_selected_class451 d _ _).mp right
  have lx := (any_mark_is_actual_original_diagnostic451 d lm).2.1
  have ry := (any_mark_is_actual_original_diagnostic451 d rm).2.1
  have l' : d.cohorts.labelled[m.ordinal]? = some (x.actual.tag,g.key) := by
    rw [lx,lk]
    simp [ActualPoint.tag,SourcePointAt.actual,xCenter,←xReq]
  have r' : d.cohorts.labelled[n.ordinal]? = some (y.actual.tag,g.key) := by
    rw [ry,rk]
    simp [ActualPoint.tag,SourcePointAt.actual,yCenter,←yReq]
  exact ⟨(indexed_cohort_label_proves_same_input_from_actual_source451 d.cohorts x y g.key l' r').1,
    by simp [outputAtoms, source_site_has_no_child_output_specification452]⟩

/-- The existing output equation operator, applied to genuine original
members. The list of pairs is not an order prescribed for the solver. -/
structure ActualPair {p : FullProblem} {a : ParentSelection p.old}
    (d : OriginalDiagnostic a) where
  group : CohortOrigins
  genuine : group ∈ d.cohortsWithOrigins
  left : OriginalMark
  right : OriginalMark
  inLeft : left ∈ group.marks
  inRight : right ∈ group.marks
  first : SourcePointAt a left.ordinal
  second : SourcePointAt a right.ordinal
  firstCenter : first.capture = left.actualCenter
  secondCenter : second.capture = right.actualCenter
  firstRequest : first.request = left.request
  secondRequest : second.request = right.request

theorem actual_group_members_form_source_pair452 {p : FullProblem}
    {a : ParentSelection p.old} (d : OriginalDiagnostic a) {g : CohortOrigins}
    (valid : g ∈ d.cohortsWithOrigins) {m n : OriginalMark}
    (head : m ∈ g.marks) (next : n ∈ g.marks) :
    ∃ pair : ActualPair (p := p) d, pair.group = g ∧ pair.left = m ∧ pair.right = n := by
  have source := (generated_group_has_exact_source_order451 d valid).2.2
  obtain ⟨x,_,cx,qx⟩ := original_mark_has_exact_actual_source_site452 d (source.subset head)
  obtain ⟨y,_,cy,qy⟩ := original_mark_has_exact_actual_source_site452 d (source.subset next)
  exact ⟨⟨g,valid,m,n,head,next,x,y,cx,cy,qx,qy⟩,rfl,rfl,rfl⟩

def ActualPair.rows {p : FullProblem} {a : ParentSelection p.old}
    {d : OriginalDiagnostic a} (x : ActualPair (p := p) d) : List (Atom Nat) :=
  outputAtoms x.first.site x.second.site

theorem each_emission_pair_is_authorized_and_writes_nothing452 {p : FullProblem}
    {a : ParentSelection p.old} {d : OriginalDiagnostic a} (x : ActualPair (p := p) d) :
    SameInputs (allAssignments p.state) x.first.site x.second.site ∧ x.rows = [] :=
  exact_class_sites_are_same_input_with_empty_output_rows452 d x.genuine x.inLeft x.inRight
    x.first x.second x.firstCenter x.secondCenter x.firstRequest x.secondRequest

def emissionRows {p : FullProblem} {a : ParentSelection p.old}
    {d : OriginalDiagnostic a} (xs : List (ActualPair (p := p) d)) : List (Atom Nat) :=
  xs.flatMap ActualPair.rows

theorem output_equation_substep_exactly_preserves_raw_input452 {p : FullProblem}
    {a : ParentSelection p.old} {d : OriginalDiagnostic a}
    (xs : List (ActualPair (p := p) d)) :
    emissionRows xs = [] ∧
      withOrdinary p.state.base.core.current.ordinary (emissionRows xs) =
        p.state.base.core.current.ordinary := by
  have empty : emissionRows xs = [] := by
    induction xs with
    | nil => rfl
    | cons h t ih =>
      simp [emissionRows, each_emission_pair_is_authorized_and_writes_nothing452 h |>.2,
        show t.flatMap ActualPair.rows = [] from ih]
  exact ⟨empty,by rw [empty]; simp [withOrdinary]⟩

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.OutputPhase452
