import Yulang.GeneralDeclarativeI65I74WhereSamePhase454

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.SamePhase454
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open InternalK2452
open OutputPhase452
open GroupedEntry453 (GroupedReport SameReport CohortView)
open GeneralDeclarativeCaptureClosure320 (withOrdinary)

theorem same_phase_key_iff_same_role_and_raw_alias_at_actual_marks454
    {p : FullProblem} (x : InternalReport p) {u v : OriginalMark}
    (uIn : u ∈ x.original.diagnostics.marks) (vIn : v ∈ x.original.diagnostics.marks) :
    u.classLabel = v.classLabel ↔
      RawSame p.state.base.core.current.ordinary
        (u.request.demand.role,u.actualCenter) (v.request.demand.role,v.actualCenter) := by
  have first := (any_mark_is_actual_original_diagnostic451 x.original.diagnostics uIn).2.1
  have last := (any_mark_is_actual_original_diagnostic451 x.original.diagnostics vIn).2.1
  exact x.original.diagnostics.cohorts.exactSame _
    (List.mem_of_getElem? first) _ (List.mem_of_getElem? last)

theorem every_reported_group_keeps_every_actual_origin454 {p : FullProblem}
    (x : InternalReport p) {r : GroupedReport} (same : SameReport r (exactReport x))
    {g : CohortView} (reported : g ∈ r.origins) :
    ∃ group : CohortOrigins, group ∈ x.groups ∧
      g = group.marks.map OriginalMark.literal ∧
      group.marks = x.original.diagnostics.atClass group.key ∧
      group.marks ≠ [] ∧ group.marks.Sublist x.original.diagnostics.marks ∧
      ∀ mark ∈ group.marks,
        (∃ site : SourcePointAt x.original.parent mark.ordinal,
          site.original.id = mark.writtenId ∧ site.capture = mark.actualCenter ∧
          site.request = mark.request) ∧ RootCycle p.state.base mark.request := by
  obtain ⟨group,member,source⟩ := List.mem_map.mp (same.2.2.mem_iff.mp reported)
  obtain ⟨all,nonempty,order,cyclic⟩ := one_checked_entry_means_K2_at_every_original452
    x.original.diagnostics member
  exact ⟨group,member,source.symm,all,nonempty,order,fun mark seen =>
    ⟨original_mark_has_exact_actual_source_site452 x.original.diagnostics (order.subset seen),
      cyclic mark seen⟩⟩

theorem each_actual_cycle_has_exactly_one_internal_reported_group454
    {p : FullProblem} (x : InternalReport p) {r : GroupedReport}
    (same : SameReport r (exactReport x)) {m : OriginalMark}
    (seen : m ∈ x.original.diagnostics.marks) :
    RootCycle p.state.base m.request ↔
      ∃ g : CohortOrigins,
        (g ∈ x.groups ∧ m ∈ g.marks ∧ g.marks.map OriginalMark.literal ∈ r.origins) ∧
        ∀ h : CohortOrigins, h ∈ x.groups ∧ m ∈ h.marks → h = g := by
  constructor
  · intro cycle
    obtain ⟨g,⟨member,atMark⟩,unique⟩ :=
      (actual_cycle_has_exactly_one_internal_diagnostic452 x.original.diagnostics seen).mp cycle
    have actual : g.marks.map OriginalMark.literal ∈ (exactReport x).origins :=
      List.mem_map.mpr ⟨g,member,rfl⟩
    exact ⟨g,⟨member,atMark,same.2.2.mem_iff.mpr actual⟩,unique⟩
  · rintro ⟨g,⟨member,atMark,_⟩,unique⟩
    exact (actual_cycle_has_exactly_one_internal_diagnostic452 x.original.diagnostics seen).mpr
      ⟨g,⟨member,atMark⟩,unique⟩

theorem real_output_emission_at_this_substep_leaves_the_graph_unchanged454
    {p : FullProblem} (x : InternalReport p) :
    emissionRows (verifiedEmissionPairs452 x.original.diagnostics) = [] ∧
    withOrdinary p.state.base.core.current.ordinary
      (emissionRows (verifiedEmissionPairs452 x.original.diagnostics)) =
      p.state.base.core.current.ordinary :=
  output_equation_substep_exactly_preserves_raw_input452 _

/-- No given profile, labels, matrix, or raw-safe sibling selection
are needed. This theorem starts from an independently authorized
parent and true K2 at an arbitrary indexed original child. -/
theorem cyclic_original_of_any_actual_scoped_parent_has_exact_witness454
    {p : FullProblem} (a : ParentSelection p.old) {i : Nat} {q : I72.Request}
    (child : a.children[i]? = some q) (cycle : RootCycle p.state.base q) :
    ∃ x : InternalReport p, x.original.parent = a ∧
      Exact p (exactReport x) ∧
      ∃ w, check_full454 p (.rawGrouped (exactReport x)) (.rawGrouped w) = true := by
  obtain ⟨_,cohort,_⟩ := source_has_finite_exact_raw_cohort451 a
  obtain ⟨bs,⟨status⟩⟩ := every_original_request_has_a_raw_status451 p.state.base a.children
  let d : OriginalDiagnostic a := ⟨cohort,bs,status⟩
  let x : InternalReport p := ⟨⟨a,d⟩⟩
  have len : a.children.length = a.decl.requirements.length := by
    simp [ParentSelection.children,GeneralDeclarativeI65.children]
  have inside : i < a.decl.requirements.length :=
    len ▸ (List.getElem?_eq_some_iff.mp child).choose
  let clause := a.decl.requirements[i]
  have atClause : a.decl.requirements[i]? = some clause := List.getElem?_eq_getElem inside
  obtain ⟨b,n,l,k,shape,_,mark,_⟩ := every_actual_clause_has_a_preserved_location_mark451 d atClause
  let actual : I72.Request := ⟨p.root.occurrence ++ [i],
    ⟨clause.role,[GeneralDeclarativeWitnessDeclaredState357.point n],[]⟩⟩
  let kept : OriginalMark := ⟨i,clause.id,actual,n,l,k⟩
  have member : kept ∈ d.marks := List.mem_of_getElem? mark
  have same : actual = q := Option.some.inj
    ((any_mark_is_actual_original_diagnostic451 d member).1.symm.trans child)
  have k2 : RootCycle p.state.base kept.request := by simpa only [kept,same] using cycle
  obtain ⟨g,⟨seen,_⟩,_⟩ := (actual_cycle_has_exactly_one_internal_diagnostic452 d member).mp k2
  have someGroup : x.groups ≠ [] := by
    intro empty
    change g ∈ x.groups at seen
    rw [empty] at seen
    exact List.not_mem_nil seen
  have exact : Exact p (exactReport x) := ⟨x,someGroup,rfl,rfl,List.Perm.refl _⟩
  exact ⟨x,rfl,exact,independent_same_phase_report_has_cumulative_witness454 p _ exact⟩

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.SamePhase454
