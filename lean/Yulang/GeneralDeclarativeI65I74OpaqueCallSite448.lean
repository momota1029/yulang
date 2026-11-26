import Yulang.GeneralDeclarativeI65I74OpaqueWholeEntry448

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Opaque448.Whole
open Yulang.GeneralDeclarativeI65
open Checker408 (Result)
open GeneralDeclarations (Declaration)
open RetainedFull445
open Roster VisibleInput

def callSiteRoleRows (p : FullProblem) (scope : CallerScope) (source : List LocatedDeclaration) :
    List Declaration :=
  (projectDeclarations scope source).filter (fun d => d.role == p.root.demand.role)

/-- Source-side relation on the whole projected list. Loading/access is
independent caller input, not selected by a checker witness. Source
validation is tied to the exact compiled snapshot separately. -/
structure CallerChoice (p : FullProblem) (scope : CallerScope) (source : List LocatedDeclaration) where
  point : VerifiedPoint p.old
  roster : BareRows p.state.base.core (callSiteRoleRows p scope source)
  picked : Declaration
  only : roster.living point.known.key = [picked]
  noOutputs : p.root.demand.outputs = []
  declaredRole : ∃ row ∈ p.state.base.core.current.environment.source.roles.rows,
    row.role = p.root.demand.role

def CallerChoice.report {p scope source} (a : CallerChoice p scope source) : Result :=
  Check408.nullaryReport a.picked

private theorem transport_preserves_living {s : GeneralDeclarativeI65.State} {rows other}
    (same : rows = other) (a : BareRows s rows) (key : Nat) :
    (show BareRows s other from same ▸ a).living key = a.living key := by
  cases same
  rfl

def CallerChoice.toWhole {p src scope rows} (a : CallerChoice p scope rows)
    (related : SameResolvedInput p src scope rows) :
    WholeChoice p.old := by
  let ids : visible p.state.base.core p.root = callSiteRoleRows p scope rows :=
    source_projection_reads_entire_original_role_list448 related
  exact ⟨a.point,ids.symm ▸ a.roster,a.picked,
    (transport_preserves_living ids.symm a.roster _).trans a.only,a.noOutputs,a.declaredRole⟩

def CallerChoice.fromWhole {p src scope rows} (a : WholeChoice p.old)
    (related : SameResolvedInput p src scope rows) :
    CallerChoice p scope rows := by
  let ids : visible p.state.base.core p.root = callSiteRoleRows p scope rows :=
    source_projection_reads_entire_original_role_list448 related
  exact ⟨a.point,ids ▸ a.roster,a.picked,
    (transport_preserves_living ids a.roster _).trans a.only,a.noOutputs,a.authoredRole⟩

/-- Relate actual independent caller-side selection and exact accepted
reports. No witness is used to supply or narrow the visible registry. -/
theorem exact_call_site_choice_iff_whole_wire448 {p src scope rows}
    (related : SameResolvedInput p src scope rows) (r : Result) :
    (∃ a : CallerChoice p scope rows, r = a.report) ↔
      ∃ w : NamedWire, check_full448 p r (.wholeBare w) = true := by
  rw [whole_wire_iff_exact_independent_report448]
  constructor
  · rintro ⟨a,er⟩
    exact ⟨a.toWhole related,er⟩
  · rintro ⟨a,er⟩
    exact ⟨CallerChoice.fromWhole a related,er⟩

theorem exact_call_site_choice_in_same_model448 {p src scope rows}
    (related : SameResolvedInput p src scope rows) (a : CallerChoice p scope rows) :
    ∃ w : NamedWire, check_full448 p a.report (.wholeBare w) = true ∧
      ∀ m, FitsFull p.state m → ReportEvidence448 p m a.report := by
  obtain ⟨w,ok⟩ := (exact_call_site_choice_iff_whole_wire448 related a.report).mp ⟨a,rfl⟩
  exact ⟨w,ok,(check_full_sound448 p a.report (.wholeBare w) ok).2⟩

theorem adding_hidden_rows_preserves_exact_call_site_reports448 {p src scope rows hidden}
    (related : SameResolvedInput p src scope rows)
    (secret : ∀ row ∈ hidden, branchVisible scope row = false)
    (r : Result) :
    (∃ a : CallerChoice p scope rows, r = a.report) ↔
    (∃ a : CallerChoice p scope (rows ++ hidden), r = a.report) :=
  (exact_call_site_choice_iff_whole_wire448 related r).trans
    (exact_call_site_choice_iff_whole_wire448
      (hidden_source_addition_keeps_same_full_problem448 related secret) r).symm

/-- Even a different submitted origin cannot make two genuine matching
bare declarations look like one in an actual fitting state. Both
direct origins read the same physical slot, hence the same native key.
The checked roster is determined by the full state. -/
theorem fitting_visible_overlap_declines_every_new_wire448 {p : FullProblem}
    (point : VerifiedPoint p.old)
    (roster : BareRows p.state.base.core (visible p.state.base.core p.root))
    (overlap : 2 ≤ (roster.living point.known.key).length)
    (m : I72.Model) (fit : FitsFull p.state m) (r : Result) (w : NamedWire) :
    check_full448 p r (.wholeBare w) = false := by
  cases tested : check_full448 p r (.wholeBare w) with
  | false => rfl
  | true =>
    obtain ⟨selected,_,_⟩ := accepted_whole_wire_is_exact_choice448 tested
    have definitelyOnePhysical :=
      List.singleton_inj.mp (point.known.asked.symm.trans selected.point.known.asked)
    have slot : point.known.rootOriginal.slot = selected.point.known.rootOriginal.slot :=
      point.known.actualLower.trans ((congrArg (·.lower) definitelyOnePhysical).trans
        selected.point.known.actualLower.symm)
    have name := same_native_slot_same_endpoint point.known.authored selected.point.known.authored slot
      m fit.1
    rw [point.known.exact,selected.point.known.exact] at name
    have key := (CommonRecursiveNominalIntervals.Endpoint.nominal.inj name).1
    have sameRoster := Option.some.inj
      ((read_bare_roster_exact448 roster).symm.trans (read_bare_roster_exact448 selected.roster))
    rw [sameRoster,key,selected.only] at overlap
    simp at overlap

theorem original_root_K2_declines_every_new_wire448 {p : FullProblem}
    (cycle : RootCycle p.state.base p.root) (r : Result) (w : NamedWire) :
    check_full448 p r (.wholeBare w) = false := by
  cases tested : check_full448 p r (.wholeBare w) with
  | false => rfl
  | true =>
    obtain ⟨selected,_,_⟩ := accepted_whole_wire_is_exact_choice448 tested
    exact (selected.point.safe cycle).elim


end Yulang.GeneralDeclarativeI65.I72.Opaque448.Whole
