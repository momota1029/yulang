import Yulang.GeneralDeclarativeI65I74WhereOrdinal450
import Yulang.GeneralNominalDemandMerging

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.NoSiblingMerge
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open Checker408 (Result)
open GeneralDeclarations (Declaration Clause)
open CommonRoleOutermostResolver (Tree)

def Separate (d : Declaration) : Prop :=
  (d.requirements.map Clause.role).Nodup

def noSiblingMerge (p : FullProblem) : Bool :=
  match visible p.state.base.core p.root with
  | [d] => decide ((d.requirements.map Clause.role).Nodup)
  | _ => false

theorem literal_child_role_is_original450 (capture : Nat → GeneralDeclarativeWhere319.Capture) (c : Clause) :
    (literalDemand capture c).role = c.role := by
  unfold literalDemand
  split <;> rfl

theorem supplied_original_child_roles_preclude_sibling_merge450 {p : Checker408.Problem}
    (a : ParentSelection p) (sep : Separate a.decl)
    {i j : Nat} (different : i ≠ j) {x y : I72.Request}
    (first : a.children[i]? = some x) (last : a.children[j]? = some y) :
    x.demand.role ≠ y.demand.role := by
  have witness : ∀ (index : Nat) (req : I72.Request), a.children[index]? = some req →
      ∃ clause : Clause, a.decl.requirements[index]? = some clause ∧ req.demand.role = clause.role := by
    intro n q indexed
    cases atClause : a.decl.requirements[n]? with
    | none =>
      simp [ParentSelection.children,GeneralDeclarativeI65.children,List.getElem?_map,List.getElem?_zipIdx,atClause] at indexed
    | some c =>
      have same := Option.some.inj ((actual_child_at_original_clause450 a atClause).symm.trans indexed)
      exact ⟨c,rfl,(congrArg (fun k : I72.Request => k.demand.role) same).symm.trans
        (literal_child_role_is_original450 _ c)⟩
  obtain ⟨xc,xi,xr⟩ := witness i x first
  obtain ⟨yc,yi,yr⟩ := witness j y last
  obtain ⟨hi,firstC⟩ := List.getElem?_eq_some_iff.mp xi
  obtain ⟨hj,lastC⟩ := List.getElem?_eq_some_iff.mp yi
  rw [xr,yr,←firstC,←lastC]
  intro sameRole
  apply different
  have ii : i < (a.decl.requirements.map Clause.role).length := by simpa using hi
  have jj : j < (a.decl.requirements.map Clause.role).length := by simpa using hj
  have roles : (a.decl.requirements.map Clause.role)[i]'ii = (a.decl.requirements.map Clause.role)[j]'jj := by
    simpa using sameRole
  exact sep.getElem_inj.mp roles

theorem differently_roled_sites_cannot_merge450 {roles}
    (x y : GeneralNominalDemandMerging.Site roles)
    (different : x.occurrence.demand.role ≠ y.occurrence.demand.role)
    (models : GeneralNominalCommonBridge.Assignment → Prop) :
    ¬GeneralNominalDemandMerging.SameInputs models x y :=
  fun same => different same.1

def GuardedOriginal (p : FullProblem) (r : Result) : Prop :=
  ∃ a : OriginalRejection p.old, r = a.report ∧ Separate a.parent.decl

/-- Only this namespace is the promoted entry. Previous tags use C449
directly so the unguarded C450 literal-trace helper cannot bypass the cut. -/
def check_full450 (p : FullProblem) (r : Result) : Witness → Bool
  | .previous w => ListSites449.Frame.check_full449 p r w
  | .whereRoot w => noSiblingMerge p && WhereSites450.check_full450 p r (.whereRoot w)

theorem previous_is_identical450 (p : FullProblem) (r : Result) (w : ListSites449.Frame.Witness) :
    check_full450 p r (.previous w) = ListSites449.Frame.check_full449 p r w := rfl

theorem actual_guard_is_exact_visible_source450 {p : FullProblem} {a : OriginalRejection p.old} :
    noSiblingMerge p = true ↔ Separate a.parent.decl := by
  unfold noSiblingMerge
  have roster : visible p.state.base.core p.root = [a.parent.decl] := a.parent.chosen.only
  rw [roster]
  simp [Separate]

theorem exact_guarded_original_report_has_data450 (p : FullProblem) (r : Result) :
    (∃ w, check_full450 p r (.whereRoot w) = true) ↔ GuardedOriginal p r := by
  constructor
  · rintro ⟨w,ok⟩
    obtain ⟨guard,base⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨a,exact,_,_⟩ := only_true_original_ordered_reports_are_accepted450 base
    exact ⟨a,exact,actual_guard_is_exact_visible_source450.mp guard⟩
  · rintro ⟨a,rfl,guard⟩
    obtain ⟨w,ok⟩ := original_ordered_rejection_reifies_same_report450 p a
    exact ⟨w,Bool.and_eq_true_iff.mpr ⟨(actual_guard_is_exact_visible_source450 (a := a)).mpr guard,ok⟩⟩

def ClassifiedAs (p : FullProblem) (r : Result) : Prop :=
  ListSites449.Frame.ClassifiedAs449 p r ∨ GuardedOriginal p r

def ReportEvidence (p : FullProblem) (m : I72.Model) (r : Result) : Prop :=
  ListSites449.Frame.ReportEvidence449 p m r ∨
    GuardedOriginal p r ∧ WhereSites450.ReportEvidence p.state.base m p.root r

theorem check_full_sound450 (p : FullProblem) (r : Result) (w : Witness)
    (ok : check_full450 p r w = true) :
    ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r := by
  cases w with
  | previous w =>
    have old := ListSites449.Frame.check_full_sound449 p r w ok
    exact ⟨.inl old.1,fun m fit => .inl (old.2 m fit)⟩
  | whereRoot w =>
    have entry := Bool.and_eq_true_iff.mp ok
    have guarded := (exact_guarded_original_report_has_data450 _ _).mp ⟨w,ok⟩
    obtain ⟨a,rfl,_,_⟩ := only_true_original_ordered_reports_are_accepted450 entry.2
    obtain ⟨e,tr,summary,out⟩ := independent_original_rejection_has_real_trace450 a
    exact ⟨.inr guarded,fun m fit => .inr ⟨guarded,e,tr,summary,out,
      exact_where_trace_model_meaning450 tr m fit.1⟩⟩

theorem guarded_entry_declines_true_parent_K2450 {p : FullProblem}
    (cycle : RootCycle p.state.base p.root) (r : Result) (w : WhereWire) :
    check_full450 p r (.whereRoot w) = false := by
  simp only [check_full450,actual_parent_K2_cannot_be_relabelled_as_child450 cycle r w,
    Bool.and_false]

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.NoSiblingMerge
