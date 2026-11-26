import Yulang.GeneralDeclarativeI65I74WhereGuard450
import Yulang.GeneralDeclarativeI65I74WhereListEntry411

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open RetainedFull445
open GeneralDeclarativeWitnessDeclaredState357 (point)
open ListSites449.Frame (AuthoredFrame)
open ListSites449 (WrittenListSite)
open WhereCycle411 (VerifiedWhereList WhereListHead)

def old_where_list_parent450 {p d} (old : VerifiedWhereList p d) : ParentSelection p := by
  let a := old.known
  let site : WrittenListSite p.state.core a.arg (.app a.key [.var a.binder]) :=
    ⟨a.key,a.binder,rfl,a.origin,a.authored,a.lower,a.center,a.upper,
      a.payload,a.endpoint,a.use,a.mode,a.table,a.atom⟩
  let roster : AuthoredFrame p.state.core p.root.demand.arguments d.head :=
    a.asked.symm ▸ a.named.symm ▸ .cons site .nil
  have one : roster.bindings = [(a.binder,a.payload)] := by
    have aux : ∀ args heads (x : args = [a.arg]) (y : heads = [.app a.key [.var a.binder]]),
        (x.symm ▸ y.symm ▸ (AuthoredFrame.cons site AuthoredFrame.nil) :
          AuthoredFrame p.state.core args heads).bindings = [(a.binder,a.payload)] := by
      intro args heads x y
      cases x; cases y
      rfl
    exact aux _ _ a.asked a.named
  exact ⟨d,⟨a.only,roster,by rw [a.asked]; simp,by rw [one]; simp,
    a.authoredRole,a.validRoles,a.checked,a.covered,
    (fun c m => by
      rw [a.exactWhere] at m
      cases (List.mem_singleton.mp m)
      exact ⟨a.binder,a.whereArgs,a.whereOutputs⟩),
    a.noOutputs,old.rawSafe⟩⟩

theorem migrated_original_singleton_child_is_literal_legacy450 {p d}
    (old : VerifiedWhereList p d) :
    (old_where_list_parent450 old).children = [old.known.child] := by
  let a := old.known
  let parent := old_where_list_parent450 old
  have roster : parent.chosen.roster.bindings = [(a.binder,a.payload)] := by
    have aux : ∀ args heads (x : args = [a.arg]) (y : heads = [.app a.key [.var a.binder]]),
        let site : WrittenListSite p.state.core a.arg (.app a.key [.var a.binder]) :=
          ⟨a.key,a.binder,rfl,a.origin,a.authored,a.lower,a.center,a.upper,
            a.payload,a.endpoint,a.use,a.mode,a.table,a.atom⟩
        (x.symm ▸ y.symm ▸ (AuthoredFrame.cons site AuthoredFrame.nil) :
          AuthoredFrame p.state.core args heads).bindings = [(a.binder,a.payload)] := by
      intro args heads x y
      cases x; cases y
      rfl
    exact aux _ _ a.asked a.named
  have found : (a.binder,a.payload) ∈ parent.chosen.roster.bindings := by rw [roster]; simp
  have cap := ListSites449.Frame.frame_lookup_preserves_original_capture449
    parent.chosen.roster parent.chosen.distinct found
  have org : parent.decl.requirements = [a.clause] := a.exactWhere
  have hit := actual_child_at_original_clause450 parent (i := 0) (c := a.clause) (by simp [org])
  have len : parent.children.length = 1 := by
    simp [ParentSelection.children,GeneralDeclarativeI65.children,org]
  have one : parent.children = [a.child] := by
    have eq : parent.children[0]? = some a.child := by
      rw [hit]
      simp [WhereListHead.child,WhereListHead.childDemand,literalDemand,a.whereArgs,cap]
    cases h : parent.children with
    | nil => rw [h] at len; cases len
    | cons x tail =>
      have xt : tail = [] := by
        rw [h] at len
        simpa using len
      have same : x = a.child := by simpa [h] using eq
      simp [same,xt]
  exact one

theorem original_C411_same_role_child_is_covered_by_promoted_C450 (p : FullProblem) {d}
    (old : VerifiedWhereList p.old d) (cycle : RootCycle p.state.base old.known.child) :
    ∃ w, NoSiblingMerge.check_full450 p (WhereCycle411.expected411 d) (.whereRoot w) = true := by
  let a := old_where_list_parent450 old
  let roster : OrderedPlan p.state.base a.children [.rejected] :=
    (migrated_original_singleton_child_is_literal_legacy450 old).symm ▸ .cons (.cycle cycle) .nil
  let original : OriginalRejection p.old := ⟨a,[.rejected],roster,List.mem_cons_self⟩
  have sep : NoSiblingMerge.Separate original.parent.decl := by
    change (d.requirements.map GeneralDeclarations.Clause.role).Nodup
    rw [old.known.exactWhere]
    simp
  exact (NoSiblingMerge.exact_guarded_original_report_has_data450 _ _).mpr ⟨original,rfl,sep⟩

end Yulang.GeneralDeclarativeI65.I72.WhereSites450
