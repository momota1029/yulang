import Yulang.GeneralSourceRoleCstCleanProducer294

/-! For an existing successful projection, the additional selected-branch
gate tests the ancestor corridor, not unrelated marks and not new typing. -/
namespace Yulang.GeneralSourceRoleCstCleanBoundary294
open GeneralSourceRoleCstTree293 (Tree Path)
open GeneralSourceRoleCstMarks294 (marks)
open GeneralSourceRoleCstMarkScope294 (classify selected_exact ancestor_exact selected_plain_iff)
open GeneralSourceRoleCstMarkPolicy294 (BranchPlain allows branch_exact guarded guarded_exact)
open GeneralSourceRoleCstSnapshot293 (Snapshot Address)
open GeneralSourceRoleCstRustSnapshot293 (exportAt export_exact)
open GeneralSourceRoleCstPath293 (follow)
open GeneralSourceRoleCstRecovery293 (TreePlain)
open GeneralSourceRoleTrack292 (Tracked)

def AncestorClear (tree : Tree) (s : Path) : Prop :=
  ∀ p k, (p,k) ∈ marks tree → classify s p ≠ .ancestor

theorem projected_selects_plain {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand))
    (projected : exportAt scope s a = some out) :
    ∃ selected, follow a.path s.root = some selected ∧ TreePlain selected := by
  obtain ⟨_,selected,raw,address,picked,_⟩ := (export_exact ..).mp projected
  exact ⟨selected,address,GeneralSourceRoleCstCleanProducer294.accepted_subtree_is_plain _ _ _ _ picked⟩

theorem projected_no_selected_marks {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand))
    (projected : exportAt scope s a = some out) :
    ∀ p k, (p,k) ∈ marks s.root → classify a.path p ≠ .selected := by
  obtain ⟨selected,here,plain⟩ := projected_selects_plain scope s a out projected
  exact (selected_plain_iff here).mp plain

theorem branch_iff_ancestor_given_projection {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand))
    (projected : exportAt scope s a = some out) :
    allows .selectedBranch s.root a.path = true ↔ AncestorClear s.root a.path := by
  have selectedFree := projected_no_selected_marks scope s a out projected
  change GeneralSourceRoleCstMarkPolicy294.branchClear s.root a.path = true ↔ _
  rw [branch_exact]
  constructor
  · intro all p k mem bad
    exact (all p k mem).2 ((ancestor_exact ..).mp bad).2
  · intro ancestors p k mem
    have notBelow : ¬ a.path <+: p := by
      rintro ⟨tail,h⟩
      exact selectedFree p k mem ((selected_exact ..).mpr ⟨tail,h.symm⟩)
    exact ⟨notBelow,fun ancPath => ancestors p k mem ((ancestor_exact ..).mpr ⟨notBelow,ancPath⟩)⟩

theorem exact_corridor {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand)) :
    guarded .selectedBranch scope s a = some out ↔
      exportAt scope s a = some out ∧ AncestorClear s.root a.path := by
  rw [guarded_exact]
  constructor
  · rintro ⟨okay,projected⟩
    exact ⟨projected,(branch_iff_ancestor_given_projection _ _ _ _ projected).mp okay⟩
  · rintro ⟨projected,ancestors⟩
    exact ⟨(branch_iff_ancestor_given_projection _ _ _ _ projected).mpr ancestors,projected⟩

end Yulang.GeneralSourceRoleCstCleanBoundary294
