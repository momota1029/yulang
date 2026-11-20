import Yulang.GeneralSourceRoleCstMarkScope294

/-! Optional adapter admission policies, not source-language validity. -/
namespace Yulang.GeneralSourceRoleCstMarkPolicy294
open GeneralSourceRoleCstTree293 (Tree Path Kind)
open GeneralSourceRoleCstMarks294 (Mark marks no_marks_exact)
open GeneralSourceRoleCstMarkScope294 (Zone classify unrelated_exact)
open GeneralSourceRoleCstRecovery293 (TreePlain)
open GeneralSourceRoleCstSnapshot293 (Address Snapshot)
open GeneralSourceRoleCstRustSnapshot293 (exportAt)
open GeneralSourceRoleTrack292 (Tracked)

inductive Policy where
  | whole | selectedBranch
  deriving DecidableEq, Repr

def branchClear (root : Tree) (s : Path) : Bool :=
  (marks root).all (fun m => classify s m.1 == .unrelated)

def allows (policy : Policy) (root : Tree) (s : Path) : Bool :=
  match policy with
  | .whole => (marks root).isEmpty
  | .selectedBranch => branchClear root s

def BranchPlain (root : Tree) (s : Path) : Prop :=
  ∀ p k, (p,k) ∈ marks root → (¬ s <+: p) ∧ ¬ p <+: s

theorem branch_exact (root : Tree) (s : Path) : branchClear root s = true ↔ BranchPlain root s := by
  rw [branchClear,List.all_eq_true]
  constructor
  · intro accepted p k hit
    exact (unrelated_exact ..).mp (beq_iff_eq.mp (accepted (p,k) hit))
  · intro declared p hit
    exact beq_iff_eq.mpr ((unrelated_exact ..).mpr (declared p.1 p.2 hit))

theorem whole_exact (root : Tree) (s : Path) : allows .whole root s = true ↔ TreePlain root := by
  simp [allows,no_marks_exact]

theorem whole_implies_branch (root : Tree) (s : Path) (ok : allows .whole root s = true) :
    allows .selectedBranch root s = true := by
  have h := (no_marks_exact root).mpr ((whole_exact root s).mp ok)
  simp [allows,branchClear,h]

def guarded {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) : Option (Tracked Scope (Address Brand)) :=
  if allows policy s.root a.path then exportAt scope s a else none

theorem guarded_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand)) :
    guarded policy scope s a = some out ↔
      allows policy s.root a.path = true ∧ exportAt scope s a = some out := by
  by_cases h : allows policy s.root a.path = true <;> simp [guarded,h]

theorem selected_gate_preserves_whole_success {Scope Brand : Type} [DecidableEq Brand]
    (scope : Scope) (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand))
    (strict : guarded .whole scope s a = some out) :
    guarded .selectedBranch scope s a = some out := by
  obtain ⟨accepted,table⟩ := (guarded_exact ..).mp strict
  exact (guarded_exact ..).mpr ⟨whole_implies_branch _ _ accepted,table⟩

end Yulang.GeneralSourceRoleCstMarkPolicy294
