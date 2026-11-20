import Yulang.GeneralSourceRoleCstMarkFixture294

/-! A separate, optional diagnostic receipt. The adapter does not obtain or
authenticate Rust's complete diagnostic list by inspecting CST bytes. -/
namespace Yulang.GeneralSourceRoleCstDiagnostics294
open GeneralSourceRoleCstTree293 (Path)
open GeneralSourceRoleCstMarkScope294 (Zone classify unrelated_exact)
open GeneralSourceRoleCstMarkPolicy294 (Policy)

inductive Cause where
  | structural | conflictingOperator | other
  deriving DecidableEq, Repr

structure Diagnostic where
  cause : Cause
  /-- This is attached ownership, not necessarily the parser diagnostic ID. -/
  owner : Option Path
  deriving DecidableEq, Repr

inductive Scan (Brand : Type) where
  | absent
  | failed
  | reported (brand : Brand) (items : List Diagnostic)

def permitted (what : Policy) (selected : Path) (d : Diagnostic) : Bool :=
  match what,d.owner with
  | .selectedBranch, some p => classify selected p == .unrelated
  | _,_ => false

def permits {Brand : Type} [DecidableEq Brand] (what : Policy) (brand : Brand)
    (selected : Path) : Scan Brand → Bool
  | .reported producer ds =>
    decide (producer = brand) && ds.all (permitted what selected)
  | _ => false

def IndependentPermission (what : Policy) (selected : Path) (d : Diagnostic) : Prop :=
  what = .selectedBranch ∧ ∃ p, d.owner = some p ∧ (¬selected <+: p) ∧ ¬p <+: selected

theorem permitted_exact (what : Policy) (selected : Path) (d : Diagnostic) :
    permitted what selected d = true ↔ IndependentPermission what selected d := by
  cases what with
  | whole => simp [permitted,IndependentPermission]
  | selectedBranch =>
    cases h : d.owner with
    | none => simp [permitted,IndependentPermission,h]
    | some p =>
      have e := unrelated_exact selected p
      simpa [permitted,IndependentPermission,h] using e

theorem permits_exact {Brand : Type} [DecidableEq Brand] (what : Policy) (brand : Brand)
    (selected : Path) (scan : Scan Brand) : permits what brand selected scan = true ↔
       ∃ ds, scan = .reported brand ds ∧ ∀ d ∈ ds, IndependentPermission what selected d := by
  cases scan with
  | absent => simp [permits]
  | failed => simp [permits]
  | reported sender ds =>
    simp [permits,List.all_eq_true,permitted_exact]
    constructor
    · rintro ⟨rfl,h⟩; exact ⟨ds,⟨rfl,rfl⟩,h⟩
    · rintro ⟨_,⟨rfl,rfl⟩,h⟩; exact ⟨rfl,h⟩

theorem whole_report_exact {Brand : Type} [DecidableEq Brand] (brand : Brand)
    (selected : Path) (scan : Scan Brand) :
    permits .whole brand selected scan = true ↔ scan = .reported brand [] := by
  rw [permits_exact]
  constructor
  · rintro ⟨ds,done,clear⟩
    cases ds with
    | nil => exact done
    | cons d ds =>
      have bad := (clear d List.mem_cons_self).1
      cases bad
  · rintro rfl
    exact ⟨[],rfl,by simp⟩

theorem unlocated_blocks_selected (selected : Path) (d : Diagnostic) (unknown : d.owner = none) :
    permitted .selectedBranch selected d = false := by simp [permitted,unknown]

end Yulang.GeneralSourceRoleCstDiagnostics294
