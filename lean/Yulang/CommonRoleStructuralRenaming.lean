import Yulang.CommonRoleStructuralNamedInputs

/-! Structural decomposition commutes with arbitrary variable renaming.
This concerns the established decomposition fragment, not full subtyping. -/
namespace Yulang.CommonRoleStructuralRenaming
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceNormalForm (Atom)
open CommonRoleStructuralDecomposition

theorem weight_rename (f : α → β) (t : TyTerm α) :
    CommonRoleRecursiveConflicts.weight (t.rename f) = CommonRoleRecursiveConflicts.weight t := by
  induction t <;> simp_all [TyTerm.rename, CommonRoleRecursiveConflicts.weight]

theorem expandFuel_rename (f : α → β) (k : Nat) (l r : TyTerm α) :
    expandFuel k (l.rename f) (r.rename f) = (expandFuel k l r).map (Atom.rename f) := by
  induction k generalizing l r with
  | zero => rfl
  | succ k ih =>
    cases l <;> cases r <;> simp only [TyTerm.rename,expandFuel]
    all_goals try rfl
    all_goals try (simp only [List.map_append,List.map_cons,List.map_nil,Atom.rename,ih])
    all_goals split <;> simp_all [List.map_cons,List.map_nil,Atom.rename,TyTerm.rename]

theorem atom_rename (f : α → β) (a : Atom α) :
    atom (a.rename f) = (atom a).map (Atom.rename f) := by
  cases a with
  | tyLe l r => simp only [Atom.rename,atom,expand,weight_rename,expandFuel_rename]
  | rowLe l r => rfl

theorem row_rename_congr (f g : Nat → α) (t : RowTerm Nat)
    (same : ∀ x ∈ CommonRoleStructuralNamedInputs.rowNames t, f x = g x) :
    t.rename f = t.rename g := by
  induction t with
  | var x => simp only [RowTerm.rename,same x (by simp [CommonRoleStructuralNamedInputs.rowNames])]
  | empty => rfl
  | join a b ia ib =>
    simp only [RowTerm.rename]
    rw [ia (fun x h => same x (List.mem_append_left _ h)),
      ib (fun x h => same x (List.mem_append_right _ h))]

theorem ty_rename_congr (f g : Nat → α) (t : TyTerm Nat)
    (same : ∀ x ∈ CommonRoleStructuralNamedInputs.tyNames t, f x = g x) :
    t.rename f = t.rename g := by
  induction t with
  | var x => simp only [TyTerm.rename,same x (by simp [CommonRoleStructuralNamedInputs.tyNames])]
  | arrow a ea b eb ia ib =>
    simp only [TyTerm.rename]
    rw [ia (fun x h => same x (by simp [CommonRoleStructuralNamedInputs.tyNames,h])),
      row_rename_congr f g ea (fun x h => same x (by simp [CommonRoleStructuralNamedInputs.tyNames,h])),
      ib (fun x h => same x (by simp [CommonRoleStructuralNamedInputs.tyNames,h])),
      row_rename_congr f g eb (fun x h => same x (by simp [CommonRoleStructuralNamedInputs.tyNames,h]))]
  | _ => simp_all [TyTerm.rename,CommonRoleStructuralNamedInputs.tyNames]

theorem atom_rename_congr (f g : Nat → α) (a : Atom Nat)
    (same : ∀ x ∈ CommonRoleStructuralNamedInputs.atomNames a, f x = g x) :
    a.rename f = a.rename g := by
  cases a with
  | tyLe a b =>
    simp only [Atom.rename]
    rw [ty_rename_congr f g a (fun x h => same x (List.mem_append_left _ h)),
      ty_rename_congr f g b (fun x h => same x (List.mem_append_right _ h))]
  | rowLe a b =>
    simp only [Atom.rename]
    rw [row_rename_congr f g a (fun x h => same x (List.mem_append_left _ h)),
      row_rename_congr f g b (fun x h => same x (List.mem_append_right _ h))]

theorem row_rename_comp (f : α → β) (g : β → γ) (t : RowTerm α) :
    (t.rename f).rename g = t.rename (g ∘ f) := by
  induction t <;> simp_all [RowTerm.rename]

theorem ty_rename_comp (f : α → β) (g : β → γ) (t : TyTerm α) :
    (t.rename f).rename g = t.rename (g ∘ f) := by
  induction t <;> simp_all [TyTerm.rename,row_rename_comp]

theorem atom_rename_comp (f : α → β) (g : β → γ) (a : Atom α) :
    (a.rename f).rename g = a.rename (g ∘ f) := by
  cases a <;> simp [Atom.rename,ty_rename_comp,row_rename_comp]

theorem row_rename_id (t : RowTerm α) : t.rename id = t := by
  induction t <;> simp_all [RowTerm.rename]

theorem ty_rename_id (t : TyTerm α) : t.rename id = t := by
  induction t <;> simp_all [TyTerm.rename,row_rename_id]

theorem atom_rename_id (a : Atom α) : a.rename id = a := by
  cases a <;> simp [Atom.rename,ty_rename_id,row_rename_id]

end Yulang.CommonRoleStructuralRenaming
