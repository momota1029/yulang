import Yulang.Inference

/-!
# Model interface and symbolic terms for presence constraint generation

This interface extends the existing value/row interface by three operations.
`emptyRecord` remains the width supertype of records. `exactEmpty` is a separate
operation for the empty record expression; `required` is a field demand; and
`recordDefault` denotes the whole result type of a strict default extension.
The latter must not be replaced by a bound on its selected field alone.

This file does not construct a concrete regular model or a solver. The exact
generation theorem is uniform in every interpretation of this signature. It
adds no equation between exact emptiness and the inherited width supertype.
-/

namespace Yulang.Core.PresenceGeneration

open Inference (Expr Base)

universe u v

structure Model extends Inference.Model.{u, v} where
  exactEmpty : Ty
  required : Nat → Ty → Ty
  recordDefault : Nat → Ty → Ty → Ty

abbrev Comp (m : Model) := m.Ty × m.Row

def Comp.le (m : Model) (a b : Comp m) : Prop :=
  m.subTy a.1 b.1 ∧ m.subRow a.2 b.2

def Comp.pure (m : Model) (a : m.Ty) : Comp m := (a, m.empty)

def Comp.arrow (m : Model) (a b : Comp m) : m.Ty :=
  m.arrow a.1 a.2 b.1 b.2

inductive RowTerm (α : Type) where
  | var : α → RowTerm α
  | empty : RowTerm α
  | join : RowTerm α → RowTerm α → RowTerm α
  deriving Repr

inductive TyTerm (α : Type) where
  | var : α → TyTerm α
  | base : Base → TyTerm α
  | bottom : TyTerm α
  | top : TyTerm α
  | union : TyTerm α → TyTerm α → TyTerm α
  | inter : TyTerm α → TyTerm α → TyTerm α
  | pair : TyTerm α → TyTerm α → TyTerm α
  | emptyRecord : TyTerm α
  | exactEmpty : TyTerm α
  | required : Nat → TyTerm α → TyTerm α
  | recordDefault : Nat → TyTerm α → TyTerm α → TyTerm α
  | record : Nat → TyTerm α → TyTerm α → TyTerm α
  | variant : Nat → TyTerm α → TyTerm α
  | arrow : TyTerm α → RowTerm α → TyTerm α → RowTerm α → TyTerm α
  deriving Repr

structure CompTerm (α : Type) where
  ty : TyTerm α
  row : RowTerm α
  deriving Repr

def CompTerm.var (a : α) : CompTerm α := ⟨.var a, .var a⟩
def CompTerm.pure (a : TyTerm α) : CompTerm α := ⟨a, .empty⟩
def CompTerm.arrow (a b : CompTerm α) : TyTerm α :=
  .arrow a.ty a.row b.ty b.row

def RowTerm.eval (m : Model) (ρ : α → Comp m) : RowTerm α → m.Row
  | .var a => (ρ a).2
  | .empty => m.empty
  | .join a b => m.join (a.eval m ρ) (b.eval m ρ)

def TyTerm.eval (m : Model) (ρ : α → Comp m) : TyTerm α → m.Ty
  | .var a => (ρ a).1
  | .base b => m.base b
  | .bottom => m.bottom
  | .top => m.top
  | .union a b => m.union (a.eval m ρ) (b.eval m ρ)
  | .inter a b => m.inter (a.eval m ρ) (b.eval m ρ)
  | .pair a b => m.pair (a.eval m ρ) (b.eval m ρ)
  | .emptyRecord => m.emptyRecord
  | .exactEmpty => m.exactEmpty
  | .required l a => m.required l (a.eval m ρ)
  | .recordDefault l a b => m.recordDefault l (a.eval m ρ) (b.eval m ρ)
  | .record l a r => m.record l (a.eval m ρ) (r.eval m ρ)
  | .variant l a => m.variant l (a.eval m ρ)
  | .arrow a ea b eb => m.arrow (a.eval m ρ) (ea.eval m ρ) (b.eval m ρ) (eb.eval m ρ)

def CompTerm.eval (m : Model) (ρ : α → Comp m) (a : CompTerm α) : Comp m :=
  (a.ty.eval m ρ, a.row.eval m ρ)

def RowTerm.rename (f : α → β) : RowTerm α → RowTerm β
  | .var a => .var (f a)
  | .empty => .empty
  | .join a b => .join (a.rename f) (b.rename f)

def TyTerm.rename (f : α → β) : TyTerm α → TyTerm β
  | .var a => .var (f a)
  | .base b => .base b
  | .bottom => .bottom
  | .top => .top
  | .union a b => .union (a.rename f) (b.rename f)
  | .inter a b => .inter (a.rename f) (b.rename f)
  | .pair a b => .pair (a.rename f) (b.rename f)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .required l a => .required l (a.rename f)
  | .recordDefault l a b => .recordDefault l (a.rename f) (b.rename f)
  | .record l a r => .record l (a.rename f) (r.rename f)
  | .variant l a => .variant l (a.rename f)
  | .arrow a ea b eb => .arrow (a.rename f) (ea.rename f) (b.rename f) (eb.rename f)

def CompTerm.rename (f : α → β) (a : CompTerm α) : CompTerm β :=
  ⟨a.ty.rename f, a.row.rename f⟩

def RowTerm.subst (f : α → CompTerm β) : RowTerm α → RowTerm β
  | .var a => (f a).row
  | .empty => .empty
  | .join a b => .join (a.subst f) (b.subst f)

def TyTerm.subst (f : α → CompTerm β) : TyTerm α → TyTerm β
  | .var a => (f a).ty
  | .base b => .base b
  | .bottom => .bottom
  | .top => .top
  | .union a b => .union (a.subst f) (b.subst f)
  | .inter a b => .inter (a.subst f) (b.subst f)
  | .pair a b => .pair (a.subst f) (b.subst f)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .required l a => .required l (a.subst f)
  | .recordDefault l a b => .recordDefault l (a.subst f) (b.subst f)
  | .record l a r => .record l (a.subst f) (r.subst f)
  | .variant l a => .variant l (a.subst f)
  | .arrow a ea b eb => .arrow (a.subst f) (ea.subst f) (b.subst f) (eb.subst f)

def CompTerm.subst (f : α → CompTerm β) (a : CompTerm α) : CompTerm β :=
  ⟨a.ty.subst f, a.row.subst f⟩

@[simp] theorem RowTerm.eval_rename (m : Model) (ρ : β → Comp m)
    (f : α → β) (a : RowTerm α) :
    (a.rename f).eval m ρ = a.eval m (ρ ∘ f) := by
  induction a <;> simp_all [rename, eval]

@[simp] theorem TyTerm.eval_rename (m : Model) (ρ : β → Comp m)
    (f : α → β) (a : TyTerm α) :
    (a.rename f).eval m ρ = a.eval m (ρ ∘ f) := by
  induction a <;> simp_all [rename, eval]

@[simp] theorem CompTerm.eval_rename (m : Model) (ρ : β → Comp m)
    (f : α → β) (a : CompTerm α) :
    (a.rename f).eval m ρ = a.eval m (ρ ∘ f) := by
  simp [rename, eval]

@[simp] theorem RowTerm.eval_subst (m : Model) (ρ : β → Comp m)
    (f : α → CompTerm β) (a : RowTerm α) :
    (a.subst f).eval m ρ = a.eval m (fun x => (f x).eval m ρ) := by
  induction a <;> simp_all [subst, eval, CompTerm.eval]

@[simp] theorem TyTerm.eval_subst (m : Model) (ρ : β → Comp m)
    (f : α → CompTerm β) (a : TyTerm α) :
    (a.subst f).eval m ρ = a.eval m (fun x => (f x).eval m ρ) := by
  induction a <;> simp_all [subst, eval, CompTerm.eval]

@[simp] theorem CompTerm.eval_subst (m : Model) (ρ : β → Comp m)
    (f : α → CompTerm β) (a : CompTerm α) :
    (a.subst f).eval m ρ = a.eval m (fun x => (f x).eval m ρ) := by
  simp [subst, eval]

def extend (ρ : α → Comp m) (c : Comp m) : Option α → Comp m
  | none => c
  | some a => ρ a

@[simp] theorem extend_none (ρ : α → Comp m) (c : Comp m) :
    extend ρ c none = c := rfl

@[simp] theorem extend_some (ρ : α → Comp m) (c : Comp m) (a : α) :
    extend ρ c (some a) = ρ a := rfl

@[simp] theorem extend_comp_some (ρ : α → Comp m) (c : Comp m) :
    extend ρ c ∘ some = ρ := rfl

@[simp] theorem CompTerm.eval_var (m : Model) (ρ : α → Comp m) (a : α) :
    (CompTerm.var a).eval m ρ = ρ a := rfl

@[simp] theorem CompTerm.eval_pure (m : Model) (ρ : α → Comp m) (a : TyTerm α) :
    (CompTerm.pure a).eval m ρ = Comp.pure m (a.eval m ρ) := rfl

end Yulang.Core.PresenceGeneration
