/-!
Type-level syntax for the paper execution types and capture-avoiding
simultaneous substitution. Variadic tuple/record/variant/nominal arguments use
explicit right-associated sequence constructors, keeping the syntax directly
inductive in Lean. This module does not identify it with the restricted
`HigherOrder.Ty` or claim a typing/executor theorem.
-/
namespace YulangClosure.PaperTypes

inductive Base where
  | unit | bool | int | float | string | bytes | path | char
  deriving DecidableEq, Repr

inductive Mutability where
  | immutable | mutable
  deriving DecidableEq, Repr

inductive Ty where
  | var (index : Nat)
  | base (kind : Base)
  | top | bottom
  | union (left right : Ty)
  | intersection (left right : Ty)
  | tupleNil | tupleCons (head tail : Ty)
  | recordNil | recordCons (label : Nat) (mutability : Mutability) (fieldType tail : Ty)
  | variantNil | variantCons (label : Nat) (payloads tail : Ty)
  | nominal (identity : Nat) (arguments : Ty)
  | mu (body : Ty)
  | thunk (result : Ty)
  | callable (carrier result : Ty)
  | poly (body : Ty)
  deriving DecidableEq, Repr

open Ty

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

def mapVars (ρ : Nat → Nat) : Ty → Ty
  | .var i => .var (ρ i)
  | .base b => .base b
  | .top => .top
  | .bottom => .bottom
  | .union a b => .union (mapVars ρ a) (mapVars ρ b)
  | .intersection a b => .intersection (mapVars ρ a) (mapVars ρ b)
  | .tupleNil => .tupleNil
  | .tupleCons a b => .tupleCons (mapVars ρ a) (mapVars ρ b)
  | .recordNil => .recordNil
  | .recordCons label mutability a b => .recordCons label mutability (mapVars ρ a) (mapVars ρ b)
  | .variantNil => .variantNil
  | .variantCons label a b => .variantCons label (mapVars ρ a) (mapVars ρ b)
  | .nominal id args => .nominal id (mapVars ρ args)
  | .mu body => .mu (mapVars (liftRen ρ) body)
  | .thunk result => .thunk (mapVars ρ result)
  | .callable carrier result => .callable (mapVars ρ carrier) (mapVars ρ result)
  | .poly body => .poly (mapVars (liftRen ρ) body)

def liftSub (σ : Nat → Ty) : Nat → Ty
  | 0 => .var 0
  | i + 1 => mapVars Nat.succ (σ i)

def subst (σ : Nat → Ty) : Ty → Ty
  | .var i => σ i
  | .base b => .base b
  | .top => .top
  | .bottom => .bottom
  | .union a b => .union (subst σ a) (subst σ b)
  | .intersection a b => .intersection (subst σ a) (subst σ b)
  | .tupleNil => .tupleNil
  | .tupleCons a b => .tupleCons (subst σ a) (subst σ b)
  | .recordNil => .recordNil
  | .recordCons label mutability a b => .recordCons label mutability (subst σ a) (subst σ b)
  | .variantNil => .variantNil
  | .variantCons label a b => .variantCons label (subst σ a) (subst σ b)
  | .nominal id args => .nominal id (subst σ args)
  | .mu body => .mu (subst (liftSub σ) body)
  | .thunk result => .thunk (subst σ result)
  | .callable carrier result => .callable (subst σ carrier) (subst σ result)
  | .poly body => .poly (subst (liftSub σ) body)

def idSub (i : Nat) : Ty := .var i

theorem liftRen_id : liftRen id = id := by
  funext i
  cases i <;> simp [liftRen]

theorem liftRen_comp (ρ κ : Nat → Nat) :
    liftRen ρ ∘ liftRen κ = liftRen (ρ ∘ κ) := by
  funext i
  cases i <;> simp [liftRen]

theorem mapVars_id (t : Ty) : mapVars id t = t := by
  induction t <;> simp_all [mapVars, liftRen_id]

theorem liftSub_id : liftSub idSub = idSub := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [liftSub, idSub, mapVars, Nat.succ_eq_add_one]

theorem subst_id (t : Ty) : subst idSub t = t := by
  induction t <;> simp_all [subst, liftSub_id, idSub]

theorem mapVars_comp (ρ κ : Nat → Nat) (t : Ty) :
    mapVars ρ (mapVars κ t) = mapVars (ρ ∘ κ) t := by
  induction t generalizing ρ κ <;> simp_all [mapVars, liftRen_comp]

theorem mapLiftSub (ρ : Nat → Nat) (σ : Nat → Ty) :
    (fun i => mapVars (liftRen ρ) (liftSub σ i)) =
      liftSub (fun i => mapVars ρ (σ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      simp only [liftSub]
      rw [mapVars_comp, mapVars_comp]
      congr 1

theorem subst_mapVars (σ : Nat → Ty) (ρ : Nat → Nat) (t : Ty) :
    subst σ (mapVars ρ t) = subst (fun i => σ (ρ i)) t := by
  induction t generalizing σ ρ with
  | var i => rfl
  | base b => rfl
  | top => rfl
  | bottom => rfl
  | union a b iha ihb => simp [subst, mapVars, iha, ihb]
  | intersection a b iha ihb => simp [subst, mapVars, iha, ihb]
  | tupleNil => rfl
  | tupleCons a b iha ihb => simp [subst, mapVars, iha, ihb]
  | recordNil => rfl
  | recordCons label mutability a b iha ihb => simp [subst, mapVars, iha, ihb]
  | variantNil => rfl
  | variantCons label a b iha ihb => simp [subst, mapVars, iha, ihb]
  | nominal id args ih => simp [subst, mapVars, ih]
  | mu body ih =>
      apply congrArg Ty.mu
      have h : (fun i => liftSub σ (liftRen ρ i)) =
          liftSub (fun i => σ (ρ i)) := by
        funext i
        cases i <;> simp [liftSub, liftRen]
      calc
        subst (liftSub σ) (mapVars (liftRen ρ) body) =
            subst (fun i => liftSub σ (liftRen ρ i)) body :=
          ih (liftSub σ) (liftRen ρ)
        _ = subst (liftSub (fun i => σ (ρ i))) body := by rw [h]
  | thunk result ih => simp [subst, mapVars, ih]
  | callable carrier result ihc ihr => simp [subst, mapVars, ihc, ihr]
  | poly body ih =>
      apply congrArg Ty.poly
      have h : (fun i => liftSub σ (liftRen ρ i)) =
          liftSub (fun i => σ (ρ i)) := by
        funext i
        cases i <;> simp [liftSub, liftRen]
      calc
        subst (liftSub σ) (mapVars (liftRen ρ) body) =
            subst (fun i => liftSub σ (liftRen ρ i)) body :=
          ih (liftSub σ) (liftRen ρ)
        _ = subst (liftSub (fun i => σ (ρ i))) body := by rw [h]

theorem mapVars_subst (ρ : Nat → Nat) (σ : Nat → Ty) (t : Ty) :
    mapVars ρ (subst σ t) = subst (fun i => mapVars ρ (σ i)) t := by
  induction t generalizing ρ σ with
  | var i => rfl
  | base b => rfl
  | top => rfl
  | bottom => rfl
  | union a b iha ihb => simp [subst, mapVars, iha, ihb]
  | intersection a b iha ihb => simp [subst, mapVars, iha, ihb]
  | tupleNil => rfl
  | tupleCons a b iha ihb => simp [subst, mapVars, iha, ihb]
  | recordNil => rfl
  | recordCons label mutability a b iha ihb => simp [subst, mapVars, iha, ihb]
  | variantNil => rfl
  | variantCons label a b iha ihb => simp [subst, mapVars, iha, ihb]
  | nominal id args ih => simp [subst, mapVars, ih]
  | mu body ih =>
      simp only [mapVars, subst]
      rw [ih (liftRen ρ) (liftSub σ)]
      apply congrArg Ty.mu
      apply congrArg (fun s => subst s body)
      exact mapLiftSub ρ σ
  | thunk result ih => simp [subst, mapVars, ih]
  | callable carrier result ihc ihr => simp [subst, mapVars, ihc, ihr]
  | poly body ih =>
      simp only [mapVars, subst]
      rw [ih (liftRen ρ) (liftSub σ)]
      apply congrArg Ty.poly
      apply congrArg (fun s => subst s body)
      exact mapLiftSub ρ σ

theorem liftSub_comp (σ τ : Nat → Ty) :
    (fun i => subst (liftSub τ) (liftSub σ i)) =
      liftSub (fun i => subst τ (σ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      calc
        subst (liftSub τ) (mapVars Nat.succ (σ i)) =
        subst (fun j => liftSub τ (Nat.succ j)) (σ i) :=
          subst_mapVars (liftSub τ) Nat.succ (σ i)
        _ = subst (fun j => mapVars Nat.succ (τ j)) (σ i) := by
          apply congrArg (fun s => subst s (σ i))
          funext j
          simp [liftSub]
        _ = mapVars Nat.succ (subst τ (σ i)) :=
          (mapVars_subst Nat.succ τ (σ i)).symm

theorem subst_comp (σ τ : Nat → Ty) (t : Ty) :
    subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  induction t generalizing σ τ with
  | var i => rfl
  | base b => rfl
  | top => rfl
  | bottom => rfl
  | union a b iha ihb => simp [subst, iha, ihb]
  | intersection a b iha ihb => simp [subst, iha, ihb]
  | tupleNil => rfl
  | tupleCons a b iha ihb => simp [subst, iha, ihb]
  | recordNil => rfl
  | recordCons label mutability a b iha ihb => simp [subst, iha, ihb]
  | variantNil => rfl
  | variantCons label a b iha ihb => simp [subst, iha, ihb]
  | nominal id args ih => simp [subst, ih]
  | mu body ih =>
      simp only [subst]
      rw [ih (liftSub σ) (liftSub τ)]
      apply congrArg Ty.mu
      apply congrArg (fun s => subst s body)
      exact liftSub_comp σ τ
  | thunk result ih => simp [subst, ih]
  | callable carrier result ihc ihr => simp [subst, ihc, ihr]
  | poly body ih =>
      simp only [subst]
      rw [ih (liftSub σ) (liftSub τ)]
      apply congrArg Ty.poly
      apply congrArg (fun s => subst s body)
      exact liftSub_comp σ τ

structure OperationInstance where
  identity : Nat
  typeArguments : Ty
  payloadType : Ty
  responseType : Ty
  deriving DecidableEq, Repr

def OperationInstance.subst (σ : Nat → Ty) (op : OperationInstance) : OperationInstance :=
  { op with
    typeArguments := YulangClosure.PaperTypes.subst σ op.typeArguments
    payloadType := YulangClosure.PaperTypes.subst σ op.payloadType
    responseType := YulangClosure.PaperTypes.subst σ op.responseType }

theorem OperationInstance.subst_id (op : OperationInstance) : op.subst idSub = op := by
  cases op
  simp [OperationInstance.subst, YulangClosure.PaperTypes.subst_id]

theorem OperationInstance.subst_comp (σ τ : Nat → Ty) (op : OperationInstance) :
    (op.subst σ).subst τ = op.subst (fun i => YulangClosure.PaperTypes.subst τ (σ i)) := by
  cases op
  simp [OperationInstance.subst, YulangClosure.PaperTypes.subst_comp]

end YulangClosure.PaperTypes
