import Yulang.RecursiveEffects

/-!
# The effect extension preserves the original core

`expr`, `formula` and `context` include the original core syntax and constraints
without changing their types or rows. The preservation theorem below compares
the actual generated formula, including every fresh binder and value-restricted
let branch. An arbitrary ambient operation signature environment is irrelevant
to a core expression with no operation calls.
-/

namespace Yulang.RecursiveEffects.Conservativity

open Inference (Model Comp CompTerm)
open RowInference (RowAlgebra RowView)

variable {Op Key Scope : Type}

def expr : Inference.Expr → Expr Op Key Scope
  | .var n => .var n
  | .lit b => .lit b
  | .lam body => .lam (expr body)
  | .app f x => .app (expr f) (expr x)
  | .letE v body => .letE (expr v) (expr body)
  | .branch g y n => .branch (expr g) (expr y) (expr n)
  | .pair x y => .pair (expr x) (expr y)
  | .fst x => .fst (expr x)
  | .snd x => .snd (expr x)
  | .emptyRecord => .emptyRecord
  | .record label value rest => .record label (expr value) (expr rest)
  | .field label value => .field label (expr value)
  | .variant label value => .variant label (expr value)

@[simp] theorem isValue_expr (e : Inference.Expr) :
    (expr (Op := Op) (Key := Key) (Scope := Scope) e).isValue = e.isValue := by
  induction e <;> simp [expr, Expr.isValue, Inference.Expr.isValue, *]

def formula : Inference.Formula α → Formula Key Scope α
  | .top => .top
  | .bot => .bot
  | .and p q => .and (formula p) (formula q)
  | .or p q => .or (formula p) (formula q)
  | .tyLe a b => .tyLe a b
  | .rowLe a b => .rowLe a b
  | .existsSlot p => .existsSlot (formula p)

@[simp] theorem formula_rename (p : Inference.Formula α) (f : α → β) :
    formula (Key := Key) (Scope := Scope) (p.rename f) = (formula p).rename f := by
  induction p generalizing β <;> simp [formula, Inference.Formula.rename, Formula.rename, *]

@[simp] theorem liftSubst_agrees (f : α → CompTerm β) :
    Inference.liftSubst f = liftSubst f := rfl

@[simp] theorem formula_subst (p : Inference.Formula α) (f : α → CompTerm β) :
    formula (Key := Key) (Scope := Scope) (p.subst f) = (formula p).subst f := by
  induction p generalizing β <;>
    simp [formula, Inference.Formula.subst, Formula.subst, *]

@[simp] theorem holds_formula (m : Model) {algebra : RowAlgebra Key Scope}
    (view : RowView m algebra) (p : Inference.Formula α) (ρ : α → Comp m) :
    (formula p).Holds m view ρ ↔ p.Holds m ρ := by
  induction p <;> simp [formula, Formula.Holds, Inference.Formula.Holds, *]

def context (Γ : Inference.SchemeEnv α) : SchemeEnv Key Scope α := Γ.map formula

@[simp] theorem context_nil : context (Key := Key) (Scope := Scope) ([] : Inference.SchemeEnv α) = [] := rfl

@[simp] theorem context_cons (s : Inference.Scheme α) (Γ : Inference.SchemeEnv α) :
    formula s :: context (Key := Key) (Scope := Scope) Γ = context (s :: Γ) := rfl

@[simp] theorem context_lift (Γ : Inference.SchemeEnv α) :
    (context (Key := Key) (Scope := Scope) Γ).lift = context Γ.lift := by
  simp [context, SchemeEnv.lift, Inference.SchemeEnv.lift, List.map_map, Function.comp_def]

@[simp] theorem mono_formula (a : CompTerm α) :
    Scheme.mono (Key := Key) (Scope := Scope) a = formula (Inference.Scheme.mono a) := rfl

@[simp] theorem instantiate_formula (s : Inference.Scheme α) (a : CompTerm α) :
    Scheme.instantiate (formula (Key := Key) (Scope := Scope) s) a = formula (s.instantiate a) := by
  exact (formula_subst s (fun | none => a | some x => CompTerm.var x)).symm

@[simp] theorem lookup_formula (Γ : Inference.SchemeEnv α) (n : Nat) (a : CompTerm α) :
    Scheme.lookup (context (Key := Key) (Scope := Scope) Γ) n a =
      formula (Inference.Scheme.lookup Γ n a) := by
  simp only [Scheme.lookup, Inference.Scheme.lookup, context, List.getElem?_map]
  cases Γ[n]? <;> simp [formula]

/-- Every core expression generates precisely its old formula embedded in the
extended constraint language. The operation environment is arbitrary. -/
theorem generate_preserved (e : Inference.Expr) (sigs : Signatures Op Key α)
    (Γ : Inference.SchemeEnv α) (out : CompTerm α) :
    generate (Scope := Scope) sigs (context Γ) (expr e) out = formula (Inference.generate Γ e out) := by
  induction e generalizing α sigs Γ out
  case letE v body ihv ihb =>
    have hcontext (p : Inference.Formula (Option α)) :
        Formula.and (formula p) (.rowLe .empty (.var none)) :: context (Key := Key) (Scope := Scope) Γ =
          context (Inference.Formula.and p (.rowLe .empty (.var none)) :: Γ) := rfl
    cases hv : v.isValue <;>
      simp [expr, generate, Inference.generate, formula, env₂,
        Inference.env₂, ihv, ihb, hv, hcontext,
        Formula.compLe, Inference.Formula.compLe]
  all_goals
    simp [expr, generate, Inference.generate, formula, env₂, env₃,
      Inference.env₂, Inference.env₃, *, Formula.compLe, Inference.Formula.compLe]

/-- The original principal scheme is unchanged, including its result binder. -/
theorem principal_preserved (e : Inference.Expr) (sigs : Signatures Op Key α)
    (Γ : Inference.SchemeEnv α) :
    principal (Scope := Scope) sigs (context Γ) (expr e) = formula (Inference.principal Γ e) := by
  simp [principal, Inference.principal, generate_preserved]

theorem generated_models_preserved (m : Model) {algebra : RowAlgebra Key Scope}
    (view : RowView m algebra) (e : Inference.Expr) (sigs : Signatures Op Key α)
    (Γ : Inference.SchemeEnv α) (out : CompTerm α) (ρ : α → Comp m) :
    (generate (Scope := Scope) sigs (context Γ) (expr e) out).Holds m view ρ ↔
      (Inference.generate Γ e out).Holds m ρ := by
  rw [generate_preserved, holds_formula]

theorem principal_models_preserved (m : Model) {algebra : RowAlgebra Key Scope}
    (view : RowView m algebra) (e : Inference.Expr) (sigs : Signatures Op Key α)
    (Γ : Inference.SchemeEnv α) (ρ : α → Comp m) (c : Comp m) :
    (principal (Scope := Scope) sigs (context Γ) (expr e)).Holds m view (Inference.extend ρ c) ↔
      (Inference.principal Γ e).Holds m (Inference.extend ρ c) := by
  rw [principal_preserved, holds_formula]

/-- The extended generator recovers the original independent type judgement on
all core programs, not only an equivalent implementation-specific checker. -/
theorem generated_core_exact (m : Model) {algebra : RowAlgebra Key Scope}
    (view : RowView m algebra) (e : Inference.Expr) (sigs : Signatures Op Key α)
    (sΓ : Inference.SchemeEnv α) (Γ : List (Inference.Binding m))
    (ρ : α → Comp m) (out : CompTerm α) (related : Inference.EnvRel m ρ sΓ Γ) :
    (generate sigs (context sΓ) (expr e) out).Holds m view ρ ↔
      Inference.Typing m Γ e (out.eval m ρ) :=
  (generated_models_preserved m view e sigs sΓ out ρ).trans
    (Inference.generate_models_iff_typing m e sΓ Γ ρ out related)

theorem principal_core_exact (m : Model) {algebra : RowAlgebra Key Scope}
    (view : RowView m algebra) (e : Inference.Expr) (sigs : Signatures Op Key α)
    (sΓ : Inference.SchemeEnv α) (Γ : List (Inference.Binding m))
    (ρ : α → Comp m) (related : Inference.EnvRel m ρ sΓ Γ) (c : Comp m) :
    (principal sigs (context sΓ) (expr e)).Holds m view (Inference.extend ρ c) ↔
      Inference.Typing m Γ e c :=
  (principal_models_preserved m view e sigs sΓ ρ c).trans
    (Inference.principal_exact m e sΓ Γ ρ related c)

end Yulang.RecursiveEffects.Conservativity
