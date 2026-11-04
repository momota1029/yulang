import Yulang.EffectInference
import Yulang.Directed

/-!
# One constraint generator for positive and signed occurrence rows

The first-order generators and exactness proofs below are shared by both row
algebras. Signed release uses the same scope and permission mask as protection;
it therefore retains negative debt. The model interface for value types stays
unchanged. Source elaboration, origin-invariant preservation and operation-local
polymorphism are not asserted here.
-/

namespace Yulang.RowInference

open Inference
open EffectInference (Signature SigKey armEnvironment semanticArmEnvironment armEnvironment_related)

structure RowAlgebra (Key Scope : Type) where
  Row : Type
  empty : Row
  join : Row → Row → Row
  head : Key → Row
  protect : Scope → (Key → Bool) → Row → Row
  release : Scope → (Key → Bool) → Row → Row
  residual : List Key → Row → Row
  le : Row → Row → Prop

structure RowView (m : Model) (algebra : RowAlgebra Key Scope) where
  decode : m.Row → algebra.Row
  decode_empty : decode m.empty = algebra.empty
  decode_join : ∀ a b, decode (m.join a b) = algebra.join (decode a) (decode b)
  subtype_iff : ∀ a b, m.subRow a b ↔ algebra.le (decode a) (decode b)

inductive RowExpr (Key Scope α : Type) where
  | empty
  | head : Key → RowExpr Key Scope α
  | var : α → RowExpr Key Scope α
  | union : RowExpr Key Scope α → RowExpr Key Scope α → RowExpr Key Scope α
  | protect : Scope → (Key → Bool) → RowExpr Key Scope α → RowExpr Key Scope α
  | release : Scope → (Key → Bool) → RowExpr Key Scope α → RowExpr Key Scope α
  | residual : List Key → RowExpr Key Scope α → RowExpr Key Scope α

def RowExpr.eval (algebra : RowAlgebra Key Scope) (ρ : α → algebra.Row) :
    RowExpr Key Scope α → algebra.Row
  | .empty => algebra.empty
  | .head key => algebra.head key
  | .var x => ρ x
  | .union a b => algebra.join (a.eval algebra ρ) (b.eval algebra ρ)
  | .protect scope mask a => algebra.protect scope mask (a.eval algebra ρ)
  | .release scope mask a => algebra.release scope mask (a.eval algebra ρ)
  | .residual keys a => algebra.residual keys (a.eval algebra ρ)

def RowExpr.subst (σ : α → RowExpr Key Scope β) : RowExpr Key Scope α → RowExpr Key Scope β
  | .empty => .empty
  | .head key => .head key
  | .var x => σ x
  | .union a b => .union (a.subst σ) (b.subst σ)
  | .protect scope mask a => .protect scope mask (a.subst σ)
  | .release scope mask a => .release scope mask (a.subst σ)
  | .residual keys a => .residual keys (a.subst σ)

theorem RowExpr.eval_subst (algebra : RowAlgebra Key Scope) (ρ : β → algebra.Row)
    (σ : α → RowExpr Key Scope β) (r : RowExpr Key Scope α) :
    (r.subst σ).eval algebra ρ = r.eval algebra (fun x => (σ x).eval algebra ρ) := by
  induction r <;> simp_all [subst, eval]

def heads (keys : List Key) : RowExpr Key Scope α :=
  keys.foldr (fun key rest => .union (.head key) rest) .empty

def keysRow (algebra : RowAlgebra Key Scope) (keys : List Key) : algebra.Row :=
  keys.foldr (fun key rest => algebra.join (algebra.head key) rest) algebra.empty

@[simp] theorem eval_heads (algebra : RowAlgebra Key Scope) (ρ : α → algebra.Row) (keys : List Key) :
    (heads keys).eval algebra ρ = keysRow algebra keys := by
  induction keys <;> simp_all [heads, keysRow, RowExpr.eval]

def fromCoreRow : RowTerm α → RowExpr Key Scope α
  | .var x => .var x
  | .empty => .empty
  | .join a b => .union (fromCoreRow a) (fromCoreRow b)

def rowEnv (view : RowView m algebra) (ρ : α → Comp m) : α → algebra.Row :=
  fun x => view.decode (ρ x).2

@[simp] theorem eval_fromCoreRow (view : RowView m algebra) (ρ : α → Comp m) (r : RowTerm α) :
    (fromCoreRow r).eval algebra (rowEnv view ρ) = view.decode (r.eval m ρ) := by
  induction r <;> simp_all [fromCoreRow, RowExpr.eval, RowTerm.eval, rowEnv,
    view.decode_empty, view.decode_join]

inductive Constraint (Key Scope : Type) : Type → Type 1 where
  | core : Formula α → Constraint Key Scope α
  | rowLe : RowExpr Key Scope α → RowExpr Key Scope α → Constraint Key Scope α
  | and : Constraint Key Scope α → Constraint Key Scope α → Constraint Key Scope α
  | existsSlot : Constraint Key Scope (Option α) → Constraint Key Scope α

def Constraint.Holds {Key Scope : Type} {m : Model} {algebra : RowAlgebra Key Scope}
    (view : RowView m algebra) :
    {α : Type} → (α → Comp m) → Constraint Key Scope α → Prop
  | _, ρ, .core p => p.Holds m ρ
  | _, ρ, .rowLe a b => algebra.le
      (a.eval algebra (rowEnv view ρ)) (b.eval algebra (rowEnv view ρ))
  | _, ρ, .and p q => p.Holds view ρ ∧ q.Holds view ρ
  | _, ρ, .existsSlot p => ∃ c, p.Holds view (extend ρ c)

def requestConstraints (Γ : SchemeEnv α) (sig : Signature α F O A)
    (payload : Expr) (out : CompTerm α) : Constraint (SigKey F O A) Scope α :=
  .existsSlot (
    .and (.core (generate Γ.lift payload ⟨sig.input.rename some, .var none⟩))
      (.and (.core (.tyLe (sig.output.rename some) (out.ty.rename some)))
        (.rowLe (.union (.var none) (.union (.head sig.key) (heads sig.extra)))
          (fromCoreRow (out.row.rename some)))))

inductive RequestTyping (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (Γ : List (Binding m)) (key : SigKey F O A) (extra : List (SigKey F O A))
    (input output : m.Ty) (payload : Expr) (out : Comp m) : Prop where
  | intro : Typing m Γ payload (input, er) → m.subTy output out.1 →
      algebra.le (algebra.join (view.decode er) (algebra.join (algebra.head key) (keysRow algebra extra)))
        (view.decode out.2) → RequestTyping algebra view Γ key extra input output payload out

inductive Boundary (Key Scope : Type) where
  | protect : Scope → (Key → Bool) → Boundary Key Scope
  | release : Scope → (Key → Bool) → Boundary Key Scope

def Boundary.row (algebra : RowAlgebra Key Scope) (boundary : Boundary Key Scope) (row : algebra.Row) :
    algebra.Row :=
  match boundary with
  | .protect scope mask => algebra.protect scope mask row
  | .release scope mask => algebra.release scope mask row

def Boundary.term (boundary : Boundary Key Scope) (row : RowExpr Key Scope α) : RowExpr Key Scope α :=
  match boundary with
  | .protect scope mask => .protect scope mask row
  | .release scope mask => .release scope mask row

@[simp] theorem Boundary.eval_term (algebra : RowAlgebra Key Scope) (boundary : Boundary Key Scope)
    (ρ : α → algebra.Row) (row : RowExpr Key Scope α) :
    (boundary.term row).eval algebra ρ = boundary.row algebra (row.eval algebra ρ) := by
  cases boundary <;> rfl

def boundaryConstraints (Γ : SchemeEnv α) (boundary : Boundary Key Scope)
    (body : Expr) (out : CompTerm α) : Constraint Key Scope α :=
  .existsSlot (
    .and (.core (generate Γ.lift body (CompTerm.var none)))
      (.and (.core (.tyLe (.var none) (out.ty.rename some)))
        (.rowLe (boundary.term (.var none)) (fromCoreRow (out.row.rename some)))))

inductive BoundaryTyping (algebra : RowAlgebra Key Scope) (view : RowView m algebra)
    (boundary : Boundary Key Scope) (Γ : List (Binding m)) (body : Expr) (out : Comp m) : Prop where
  | intro : Typing m Γ body input → m.subTy input.1 out.1 →
      algebra.le (boundary.row algebra (view.decode input.2)) (view.decode out.2) →
      BoundaryTyping algebra view boundary Γ body out

def handlerConstraints (Γ : SchemeEnv α) (sig : Signature α F O A)
    (action onReturn onOperation : Expr) (out : CompTerm α) : Constraint (SigKey F O A) Scope α :=
  .existsSlot (.existsSlot (.existsSlot (
    .and (.core (generate (env₃ Γ) action fresh₀₃))
      (.and (.core (generate (Scheme.mono (CompTerm.pure fresh₀₃.ty) :: env₃ Γ) onReturn fresh₁₃))
        (.and (.core (generate
            (armEnvironment (env₃ Γ) fresh₀₃
              (sig.input.rename (fun x => some (some (some x))))
              (sig.output.rename (fun x => some (some (some x))))) onOperation fresh₂₃))
          (.and (.core (.tyLe (.union fresh₁₃.ty fresh₂₃.ty) (lift₃ out).ty))
            (.rowLe (.union (.residual [sig.key] (.var (some (some none))))
                (.union (.var (some none)) (.var none))) (fromCoreRow (lift₃ out).row))))))))

inductive HandlerTyping (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (Γ : List (Binding m)) (key : SigKey F O A) (payload response : m.Ty)
    (action onReturn onOperation : Expr) (out : Comp m) : Prop where
  | intro : Typing m Γ action input →
      Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
      Typing m (semanticArmEnvironment m Γ input payload response) onOperation operated →
      m.subTy (m.union returned.1 operated.1) out.1 →
      algebra.le (algebra.join (algebra.residual [key] (view.decode input.2))
        (algebra.join (view.decode returned.2) (view.decode operated.2))) (view.decode out.2) →
      HandlerTyping algebra view Γ key payload response action onReturn onOperation out

@[simp] theorem requestTyping_iff (algebra : RowAlgebra (SigKey F O A) Scope)
    (view : RowView m algebra) (Γ : List (Binding m)) (key : SigKey F O A) (extra : List (SigKey F O A))
    (input output : m.Ty) (payload : Expr) (out : Comp m) :
    RequestTyping algebra view Γ key extra input output payload out ↔ ∃ er,
      Typing m Γ payload (input, er) ∧ m.subTy output out.1 ∧
      algebra.le (algebra.join (view.decode er) (algebra.join (algebra.head key) (keysRow algebra extra)))
        (view.decode out.2) := by
  constructor
  · intro h; cases h with | intro hp ht he => exact ⟨_, hp, ht, he⟩
  · rintro ⟨er, hp, ht, he⟩; exact .intro hp ht he

theorem request_constraints_exact (algebra : RowAlgebra (SigKey F O A) Scope)
    (view : RowView m algebra) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (sig : Signature α F O A)
    (payload : Expr) (out : CompTerm α) :
    (requestConstraints sΓ sig payload out).Holds view ρ ↔
      RequestTyping algebra view Γ sig.key sig.extra (sig.input.eval m ρ) (sig.output.eval m ρ)
        payload (out.eval m ρ) := by
  have hp (c : Comp m) :
      (generate sΓ.lift payload ⟨sig.input.rename some, .var none⟩).Holds m (extend ρ c) ↔
      Typing m Γ payload (sig.input.eval m ρ, c.2) := by
    simpa [CompTerm.eval, TyTerm.eval, RowTerm.eval]
      using generate_models_iff_typing m payload sΓ.lift Γ (extend ρ c)
        ⟨sig.input.rename some, .var none⟩ (henv.lift c)
  simp only [requestConstraints, Constraint.Holds, requestTyping_iff]
  simp only [hp, Formula.Holds, TyTerm.eval_rename, extend_comp_some,
    RowExpr.eval, eval_heads, eval_fromCoreRow, RowTerm.eval_rename]
  simp only [rowEnv, extend_none, CompTerm.eval]
  exact exists_comp_row m (fun er => Typing m Γ payload (sig.input.eval m ρ, er) ∧
    m.subTy (sig.output.eval m ρ) (out.ty.eval m ρ) ∧
    algebra.le (algebra.join (view.decode er) (algebra.join (algebra.head sig.key) (keysRow algebra sig.extra)))
      (view.decode (out.row.eval m ρ)))

@[simp] theorem boundaryTyping_iff (algebra : RowAlgebra Key Scope) (view : RowView m algebra)
    (boundary : Boundary Key Scope) (Γ : List (Binding m)) (body : Expr) (out : Comp m) :
    BoundaryTyping algebra view boundary Γ body out ↔ ∃ input,
      Typing m Γ body input ∧ m.subTy input.1 out.1 ∧
      algebra.le (boundary.row algebra (view.decode input.2)) (view.decode out.2) := by
  constructor
  · intro h; cases h with | intro hb ht he => exact ⟨_, hb, ht, he⟩
  · rintro ⟨input, hb, ht, he⟩; exact .intro hb ht he

theorem boundary_constraints_exact (algebra : RowAlgebra Key Scope) (view : RowView m algebra)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m)
    (henv : EnvRel m ρ sΓ Γ) (boundary : Boundary Key Scope) (body : Expr) (out : CompTerm α) :
    (boundaryConstraints sΓ boundary body out).Holds view ρ ↔
      BoundaryTyping algebra view boundary Γ body (out.eval m ρ) := by
  have hb (input : Comp m) :
      (generate sΓ.lift body (CompTerm.var none)).Holds m (extend ρ input) ↔ Typing m Γ body input := by
    simpa using generate_models_iff_typing m body sΓ.lift Γ (extend ρ input)
      (CompTerm.var none) (henv.lift input)
  simp only [boundaryConstraints, Constraint.Holds, boundaryTyping_iff]
  apply exists_congr; intro input
  rw [hb]
  simp [Formula.Holds, TyTerm.eval, CompTerm.eval, Boundary.eval_term, RowExpr.eval, rowEnv]

@[simp] theorem handlerTyping_iff (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (Γ : List (Binding m)) (key : SigKey F O A) (payload response : m.Ty)
    (action onReturn onOperation : Expr) (out : Comp m) :
    HandlerTyping algebra view Γ key payload response action onReturn onOperation out ↔
      ∃ input returned operated, Typing m Γ action input ∧
      Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned ∧
      Typing m (semanticArmEnvironment m Γ input payload response) onOperation operated ∧
      m.subTy (m.union returned.1 operated.1) out.1 ∧
      algebra.le (algebra.join (algebra.residual [key] (view.decode input.2))
        (algebra.join (view.decode returned.2) (view.decode operated.2))) (view.decode out.2) := by
  constructor
  · intro h; cases h with | intro hi hr ho ht he => exact ⟨_, _, _, hi, hr, ho, ht, he⟩
  · rintro ⟨input, returned, operated, hi, hr, ho, ht, he⟩; exact .intro hi hr ho ht he

/-- The same closed proof applies to positive lists and signed rows. The
continuation carries `input`, not `residual input`, in both specializations. -/
theorem handler_constraints_exact (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ)
    (sig : Signature α F O A) (action onReturn onOperation : Expr) (out : CompTerm α) :
    (handlerConstraints sΓ sig action onReturn onOperation out).Holds view ρ ↔
      HandlerTyping algebra view Γ sig.key (sig.input.eval m ρ) (sig.output.eval m ρ)
        action onReturn onOperation (out.eval m ρ) := by
  have hi (input returned operated : Comp m) :
      (generate (env₃ sΓ) action fresh₀₃).Holds m (extend (extend (extend ρ input) returned) operated) ↔
      Typing m Γ action input := by
    simpa [env₃, fresh₀₃] using generate_models_iff_typing m action (env₃ sΓ) Γ
      (extend (extend (extend ρ input) returned) operated) fresh₀₃
      (((henv.lift input).lift returned).lift operated)
  have hr (input returned operated : Comp m) :
      (generate (Scheme.mono (CompTerm.pure fresh₀₃.ty) :: env₃ sΓ) onReturn fresh₁₃).Holds m
        (extend (extend (extend ρ input) returned) operated) ↔
      Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned := by
    simpa [env₃, fresh₀₃, fresh₁₃, CompTerm.var, CompTerm.pure, CompTerm.eval,
      TyTerm.eval, RowTerm.eval, Comp.pure] using generate_models_iff_typing m onReturn _ _
        (extend (extend (extend ρ input) returned) operated) fresh₁₃
        ((((henv.lift input).lift returned).lift operated).mono (CompTerm.pure fresh₀₃.ty))
  have ho (input returned operated : Comp m) :
      (generate (armEnvironment (env₃ sΓ) fresh₀₃
          (sig.input.rename (fun x => some (some (some x))))
          (sig.output.rename (fun x => some (some (some x))))) onOperation fresh₂₃).Holds m
        (extend (extend (extend ρ input) returned) operated) ↔
      Typing m (semanticArmEnvironment m Γ input (sig.input.eval m ρ) (sig.output.eval m ρ))
        onOperation operated := by
    have hrel := armEnvironment_related m (extend (extend (extend ρ input) returned) operated)
      (env₃ sΓ) Γ (((henv.lift input).lift returned).lift operated) fresh₀₃
      (sig.input.rename (fun x => some (some (some x)))) (sig.output.rename (fun x => some (some (some x))))
    simpa [env₃, fresh₀₃, fresh₂₃, Function.comp_def] using generate_models_iff_typing m onOperation _ _
      (extend (extend (extend ρ input) returned) operated) fresh₂₃ hrel
  simp only [handlerConstraints, Constraint.Holds, handlerTyping_iff]
  apply exists_congr; intro input
  apply exists_congr; intro returned
  apply exists_congr; intro operated
  rw [hi, hr, ho]
  simp [Formula.Holds, RowExpr.eval, rowEnv, CompTerm.eval, fresh₁₃, fresh₂₃,
    lift₃, CompTerm.rename, CompTerm.var, TyTerm.eval, Function.comp_def]

/-- The earlier positive-list experiment. Its release is intentionally erase;
no two-sided cancellation theorem is stated for this instance. -/
def positiveAlgebra (Key : Type) [DecidableEq Key] : RowAlgebra Key Nat where
  Row := Effects.Row Key
  empty := []
  join := List.append
  head := fun key => [{key := key}]
  protect := Effects.protect
  release := fun scope _ => Effects.release scope
  residual := Effects.residual
  le := Effects.RowSubset

/-- Signed rows retain unbounded integer balances on the finite scope interface. -/
def signedAlgebra (n : Nat) (Key : Type) [DecidableEq Key] : RowAlgebra Key (Fin n) where
  Row := Directed.Row n Key
  empty := []
  join := List.append
  head := fun key => [Directed.raw key]
  protect := fun scope mask row => row.map (Directed.protect scope mask)
  release := fun scope mask row => row.map (Directed.release scope mask)
  residual := Directed.residual
  le := fun a b => ∀ occurrence, occurrence ∈ a → occurrence ∈ b

theorem signed_eval_release_protect [DecidableEq Key] (scope : Fin n) (mask : Key → Bool)
    (ρ : α → Directed.Row n Key) (row : RowExpr Key (Fin n) α) :
    (RowExpr.release scope mask (.protect scope mask row)).eval (signedAlgebra n Key) ρ =
      row.eval (signedAlgebra n Key) ρ := by
  exact Directed.protect_row_release scope mask (row.eval (signedAlgebra n Key) ρ)

theorem signed_eval_protect_release [DecidableEq Key] (scope : Fin n) (mask : Key → Bool)
    (ρ : α → Directed.Row n Key) (row : RowExpr Key (Fin n) α) :
    (RowExpr.protect scope mask (.release scope mask row)).eval (signedAlgebra n Key) ρ =
      row.eval (signedAlgebra n Key) ρ := by
  exact Directed.release_row_protect scope mask (row.eval (signedAlgebra n Key) ρ)

/-- A release debt survives handler subtraction; its matching later guard may
cancel it, but subtraction alone never consumes it. -/
theorem signed_negative_debt_survives [DecidableEq Key] (scope : Fin n) (key : Key) :
    Directed.residual [key] [Directed.release scope Directed.allowNone (Directed.raw key)] =
      [Directed.release scope Directed.allowNone (Directed.raw key)] := by
  have blocked := Directed.negative_debt_not_capturable [key] scope Directed.allowNone
    (Directed.raw key) rfl rfl
  simp [Directed.residual, blocked]

end Yulang.RowInference
