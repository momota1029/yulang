import Yulang.QualifiedGeneralization
import Yulang.RowInference

/-!
# Operation-local role evidence at calls and shallow handlers

Calls instantiate the operation's value-type locals and discharge every role
premise. Handler arms are checked for all local types under precisely the
signature's dictionaries. Their result and outer environment are fixed before
this quantifier. These remain type-only operation parameters; ordinary qualified
let uses the separate type-and-row binders of `QualifiedGeneralization`.

This is a resolved rule layer using the qualified expression generator. It does
not claim source name selection, whole-AST effect elaboration or runtime safety.
-/

namespace Yulang.RoleEvidence

open Inference (Model Comp CompTerm TyTerm RowTerm extend extend_comp_some extend_none extend_some exists_comp_row)
open RoleConstraints
open QualifiedInference
open EffectInference (SigKey localEnv localEnv_comp_inl localEnv_map)
open RowInference (RowAlgebra RowView fromCoreRow heads keysRow rowEnv)

structure Signature (α : Type) (n : Nat) (F O A : Type) where
  operation : EffectInference.PolySignature α n F O A
  requirements : List (Goal (α ⊕ Fin n))

inductive Constraint (Key Scope : Type) : Type → Type 1 where
  | core : QualifiedInference.Formula α → Constraint Key Scope α
  | rowLe : RowInference.RowExpr Key Scope α → RowInference.RowExpr Key Scope α → Constraint Key Scope α
  | and : Constraint Key Scope α → Constraint Key Scope α → Constraint Key Scope α
  | existsSlot : Constraint Key Scope (Option α) → Constraint Key Scope α
  | existsTypes : (n : Nat) → Constraint Key Scope (α ⊕ Fin n) → Constraint Key Scope α
  | forallTypes : (n : Nat) → Constraint Key Scope (α ⊕ Fin n) → Constraint Key Scope α
  | given : List (Goal α) → Constraint Key Scope α → Constraint Key Scope α

def Constraint.Holds {Key Scope : Type} {m : Model} {algebra : RowAlgebra Key Scope}
    (view : RowView m algebra) (theory : Theory m) :
    {α : Type} → (α → Comp m) → Constraint Key Scope α → Prop
  | _, ρ, .core p => p.Holds m theory ρ
  | _, ρ, .rowLe a b => algebra.le
      (a.eval algebra (rowEnv view ρ)) (b.eval algebra (rowEnv view ρ))
  | _, ρ, .and p q => p.Holds view theory ρ ∧ q.Holds view theory ρ
  | _, ρ, .existsSlot p => ∃ c, p.Holds view theory (extend ρ c)
  | _, ρ, .existsTypes n p => ∃ ι : Fin n → m.Ty, p.Holds view theory (localEnv m ρ ι)
  | _, ρ, .forallTypes n p => ∀ ι : Fin n → m.Ty, p.Holds view theory (localEnv m ρ ι)
  | _, ρ, .given goals p => p.Holds view (WithEvidence theory (goals.map (Goal.eval m ρ))) ρ

def monoRequestConstraints (methods : MethodTable) (Γ : SchemeEnv α)
    (sig : EffectInference.Signature α F O A) (payload : QualifiedInference.Expr) (out : CompTerm α) :
    Constraint (SigKey F O A) Scope α :=
  .existsSlot (
    .and (.core (generate methods Γ.lift payload ⟨sig.input.rename some, .var none⟩))
      (.and (.core (.tyLe (sig.output.rename some) (out.ty.rename some)))
        (.rowLe (.union (.var none) (.union (.head sig.key) (heads sig.extra)))
          (fromCoreRow (out.row.rename some)))))

inductive RequestTyping (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (methods : MethodTable) (theory : Theory m) (Γ : List (QualifiedInference.Binding m))
    (key : SigKey F O A) (extra : List (SigKey F O A)) (input output : m.Ty)
    (payload : QualifiedInference.Expr) (out : Comp m) : Prop where
  | intro : QualifiedInference.Typing m methods theory Γ payload (input, er) → m.subTy output out.1 →
      algebra.le (algebra.join (view.decode er) (algebra.join (algebra.head key) (keysRow algebra extra)))
        (view.decode out.2) → RequestTyping algebra view methods theory Γ key extra input output payload out

@[simp] theorem requestTyping_iff (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (methods : MethodTable) (theory : Theory m) (Γ : List (QualifiedInference.Binding m))
    (key : SigKey F O A) (extra : List (SigKey F O A)) (input output : m.Ty)
    (payload : QualifiedInference.Expr) (out : Comp m) :
    RequestTyping algebra view methods theory Γ key extra input output payload out ↔ ∃ er,
      QualifiedInference.Typing m methods theory Γ payload (input, er) ∧ m.subTy output out.1 ∧
      algebra.le (algebra.join (view.decode er) (algebra.join (algebra.head key) (keysRow algebra extra)))
        (view.decode out.2) := by
  constructor
  · intro h; cases h with | intro hp ht he => exact ⟨_, hp, ht, he⟩
  · rintro ⟨_, hp, ht, he⟩; exact .intro hp ht he

theorem mono_request_exact (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (methods : MethodTable) (theory : Theory m) (sΓ : SchemeEnv α) (Γ : List (QualifiedInference.Binding m))
    (ρ : α → Comp m) (henv : QualifiedInference.EnvRel m theory ρ sΓ Γ)
    (sig : EffectInference.Signature α F O A) (payload : QualifiedInference.Expr) (out : CompTerm α) :
    (monoRequestConstraints methods sΓ sig payload out).Holds view theory ρ ↔
      RequestTyping algebra view methods theory Γ sig.key sig.extra
        (sig.input.eval m ρ) (sig.output.eval m ρ) payload (out.eval m ρ) := by
  have hp (c : Comp m) :
      (generate methods sΓ.lift payload ⟨sig.input.rename some, .var none⟩).Holds m theory (extend ρ c) ↔
      QualifiedInference.Typing m methods theory Γ payload (sig.input.eval m ρ, c.2) := by
    simpa [CompTerm.eval, TyTerm.eval, RowTerm.eval] using
      QualifiedInference.generate_models_iff_typing m methods theory payload sΓ.lift Γ (extend ρ c)
        ⟨sig.input.rename some, .var none⟩ (henv.lift c)
  simp only [monoRequestConstraints, Constraint.Holds, requestTyping_iff, hp,
    QualifiedInference.Formula.Holds, TyTerm.eval_rename, extend_comp_some,
    RowInference.RowExpr.eval, RowInference.eval_heads, RowInference.eval_fromCoreRow, RowTerm.eval_rename]
  simp only [rowEnv, extend_none, CompTerm.eval]
  exact exists_comp_row m (fun er =>
    QualifiedInference.Typing m methods theory Γ payload (sig.input.eval m ρ, er) ∧
    m.subTy (sig.output.eval m ρ) (out.ty.eval m ρ) ∧
    algebra.le (algebra.join (view.decode er) (algebra.join (algebra.head sig.key) (keysRow algebra sig.extra)))
      (view.decode (out.row.eval m ρ)))

def requestConstraints (methods : MethodTable) (Γ : SchemeEnv α) (sig : Signature α n F O A)
    (payload : QualifiedInference.Expr) (out : CompTerm α) : Constraint (SigKey F O A) Scope α :=
  .existsTypes n (.and (.core (QualifiedInference.Formula.roles sig.requirements))
    (monoRequestConstraints methods (Γ.rename Sum.inl) sig.operation.mono payload (out.rename Sum.inl)))

inductive PolyRequestTyping (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (methods : MethodTable) (theory : Theory m) (Γ : List (QualifiedInference.Binding m))
    (key : SigKey F O A) (extra : List (SigKey F O A))
    (requirements : (Fin n → m.Ty) → List (Predicate m.Ty)) (input output : (Fin n → m.Ty) → m.Ty)
    (payload : QualifiedInference.Expr) (out : Comp m) : Prop where
  | intro (ι : Fin n → m.Ty) : Satisfies theory (requirements ι) →
      RequestTyping algebra view methods theory Γ key extra (input ι) (output ι) payload out →
      PolyRequestTyping algebra view methods theory Γ key extra requirements input output payload out

theorem request_constraints_exact (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (methods : MethodTable) (theory : Theory m) (sΓ : SchemeEnv α) (Γ : List (QualifiedInference.Binding m))
    (ρ : α → Comp m) (henv : QualifiedInference.EnvRel m theory ρ sΓ Γ)
    (sig : Signature α n F O A) (payload : QualifiedInference.Expr) (out : CompTerm α) :
    (requestConstraints methods sΓ sig payload out).Holds view theory ρ ↔
      PolyRequestTyping algebra view methods theory Γ sig.operation.key sig.operation.extra
        (fun ι => sig.requirements.map (Goal.eval m (localEnv m ρ ι)))
        (fun ι => sig.operation.input.eval m (localEnv m ρ ι))
        (fun ι => sig.operation.output.eval m (localEnv m ρ ι)) payload (out.eval m ρ) := by
  simp only [requestConstraints, Constraint.Holds, QualifiedInference.Formula.holds_roles]
  constructor
  · rintro ⟨ι, hr, hp⟩
    apply PolyRequestTyping.intro ι hr
    simpa [EffectInference.PolySignature.mono] using
      (mono_request_exact algebra view methods theory _ Γ _ (henv.rename Sum.inl _ rfl)
        sig.operation.mono payload (out.rename Sum.inl)).mp hp
  · intro h
    cases h with
    | intro ι hr hp =>
      refine ⟨ι, hr, (mono_request_exact algebra view methods theory _ Γ _
        (henv.rename Sum.inl _ rfl) sig.operation.mono payload (out.rename Sum.inl)).mpr ?_⟩
      simpa [EffectInference.PolySignature.mono] using hp

def armEnvironment (Γ : SchemeEnv α) (input : CompTerm α) (payload response : TyTerm α) : SchemeEnv α :=
  Scheme.mono (CompTerm.pure payload) ::
    Scheme.mono (CompTerm.pure (CompTerm.arrow (CompTerm.pure response) input)) :: Γ

def semanticArmEnvironment (m : Model) (Γ : List (QualifiedInference.Binding m))
    (input : Comp m) (payload response : m.Ty) : List (QualifiedInference.Binding m) :=
  .mono (Comp.pure m payload) :: .mono (Comp.pure m (Comp.arrow m (Comp.pure m response) input)) :: Γ

theorem armEnvironment_related (m : Model) (theory : Theory m) (ρ : α → Comp m)
    (sΓ : SchemeEnv α) (Γ : List (QualifiedInference.Binding m))
    (henv : QualifiedInference.EnvRel m theory ρ sΓ Γ)
    (input : CompTerm α) (payload response : TyTerm α) :
    QualifiedInference.EnvRel m theory ρ (armEnvironment sΓ input payload response)
      (semanticArmEnvironment m Γ (input.eval m ρ) (payload.eval m ρ) (response.eval m ρ)) := by
  simpa [armEnvironment, semanticArmEnvironment, CompTerm.eval, CompTerm.pure,
    CompTerm.arrow, TyTerm.eval, RowTerm.eval, Comp.pure, Comp.arrow] using
    (henv.mono (CompTerm.pure (CompTerm.arrow (CompTerm.pure response) input))).mono (CompTerm.pure payload)

def operationArmConstraints (methods : MethodTable) (Γ : SchemeEnv α)
    (sig : EffectInference.Signature α F O A) (input returned out : CompTerm α)
    (onOperation : QualifiedInference.Expr) : Constraint (SigKey F O A) Scope α :=
  .existsSlot (
    .and (.core (generate methods (armEnvironment Γ.lift (input.rename some)
      (sig.input.rename some) (sig.output.rename some)) onOperation (CompTerm.var none)))
      (.and (.core (.tyLe (.union (returned.ty.rename some) (.var none)) (out.ty.rename some)))
        (.rowLe (.union (.residual [sig.key] (fromCoreRow (input.row.rename some)))
          (.union (fromCoreRow (returned.row.rename some)) (.var none)))
          (fromCoreRow (out.row.rename some)))))

theorem operation_arm_exact (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (methods : MethodTable) (theory : Theory m) (sΓ : SchemeEnv α) (Γ : List (QualifiedInference.Binding m))
    (ρ : α → Comp m) (henv : QualifiedInference.EnvRel m theory ρ sΓ Γ)
    (sig : EffectInference.Signature α F O A) (input returned out : CompTerm α)
    (onOperation : QualifiedInference.Expr) :
    (operationArmConstraints methods sΓ sig input returned out onOperation).Holds view theory ρ ↔
      ∃ operated, QualifiedInference.Typing m methods theory
        (semanticArmEnvironment m Γ (input.eval m ρ) (sig.input.eval m ρ) (sig.output.eval m ρ))
        onOperation operated ∧
      m.subTy (m.union (returned.eval m ρ).1 operated.1) (out.eval m ρ).1 ∧
      algebra.le (algebra.join (algebra.residual [sig.key] (view.decode (input.eval m ρ).2))
        (algebra.join (view.decode (returned.eval m ρ).2) (view.decode operated.2)))
        (view.decode (out.eval m ρ).2) := by
  have ho (operated : Comp m) :
      (generate methods (armEnvironment sΓ.lift (input.rename some) (sig.input.rename some)
        (sig.output.rename some)) onOperation (CompTerm.var none)).Holds m theory (extend ρ operated) ↔
      QualifiedInference.Typing m methods theory
        (semanticArmEnvironment m Γ (input.eval m ρ) (sig.input.eval m ρ) (sig.output.eval m ρ))
        onOperation operated := by
    simpa using QualifiedInference.generate_models_iff_typing m methods theory onOperation _ _
      (extend ρ operated) (CompTerm.var none)
      (armEnvironment_related m theory (extend ρ operated) sΓ.lift Γ (henv.lift operated)
        (input.rename some) (sig.input.rename some) (sig.output.rename some))
  simp only [operationArmConstraints, Constraint.Holds]
  apply exists_congr; intro operated
  rw [ho]
  simp [QualifiedInference.Formula.Holds, RowInference.RowExpr.eval, rowEnv, CompTerm.eval, TyTerm.eval]

def handlerConstraints (methods : MethodTable) (Γ : SchemeEnv α) (sig : Signature α n F O A)
    (action onReturn onOperation : QualifiedInference.Expr) (out : CompTerm α) :
    Constraint (SigKey F O A) Scope α :=
  .existsSlot (.existsSlot (
    .and (.core (generate methods (env₂ Γ) action fresh₀))
      (.and (.core (generate methods (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ Γ) onReturn fresh₁))
        (.forallTypes n (.given
          (sig.requirements.map (Goal.rename (Sum.map (fun x => some (some x)) id)))
          (operationArmConstraints methods ((env₂ Γ).rename Sum.inl)
            (sig.operation.rename (fun x => some (some x))).mono
            (fresh₀.rename Sum.inl) (fresh₁.rename Sum.inl) ((lift₂ out).rename Sum.inl) onOperation))))))

inductive HandlerTyping (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (methods : MethodTable) (theory : Theory m) (Γ : List (QualifiedInference.Binding m))
    (key : SigKey F O A) (requirements : (Fin n → m.Ty) → List (Predicate m.Ty))
    (payload response : (Fin n → m.Ty) → m.Ty)
    (action onReturn onOperation : QualifiedInference.Expr) (out : Comp m) : Prop where
  | intro : QualifiedInference.Typing m methods theory Γ action input →
      QualifiedInference.Typing m methods theory (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
      (∀ ι, ∃ operated, QualifiedInference.Typing m methods (WithEvidence theory (requirements ι))
        (semanticArmEnvironment m Γ input (payload ι) (response ι)) onOperation operated ∧
        m.subTy (m.union returned.1 operated.1) out.1 ∧
        algebra.le (algebra.join (algebra.residual [key] (view.decode input.2))
          (algebra.join (view.decode returned.2) (view.decode operated.2))) (view.decode out.2)) →
      HandlerTyping algebra view methods theory Γ key requirements payload response action onReturn onOperation out

@[simp] theorem handlerTyping_iff (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (methods : MethodTable) (theory : Theory m) (Γ : List (QualifiedInference.Binding m))
    (key : SigKey F O A) (requirements : (Fin n → m.Ty) → List (Predicate m.Ty))
    (payload response : (Fin n → m.Ty) → m.Ty)
    (action onReturn onOperation : QualifiedInference.Expr) (out : Comp m) :
    HandlerTyping algebra view methods theory Γ key requirements payload response action onReturn onOperation out ↔
      ∃ input returned, QualifiedInference.Typing m methods theory Γ action input ∧
        QualifiedInference.Typing m methods theory (.mono (Comp.pure m input.1) :: Γ) onReturn returned ∧
      ∀ ι, ∃ operated, QualifiedInference.Typing m methods (WithEvidence theory (requirements ι))
        (semanticArmEnvironment m Γ input (payload ι) (response ι)) onOperation operated ∧
        m.subTy (m.union returned.1 operated.1) out.1 ∧
        algebra.le (algebra.join (algebra.residual [key] (view.decode input.2))
          (algebra.join (view.decode returned.2) (view.decode operated.2))) (view.decode out.2) := by
  constructor
  · intro h; cases h with | intro hi hr ho => exact ⟨_, _, hi, hr, ho⟩
  · rintro ⟨_, _, hi, hr, ho⟩; exact .intro hi hr ho

/-- The operation-local forall remains outside the operation-arm witness; the
input/return types and the final result are fixed before it. -/
theorem handler_constraints_exact (algebra : RowAlgebra (SigKey F O A) Scope) (view : RowView m algebra)
    (methods : MethodTable) (theory : Theory m) (sΓ : SchemeEnv α) (Γ : List (QualifiedInference.Binding m))
    (ρ : α → Comp m) (henv : ∀ evidence, QualifiedInference.EnvRel m evidence ρ sΓ Γ)
    (sig : Signature α n F O A) (action onReturn onOperation : QualifiedInference.Expr) (out : CompTerm α) :
    (handlerConstraints methods sΓ sig action onReturn onOperation out).Holds view theory ρ ↔
      HandlerTyping algebra view methods theory Γ sig.operation.key
        (fun ι => sig.requirements.map (Goal.eval m (localEnv m ρ ι)))
        (fun ι => sig.operation.input.eval m (localEnv m ρ ι))
        (fun ι => sig.operation.output.eval m (localEnv m ρ ι)) action onReturn onOperation (out.eval m ρ) := by
  have hi (input returned : Comp m) :
      (generate methods (env₂ sΓ) action fresh₀).Holds m theory (extend (extend ρ input) returned) ↔
      QualifiedInference.Typing m methods theory Γ action input := by
    simpa [env₂, fresh₀] using QualifiedInference.generate_models_iff_typing m methods theory action _ Γ
      (extend (extend ρ input) returned) fresh₀ (((henv theory).lift input).lift returned)
  have hr (input returned : Comp m) :
      (generate methods (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) onReturn fresh₁).Holds m theory
        (extend (extend ρ input) returned) ↔
      QualifiedInference.Typing m methods theory (.mono (Comp.pure m input.1) :: Γ) onReturn returned := by
    simpa [env₂, fresh₀, fresh₁, CompTerm.var, CompTerm.pure, CompTerm.eval,
      TyTerm.eval, RowTerm.eval, Comp.pure] using
      QualifiedInference.generate_models_iff_typing m methods theory onReturn _ _
        (extend (extend ρ input) returned) fresh₁
        ((((henv theory).lift input).lift returned).mono (CompTerm.pure fresh₀.ty))
  simp only [handlerConstraints, Constraint.Holds, handlerTyping_iff]
  apply exists_congr; intro input
  apply exists_congr; intro returned
  rw [hi, hr]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'; intro ι
  have he : extend (extend ρ input) returned ∘ (fun x => some (some x)) = ρ := rfl
  have hgoals :
      (sig.requirements.map (Goal.rename (Sum.map (fun x => some (some x)) id))).map
        (Goal.eval m (localEnv m (extend (extend ρ input) returned) ι)) =
      sig.requirements.map (Goal.eval m (localEnv m ρ ι)) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro goal _
    change (goal.rename _).eval m _ = _
    rw [Goal.eval_rename, localEnv_map, he]
  rw [hgoals]
  have ha := operation_arm_exact algebra view methods
    (WithEvidence theory (sig.requirements.map (Goal.eval m (localEnv m ρ ι))))
    ((env₂ sΓ).rename Sum.inl) Γ (localEnv m (extend (extend ρ input) returned) ι)
    ((((henv _).lift input).lift returned).rename Sum.inl _ rfl)
    (sig.operation.rename (fun x => some (some x))).mono
    (fresh₀.rename Sum.inl) (fresh₁.rename Sum.inl) ((lift₂ out).rename Sum.inl) onOperation
  simpa only [EffectInference.PolySignature.mono, EffectInference.PolySignature.rename,
    CompTerm.eval_rename,
    TyTerm.eval_rename, localEnv_comp_inl, localEnv_map, he,
    fresh₀, fresh₁, lift₂, CompTerm.eval_var, extend_some, extend_none] using ha

end Yulang.RoleEvidence
