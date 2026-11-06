import Yulang.CoreExpr
import Yulang.RecursiveEffects

/-! Independent recursive-effect rules on the shared syntax. The original
monomorphic signatures, signed row algebra and captured environments are kept.
No role/case/presence rules are silently added to this model. -/
namespace Yulang.Core.Effects
open Inference (Model Comp)
open RowInference (RowAlgebra RowView keysRow)
variable {Op Key Scope : Type} {algebra : RowAlgebra Key Scope}
abbrev Term (Op Key Scope : Type) := Core.Expr ⟨Op, Key, Scope, Empty, Empty⟩

def embed : RecursiveEffects.Expr Op Key Scope → Term Op Key Scope
  | .var a => .var a
  | .lit a => .lit a
  | .lam a => .lam (embed a)
  | .app a b => .app (embed a) (embed b)
  | .letE a b => .letE none (embed a) (embed b)
  | .branch a b c => .branch (embed a) (embed b) (embed c)
  | .pair a b => .pair (embed a) (embed b)
  | .fst a => .fst (embed a)
  | .snd a => .snd (embed a)
  | .emptyRecord => .emptyRecord
  | .record a b c => .record a (embed b) (embed c)
  | .recordDefault a b c => .recordDefault a (embed b) (embed c)
  | .field a b => .field a (embed b)
  | .variant a b => .variant a (embed b)
  | .request a b => .request a (embed b)
  | .boundary a b => .boundary a (embed b)
  | .handler a b c d => .handler a (embed b) (embed c) (embed d)

def decode : Term Op Key Scope → RecursiveEffects.Expr Op Key Scope
  | .var a => .var a
  | .lit a => .lit a
  | .lam a => .lam (decode a)
  | .app a b => .app (decode a) (decode b)
  | .letE _ a b => .letE (decode a) (decode b)
  | .branch a b c => .branch (decode a) (decode b) (decode c)
  | .pair a b => .pair (decode a) (decode b)
  | .fst a => .fst (decode a)
  | .snd a => .snd (decode a)
  | .emptyRecord => .emptyRecord
  | .record a b c => .record a (decode b) (decode c)
  | .recordDefault a b c => .recordDefault a (decode b) (decode c)
  | .field a b => .field a (decode b)
  | .variant a b => .variant a (decode b)
  | .request a b => .request a (decode b)
  | .boundary a b => .boundary a (decode b)
  | .handler a b c d => .handler a (decode b) (decode c) (decode d)
  | _ => .lit .unit

@[simp] theorem decode_embed (e : RecursiveEffects.Expr Op Key Scope) : decode (embed e) = e := by
  induction e <;> simp [embed, decode, *]

@[simp] theorem embed_isValue (e : RecursiveEffects.Expr Op Key Scope) : (embed e).isValue = e.isValue := by
  induction e <;> simp [embed, Core.Expr.isValue, RecursiveEffects.Expr.isValue, *]

theorem decode_value (e : Term Op Key Scope) (h : e.isValue = true) : (decode e).isValue = true := by
  cases e <;> simp_all [Core.Expr.isValue, decode, RecursiveEffects.Expr.isValue]
  all_goals first | exact ⟨decode_value _ h.1, decode_value _ h.2⟩ | exact decode_value _ h

inductive Binding (m : Model) (Op Key Scope : Type) where
  | mono : Comp m → Binding m Op Key Scope
  | poly : Term Op Key Scope → List (Binding m Op Key Scope) → Binding m Op Key Scope
  /-- An independently prescribed signature quantifies value types only.
  Inferred row assignments and the lexical environment are captured by
  `instantiate`; no fresh row assignment is supplied at a call. -/
  | signature (n : Nat) (instantiate : (Fin n → m.Ty) → Comp m) : Binding m Op Key Scope

mutual
  inductive Typing (m : Model) (view : RowView m algebra) (sigs : Op → RecursiveEffects.Signature m Key) : List (Binding m Op Key Scope) → Term Op Key Scope → Comp m → Prop where
    | var : Γ[n]? = some b → BindingTyping m view sigs b c → Typing m view sigs Γ (.var n) c
    | lit : Comp.le m (Comp.pure m (m.base b)) c → Typing m view sigs Γ (.lit b) c
    | lam : Typing m view sigs (.mono a :: Γ) body b →
        Comp.le m (Comp.pure m (Comp.arrow m a b)) c → Typing m view sigs Γ (.lam body) c
    | app : Typing m view sigs Γ f (Comp.arrow m a b, ef) → Typing m view sigs Γ x a →
        Comp.le m (b.1, m.join ef b.2) c → Typing m view sigs Γ (.app f x) c
    | letValue : v.isValue = true → Typing m view sigs Γ v (Comp.pure m a) →
        Typing m view sigs (.poly v Γ :: Γ) body c → Typing m view sigs Γ (.letE none v body) c
    | letComputed : Typing m view sigs Γ v a →
        Typing m view sigs (.mono (Comp.pure m a.1) :: Γ) body b →
        Comp.le m (b.1, m.join a.2 b.2) c → Typing m view sigs Γ (.letE none v body) c
    | branch : Typing m view sigs Γ condition (m.base .bool, eg) →
        Typing m view sigs Γ yes a → Typing m view sigs Γ no b →
        Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c →
        Typing m view sigs Γ (.branch condition yes no) c
    | pair : Typing m view sigs Γ x a → Typing m view sigs Γ y b →
        Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c → Typing m view sigs Γ (.pair x y) c
    | fst : Typing m view sigs Γ x (m.pair a b, er) →
        Comp.le m (a, er) c → Typing m view sigs Γ (.fst x) c
    | snd : Typing m view sigs Γ x (m.pair a b, er) →
        Comp.le m (b, er) c → Typing m view sigs Γ (.snd x) c
    | emptyRecord : Comp.le m (Comp.pure m m.emptyRecord) c →
        Typing m view sigs Γ .emptyRecord c
    | record : Typing m view sigs Γ x a → Typing m view sigs Γ rest b → m.subTy b.1 m.emptyRecord →
        Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c →
        Typing m view sigs Γ (.record l x rest) c
    | field : Typing m view sigs Γ x (m.record l a m.emptyRecord, er) →
        Comp.le m (a, er) c → Typing m view sigs Γ (.field l x) c
    | variant : Typing m view sigs Γ x a →
        Comp.le m (m.variant l a.1, a.2) c → Typing m view sigs Γ (.variant l x) c

    | request : Typing m view sigs Γ payload ((sigs op).input, er) →
        m.subTy (sigs op).output c.1 →
        algebra.le (algebra.join (view.decode er)
          (algebra.join (algebra.head (sigs op).key) (keysRow algebra (sigs op).extra)))
          (view.decode c.2) → Typing m view sigs Γ (.request op payload) c
    | boundary : Typing m view sigs Γ body input → m.subTy input.1 c.1 →
        algebra.le (boundary.row algebra (view.decode input.2)) (view.decode c.2) →
        Typing m view sigs Γ (.boundary boundary body) c
    | handler : Typing m view sigs Γ action input →
        Typing m view sigs (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
        Typing m view sigs
          (.mono (Comp.pure m (sigs op).input) ::
           .mono (Comp.pure m (Comp.arrow m (Comp.pure m (sigs op).output) input)) :: Γ)
          onOperation operated →
        m.subTy (m.union returned.1 operated.1) c.1 →
        algebra.le (algebra.join (algebra.residual [(sigs op).key] (view.decode input.2))
          (algebra.join (view.decode returned.2) (view.decode operated.2))) (view.decode c.2) →
        Typing m view sigs Γ (.handler op action onReturn onOperation) c

  inductive BindingTyping (m : Model) (view : RowView m algebra) (sigs : Op → RecursiveEffects.Signature m Key) : Binding m Op Key Scope → Comp m → Prop where
    | mono : Comp.le m a c → BindingTyping m view sigs (.mono a) c
    | poly : Typing m view sigs Γ v (Comp.pure m c.1) → m.subRow m.empty c.2 →
        BindingTyping m view sigs (.poly v Γ) c
    | signature {n : Nat} {instantiate : (Fin n → m.Ty) → Comp m} {ι : Fin n → m.Ty} :
        Comp.le m (instantiate ι) c →
        BindingTyping m view sigs (.signature n instantiate) c
end

def model (m : Model) (view : RowView m algebra)
    (sigs : Op → RecursiveEffects.Signature m Key) :
    TypingModel ⟨Op, Key, Scope, Empty, Empty⟩ :=
  ⟨List (Binding m Op Key Scope), Comp m, Typing m view sigs⟩

def binding : RecursiveEffects.Binding m Op Key Scope → Binding m Op Key Scope
  | .mono a => .mono a
  | .poly e Γ => .poly (embed e) (Γ.map binding)
  | .signature n instantiate => .signature n instantiate

def unbinding : Binding m Op Key Scope → RecursiveEffects.Binding m Op Key Scope
  | .mono a => .mono a
  | .poly e Γ => .poly (decode e) (Γ.map unbinding)
  | .signature n instantiate => .signature n instantiate

@[simp] theorem unbinding_binding (b : RecursiveEffects.Binding m Op Key Scope) : unbinding (binding b) = b := by
  induction b using RecursiveEffects.Binding.rec
    (motive_2 := fun Γ => (Γ.map binding).map unbinding = Γ) <;>
    simp_all [binding, unbinding, List.map_map, Function.comp_def]

theorem preserved {view : RowView m algebra} {sigs : Op → RecursiveEffects.Signature m Key} (h : RecursiveEffects.Typing m view sigs Γ e c) :
    Typing m view sigs (Γ.map binding) (embed e) c := by
  induction h using RecursiveEffects.Typing.rec
    (motive_2 := fun b c _ => BindingTyping m view sigs (binding b) c)
  all_goals simp only [embed, binding, List.map_cons] at *
  case var found _ ih => exact .var (by simp [List.getElem?_map, found]) ih
  all_goals first
    | apply Typing.letValue <;> first | simpa using ‹_› | assumption
    | apply Typing.lit; assumption
    | apply Typing.lam <;> assumption
    | apply Typing.app <;> assumption
    | apply Typing.letComputed <;> assumption
    | apply Typing.branch <;> assumption
    | apply Typing.pair <;> assumption
    | apply Typing.fst <;> assumption
    | apply Typing.snd <;> assumption
    | apply Typing.emptyRecord; assumption
    | apply Typing.record <;> assumption
    | apply Typing.field <;> assumption
    | apply Typing.variant <;> assumption
    | apply Typing.request <;> assumption
    | apply Typing.boundary <;> assumption
    | apply Typing.handler <;> assumption
    | apply BindingTyping.mono; assumption
    | apply BindingTyping.poly <;> assumption
    | apply BindingTyping.signature; assumption

theorem reflected {view : RowView m algebra} {sigs : Op → RecursiveEffects.Signature m Key} (h : Typing m view sigs Γ e c) :
    RecursiveEffects.Typing m view sigs (Γ.map unbinding) (decode e) c := by
  induction h using Typing.rec
    (motive_2 := fun b c _ => RecursiveEffects.BindingTyping m view sigs (unbinding b) c)
  all_goals simp only [decode, unbinding, List.map_cons] at *
  case var found _ ih => exact .var (by simp [List.getElem?_map, found]) ih
  case letValue value _ _ ihv ihb => exact .letValue (decode_value _ value) ihv ihb
  all_goals first
    | apply RecursiveEffects.Typing.lit; assumption
    | apply RecursiveEffects.Typing.lam <;> assumption
    | apply RecursiveEffects.Typing.app <;> assumption
    | apply RecursiveEffects.Typing.letComputed <;> assumption
    | apply RecursiveEffects.Typing.branch <;> assumption
    | apply RecursiveEffects.Typing.pair <;> assumption
    | apply RecursiveEffects.Typing.fst <;> assumption
    | apply RecursiveEffects.Typing.snd <;> assumption
    | apply RecursiveEffects.Typing.emptyRecord; assumption
    | apply RecursiveEffects.Typing.record <;> assumption
    | apply RecursiveEffects.Typing.field <;> assumption
    | apply RecursiveEffects.Typing.variant <;> assumption
    | apply RecursiveEffects.Typing.request <;> assumption
    | apply RecursiveEffects.Typing.boundary <;> assumption
    | apply RecursiveEffects.Typing.handler <;> assumption
    | apply RecursiveEffects.BindingTyping.mono; assumption
    | apply RecursiveEffects.BindingTyping.poly <;> assumption
    | apply RecursiveEffects.BindingTyping.signature; assumption

/-- All models, all environments (including captured schemes), terms and
result computations. No inference success or syntactic support premise. -/
theorem conservative (m : Model) (view : RowView m algebra)
    (sigs : Op → RecursiveEffects.Signature m Key) (Γ : List (RecursiveEffects.Binding m Op Key Scope))
    (e : RecursiveEffects.Expr Op Key Scope) (c : Comp m) :
    RecursiveEffects.Typing m view sigs Γ e c ↔ Core.Typing (model m view sigs) (Γ.map binding) (embed e) c := by
  constructor
  · exact preserved
  · intro h
    simpa [List.map_map, Function.comp_def] using reflected h

end Yulang.Core.Effects
