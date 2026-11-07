import Yulang.CoreExpr
import Yulang.Inference

/-! Independent required-field rules on `Core.Expr`. These are the rules of
`Inference`, including its captured polymorphic bindings; no legacy typing
judgement occurs in their definition. `recordDefault` deliberately has no rule.
Its presence-aware interpretation is a different model (M1 boundary). -/

namespace Yulang.Core.Required
open Inference (Model Comp)
abbrev Term := Core.Expr Signature.empty

def embed : Inference.Expr → Term
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

/-- A retraction, used only to prove reflection. Unsupported syntax is never
accepted by the independent judgement below. -/
def decode : Term → Inference.Expr
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
  | _ => .lit .unit

@[simp] theorem decode_embed (e : Inference.Expr) : decode (embed e) = e := by
  induction e <;> simp [embed, decode, *]

@[simp] theorem embed_isValue (e : Inference.Expr) : (embed e).isValue = e.isValue := by
  induction e <;> simp [embed, Core.Expr.isValue, Inference.Expr.isValue, *]

theorem decode_value (e : Term) (h : e.isValue = true) : (decode e).isValue = true := by
  cases e <;> simp_all [Core.Expr.isValue, decode, Inference.Expr.isValue]
  all_goals first | exact ⟨decode_value _ h.1, decode_value _ h.2⟩ | exact decode_value _ h

inductive Binding (m : Model) where
  | mono : Comp m → Binding m
  | poly : Term → List (Binding m) → Binding m
  /-- An independently prescribed signature quantifies value types only.
  Inferred row assignments and the lexical environment are captured by
  `instantiate`; no fresh row assignment is supplied at a call. -/
  | signature (n : Nat) (instantiate : (Fin n → m.Ty) → Comp m) : Binding m

mutual
  inductive Typing (m : Model) : List (Binding m) → Term → Comp m → Prop where
    | var : Γ[n]? = some b → BindingTyping m b c → Typing m Γ (.var n) c
    | lit : Comp.le m (Comp.pure m (m.base b)) c → Typing m Γ (.lit b) c
    | lam : Typing m (.mono a :: Γ) body b →
        Comp.le m (Comp.pure m (Comp.arrow m a b)) c → Typing m Γ (.lam body) c
    | app : Typing m Γ f (Comp.arrow m a b, ef) → Typing m Γ x a →
        Comp.le m (b.1, m.join ef b.2) c → Typing m Γ (.app f x) c
    | letValue : v.isValue = true → Typing m Γ v (Comp.pure m a) →
        Typing m (.poly v Γ :: Γ) body c → Typing m Γ (.letE none v body) c
    | letComputed : Typing m Γ v a →
        Typing m (.mono (Comp.pure m a.1) :: Γ) body b →
        Comp.le m (b.1, m.join a.2 b.2) c → Typing m Γ (.letE none v body) c
    | branch : Typing m Γ condition (m.base .bool, eg) →
        Typing m Γ yes a → Typing m Γ no b →
        Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c →
        Typing m Γ (.branch condition yes no) c
    | pair : Typing m Γ x a → Typing m Γ y b →
        Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c → Typing m Γ (.pair x y) c
    | fst : Typing m Γ x (m.pair a b, er) →
        Comp.le m (a, er) c → Typing m Γ (.fst x) c
    | snd : Typing m Γ x (m.pair a b, er) →
        Comp.le m (b, er) c → Typing m Γ (.snd x) c
    | emptyRecord : Comp.le m (Comp.pure m m.emptyRecord) c →
        Typing m Γ .emptyRecord c
    | record : Typing m Γ x a → Typing m Γ rest b → m.subTy b.1 m.emptyRecord →
        Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c →
        Typing m Γ (.record l x rest) c
    | field : Typing m Γ x (m.record l a m.emptyRecord, er) →
        Comp.le m (a, er) c → Typing m Γ (.field l x) c
    | variant : Typing m Γ x a →
        Comp.le m (m.variant l a.1, a.2) c → Typing m Γ (.variant l x) c

  inductive BindingTyping (m : Model) : Binding m → Comp m → Prop where
    | mono : Comp.le m a c → BindingTyping m (.mono a) c
    | poly : Typing m Γ v (Comp.pure m c.1) → m.subRow m.empty c.2 →
        BindingTyping m (.poly v Γ) c
    | signature {n : Nat} {instantiate : (Fin n → m.Ty) → Comp m} {ι : Fin n → m.Ty} :
        Comp.le m (instantiate ι) c →
        BindingTyping m (.signature n instantiate) c
end


def model (m : Model) : TypingModel Signature.empty :=
  ⟨List (Binding m), Comp m, Typing m⟩

def binding : Inference.Binding m → Binding m
  | .mono a => .mono a
  | .poly e Γ => .poly (embed e) (Γ.map binding)
  | .signature n instantiate => .signature n instantiate

def unbinding : Binding m → Inference.Binding m
  | .mono a => .mono a
  | .poly e Γ => .poly (decode e) (Γ.map unbinding)
  | .signature n instantiate => .signature n instantiate

@[simp] theorem unbinding_binding (b : Inference.Binding m) : unbinding (binding b) = b := by
  induction b using Inference.Binding.rec
    (motive_2 := fun Γ => (Γ.map binding).map unbinding = Γ) <;>
    simp_all [binding, unbinding, List.map_map, Function.comp_def]

theorem preserved (h : Inference.Typing m Γ e c) :
    Typing m (Γ.map binding) (embed e) c := by
  induction h using Inference.Typing.rec
    (motive_2 := fun b c _ => BindingTyping m (binding b) c)
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
    | apply BindingTyping.mono; assumption
    | apply BindingTyping.poly <;> assumption
    | apply BindingTyping.signature; assumption

theorem reflected (h : Typing m Γ e c) :
    Inference.Typing m (Γ.map unbinding) (decode e) c := by
  induction h using Typing.rec
    (motive_2 := fun b c _ => Inference.BindingTyping m (unbinding b) c)
  all_goals simp only [decode, unbinding, List.map_cons] at *
  case var found _ ih => exact .var (by simp [List.getElem?_map, found]) ih
  case letValue value _ _ ihv ihb => exact .letValue (decode_value _ value) ihv ihb
  all_goals first
    | apply Inference.Typing.lit; assumption
    | apply Inference.Typing.lam <;> assumption
    | apply Inference.Typing.app <;> assumption
    | apply Inference.Typing.letComputed <;> assumption
    | apply Inference.Typing.branch <;> assumption
    | apply Inference.Typing.pair <;> assumption
    | apply Inference.Typing.fst <;> assumption
    | apply Inference.Typing.snd <;> assumption
    | apply Inference.Typing.emptyRecord; assumption
    | apply Inference.Typing.record <;> assumption
    | apply Inference.Typing.field <;> assumption
    | apply Inference.Typing.variant <;> assumption
    | apply Inference.BindingTyping.mono; assumption
    | apply Inference.BindingTyping.poly <;> assumption
    | apply Inference.BindingTyping.signature; assumption

/-- All models, all environments (including captured schemes), terms and
result computations. No inference success or syntactic support premise. -/
theorem conservative (m : Model) (Γ : List (Inference.Binding m))
    (e : Inference.Expr) (c : Comp m) :
    Inference.Typing m Γ e c ↔ Core.Typing (model m) (Γ.map binding) (embed e) c := by
  constructor
  · exact preserved
  · intro h
    simpa [List.map_map, Function.comp_def] using reflected h

end Yulang.Core.Required
