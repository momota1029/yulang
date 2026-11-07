import Yulang.CoreExpr
import Yulang.QualifiedInference

/-! Qualified rules retain the old ground role theory and method table.
Binding typing contains only semantic predicates, not expression typing. -/
namespace Yulang.Core.Qualified
open Inference (Model Comp)
open RoleConstraints
open QualifiedInference (MethodTable Binding BindingTyping typeEnv)
abbrev Term := Core.Expr Signature.empty

def embed : QualifiedInference.Expr → Term
  | .var a => .var a
  | .method a => .method a
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
  | .field a b => .field a (embed b)
  | .variant a b => .variant a (embed b)

def decode : Term → QualifiedInference.Expr
  | .var a => .var a
  | .method a => .method a
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
  | .field a b => .field a (decode b)
  | .variant a b => .variant a (decode b)
  | _ => .lit .unit

@[simp] theorem decode_embed (e : QualifiedInference.Expr) : decode (embed e) = e := by
  induction e <;> simp [embed, decode, *]

inductive Typing (m : Model) (methods : MethodTable) (theory : Theory m) : List (Binding m) → Term → Comp m → Prop where
  | var : Γ[n]? = some b → BindingTyping m theory b c → Typing m methods theory Γ (.var n) c
  | method (ι : Fin (methods name).locals → m.Ty) :
      Satisfies theory ((methods name).requirements.map (Goal.eval m (typeEnv m ι))) →
      Comp.le m (Comp.pure m ((methods name).value.eval m (typeEnv m ι))) c →
      Typing m methods theory Γ (.method name) c
  | lit : Comp.le m (Comp.pure m (m.base b)) c → Typing m methods theory Γ (.lit b) c
  | lam : Typing m methods theory (.mono a :: Γ) body b →
      Comp.le m (Comp.pure m (Comp.arrow m a b)) c → Typing m methods theory Γ (.lam body) c
  | app : Typing m methods theory Γ f (Comp.arrow m a b, ef) → Typing m methods theory Γ x a →
      Comp.le m (b.1, m.join ef b.2) c → Typing m methods theory Γ (.app f x) c
  | letComputed : Typing m methods theory Γ v a →
      Typing m methods theory (.mono (Comp.pure m a.1) :: Γ) body b →
      Comp.le m (b.1, m.join a.2 b.2) c → Typing m methods theory Γ (.letE none v body) c
  | branch : Typing m methods theory Γ condition (m.base .bool, eg) →
      Typing m methods theory Γ yes a → Typing m methods theory Γ no b →
      Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c →
      Typing m methods theory Γ (.branch condition yes no) c
  | pair : Typing m methods theory Γ x a → Typing m methods theory Γ y b →
      Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c → Typing m methods theory Γ (.pair x y) c
  | fst : Typing m methods theory Γ x (m.pair a b, er) →
      Comp.le m (a, er) c → Typing m methods theory Γ (.fst x) c
  | snd : Typing m methods theory Γ x (m.pair a b, er) →
      Comp.le m (b, er) c → Typing m methods theory Γ (.snd x) c
  | emptyRecord : Comp.le m (Comp.pure m m.emptyRecord) c →
      Typing m methods theory Γ .emptyRecord c
  | record : Typing m methods theory Γ x a → Typing m methods theory Γ rest b → m.subTy b.1 m.emptyRecord →
      Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c →
      Typing m methods theory Γ (.record l x rest) c
  | field : Typing m methods theory Γ x (m.record l a m.emptyRecord, er) →
      Comp.le m (a, er) c → Typing m methods theory Γ (.field l x) c
  | variant : Typing m methods theory Γ x a →
      Comp.le m (m.variant l a.1, a.2) c → Typing m methods theory Γ (.variant l x) c


/-- Two fresh slots. Their names and all prior free names remain distinct. -/
def model (m : Model) (methods : MethodTable) (theory : Theory m) :
    TypingModel Signature.empty := ⟨List (Binding m), Comp m, Typing m methods theory⟩

theorem preserved (h : QualifiedInference.Typing m methods theory Γ e c) :
    Typing m methods theory Γ (embed e) c := by
  induction h
  all_goals simp only [embed] at *
  all_goals first
    | apply Typing.var <;> assumption
    | apply Typing.method <;> assumption
    | apply Typing.lit <;> assumption
    | apply Typing.lam <;> assumption
    | apply Typing.app <;> assumption
    | apply Typing.letComputed <;> assumption
    | apply Typing.branch <;> assumption
    | apply Typing.pair <;> assumption
    | apply Typing.fst <;> assumption
    | apply Typing.snd <;> assumption
    | apply Typing.emptyRecord <;> assumption
    | apply Typing.record <;> assumption
    | apply Typing.field <;> assumption
    | apply Typing.variant <;> assumption

theorem reflected (h : Typing m methods theory Γ e c) :
    QualifiedInference.Typing m methods theory Γ (decode e) c := by
  induction h
  all_goals simp only [decode] at *
  all_goals first
    | apply QualifiedInference.Typing.var <;> assumption
    | apply QualifiedInference.Typing.method <;> assumption
    | apply QualifiedInference.Typing.lit <;> assumption
    | apply QualifiedInference.Typing.lam <;> assumption
    | apply QualifiedInference.Typing.app <;> assumption
    | apply QualifiedInference.Typing.letComputed <;> assumption
    | apply QualifiedInference.Typing.branch <;> assumption
    | apply QualifiedInference.Typing.pair <;> assumption
    | apply QualifiedInference.Typing.fst <;> assumption
    | apply QualifiedInference.Typing.snd <;> assumption
    | apply QualifiedInference.Typing.emptyRecord <;> assumption
    | apply QualifiedInference.Typing.record <;> assumption
    | apply QualifiedInference.Typing.field <;> assumption
    | apply QualifiedInference.Typing.variant <;> assumption

theorem conservative (m : Model) (methods : MethodTable) (theory : Theory m)
    (Γ : List (Binding m)) (e : QualifiedInference.Expr) (c : Comp m) :
    QualifiedInference.Typing m methods theory Γ e c ↔
      Core.Typing (model m methods theory) Γ (embed e) c := by
  constructor
  · exact preserved
  · intro h; simpa using reflected h

end Yulang.Core.Qualified
