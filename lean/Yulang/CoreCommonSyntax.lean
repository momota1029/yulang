import Yulang.CorePresenceGenerationCore
import Yulang.CoreLiteral

/-!
# The common constructor judgment with content-bearing literals

This is an independent constructor judgment. Its rules do not mention a
generator, a solver, or the lowering used to implement inference. The original
presence judgment is retained separately. Literal contents stay in Core syntax;
their static type is the corresponding base type (spec 3.1 and 10.5.1).

This first stage still uses `Signature.empty`: its float/operation/atom
carriers are empty. It adds all four inhabited literal kinds and the transparent
data-leaf wrapper, at arbitrary depth under the original presence constructors.
Binder names on `letE` are provenance only, as in `CoreData`.

The separate value predicate treats these literals as values, without changing
the historical predicate used by the older models. The fallback in `lower`
is never an accepted compilation: `covered` gates the eventual solver entry.
-/

namespace Yulang.Core.CommonSyntax

open PresenceGeneration (Model Comp)
abbrev Term := Required.Term

def literalBase : LiteralValues.Literal Empty → Inference.Base
  | .int _ => .int
  | .str _ => .str
  | .bool _ => .bool
  | .unit => .unit

@[simp] theorem literalBase_exact (value : LiteralValues.Literal Empty) :
    value.legacyBase = some (literalBase value) := by
  cases value <;> first | rfl | contradiction

def covered : Term → Bool
  | .var _ | .lit _ | .literal _ | .emptyRecord => true
  | .lam body | .leaf body | .fst body | .snd body | .field _ body | .variant _ body => covered body
  | .app first last | .letE _ first last | .pair first last |
      .record _ first last | .recordDefault _ first last => covered first && covered last
  | .branch condition yes no => covered condition && covered yes && covered no
  | _ => false

def isValue : Term → Bool
  | .var _ | .lit _ | .literal _ | .lam _ | .emptyRecord => true
  | .pair first last | .record _ first last | .recordDefault _ first last =>
      isValue first && isValue last
  | .variant _ body | .leaf body => isValue body
  | _ => false

def lower : Term → Inference.Expr
  | .var index => .var index
  | .lit base => .lit base
  | .literal value => .lit (literalBase value)
  | .lam body => .lam (lower body)
  | .app first last => .app (lower first) (lower last)
  | .letE _ value body => .letE (lower value) (lower body)
  | .leaf body => lower body
  | .branch condition yes no => .branch (lower condition) (lower yes) (lower no)
  | .pair first last => .pair (lower first) (lower last)
  | .fst body => .fst (lower body)
  | .snd body => .snd (lower body)
  | .emptyRecord => .emptyRecord
  | .record label head tail => .record label (lower head) (lower tail)
  | .recordDefault label source fallback => .recordDefault label (lower source) (lower fallback)
  | .field label body => .field label (lower body)
  | .variant label body => .variant label (lower body)
  | _ => .lit .unit

@[simp] theorem covered_embed (expression : Inference.Expr) : covered (Required.embed expression) = true := by
  induction expression <;> simp [Required.embed, covered, *]

@[simp] theorem lower_embed (expression : Inference.Expr) : lower (Required.embed expression) = expression := by
  induction expression <;> simp [Required.embed, lower, *]

@[simp] theorem isValue_embed (expression : Inference.Expr) :
    isValue (Required.embed expression) = expression.isValue := by
  induction expression <;> simp [Required.embed, isValue, Inference.Expr.isValue, *]

theorem lower_isValue (expression : Term) (within : covered expression = true) :
    (lower expression).isValue = isValue expression := by
  cases expression <;> simp_all [covered, lower, isValue, Inference.Expr.isValue]
  all_goals first
    | rw [lower_isValue _ within.1, lower_isValue _ within.2]
    | exact lower_isValue _ within

inductive Binding (m : Model) where
  | mono : Comp m → Binding m
  | poly : Term → List (Binding m) → Binding m
  | signature (n : Nat) (instantiate : (Fin n → m.Ty) → Comp m) : Binding m

mutual
  inductive Typing (m : Model) : List (Binding m) → Term → Comp m → Prop where
    | var : Γ[n]? = some b → BindingTyping m b c → Typing m Γ (.var n) c
    | lit : Comp.le m (Comp.pure m (m.base b)) c → Typing m Γ (.lit b) c
    | literal : Comp.le m (Comp.pure m (m.base (literalBase value))) c →
        Typing m Γ (.literal value) c
    | lam : Typing m (.mono a :: Γ) body b →
        Comp.le m (Comp.pure m (Comp.arrow m a b)) c → Typing m Γ (.lam body) c
    | app : Typing m Γ f (Comp.arrow m a b, ef) → Typing m Γ x a →
        Comp.le m (b.1, m.join ef b.2) c → Typing m Γ (.app f x) c
    | letValue : isValue v = true → Typing m Γ v (Comp.pure m a) →
        Typing m (.poly v Γ :: Γ) body c → Typing m Γ (.letE name v body) c
    | letComputed : Typing m Γ v a →
        Typing m (.mono (Comp.pure m a.1) :: Γ) body b →
        Comp.le m (b.1, m.join a.2 b.2) c → Typing m Γ (.letE name v body) c
    | leaf : Typing m Γ body c → Typing m Γ (.leaf body) c
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
    | emptyRecord : Comp.le m (Comp.pure m m.exactEmpty) c → Typing m Γ .emptyRecord c
    | record : Typing m Γ x a → Typing m Γ rest b → m.subTy b.1 m.emptyRecord →
        Comp.le m (m.record label a.1 b.1, m.join a.2 b.2) c →
        Typing m Γ (.record label x rest) c
    | recordDefault : Typing m Γ source a → Typing m Γ fallback b → m.subTy a.1 m.emptyRecord →
        Comp.le m (m.recordDefault label a.1 b.1, m.join a.2 b.2) c →
        Typing m Γ (.recordDefault label source fallback) c
    | field : Typing m Γ x (m.required label a, er) →
        Comp.le m (a, er) c → Typing m Γ (.field label x) c
    | variant : Typing m Γ x a →
        Comp.le m (m.variant label a.1, a.2) c → Typing m Γ (.variant label x) c

  inductive BindingTyping (m : Model) : Binding m → Comp m → Prop where
    | mono : Comp.le m a c → BindingTyping m (.mono a) c
    | poly : Typing m Γ v (Comp.pure m c.1) → m.subRow m.empty c.2 →
        BindingTyping m (.poly v Γ) c
    | signature {n : Nat} {instantiate : (Fin n → m.Ty) → Comp m} {ι : Fin n → m.Ty} :
        Comp.le m (instantiate ι) c → BindingTyping m (.signature n instantiate) c
end

def model (m : Model) : TypingModel Signature.empty :=
  ⟨List (Binding m), Comp m, Typing m⟩

theorem typing_covered (typed : Typing m Γ expression result) : covered expression = true := by
  induction typed using Typing.rec (motive_2 := fun _ _ _ => True)
  all_goals first | trivial | simp_all [covered]

end Yulang.Core.CommonSyntax
