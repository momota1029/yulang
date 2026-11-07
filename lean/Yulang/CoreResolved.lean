import Yulang.CoreExpr
import Yulang.MultiOperationHandlerTyping

/-! Independent shape-resolved typing over untyped shared syntax. Shape and
annotation information is existential in a derivation, not stored in the AST.
Both historical suspended and strict applications have explicit constructors.
Erasure preserves typing; reflection to the *same annotated source term* is
false, because erasure forgets lambda/handler/widen annotations. -/
namespace Yulang.Core.Resolved
open Directed OperationalTyping MultiOperationHandlers
open MultiOperationHandlerTyping (collectRows)
variable {n : Nat} {Key Atom : Type}
abbrev Term (n : Nat) (Key Atom : Type) := Core.Expr ⟨Key, Key, Fin n, Empty, Atom⟩

def varIndex : Var Γ s → Nat
  | .here => 0
  | .there index => varIndex index + 1

def operational : OperationalTyping.Expr n Key Atom Γ s → Term n Key Atom
  | .var index => .var (varIndex index)
  | .lit value => .atom value
  | .lam _ body => .lam (operational body)
  | .app f a => .app (operational f) (operational a)
  | .pair a b => .pair (operational a) (operational b)
  | .fst a => .fst (operational a)
  | .snd a => .snd (operational a)
  | .letE a b => .letE none (operational a) (operational b)
  | .request key a => .request key (operational a)
  | .boundary boundary a => .boundary boundary (operational a)
  | .handler key _ a b c => .handler key (operational a) (operational b) (operational c)
  | .widen _ a => operational a

def multi : MultiOperationHandlerTyping.Expr n Key Atom Γ s → Term n Key Atom
  | .core expression => operational (StrictApplication.compile expression)
  | .lam _ body => .lam (multi body)
  | .app f a => .strictApp (multi f) (multi a)
  | .pair a b => .pair (multi a) (multi b)
  | .fst a => .fst (multi a)
  | .snd a => .snd (multi a)
  | .letE a b => .letE none (multi a) (multi b)
  | .request key a => .request key (multi a)
  | .boundary boundary a => .boundary boundary (multi a)
  | .handler ops _ a b cs => .multiHandler ops (multi a) (multi b) (fun i => multi (cs i))
  | .partialHandler arms _ a b cs => .partialHandler arms (multi a) (multi b) (fun i => multi (cs i))
  | .widen _ a => multi a

inductive Typing [DecidableEq Key] : {Γ : List Shape} →
    Env (CTy n Key) Γ → {s : Shape} → Term n Key Atom → CTy n Key s → Prop where
  | var : Typing types (.var (varIndex index)) (types index)
  | lit : Typing types (.atom value) (CTy.pure .atom)
  | lam : Typing (Env.cons input types) body output →
      Typing types (.lam body) (CTy.pure (CTy.arrow input output))
  | app : Typing types function ⟨CTy.arrow input output, functionRow⟩ →
      Typing types argument actual → CLe actual input →
      Typing types (.app function argument) ⟨output.value, functionRow ++ output.row⟩
  | strictApp : Typing types function ⟨CTy.arrow input output, functionRow⟩ →
      Typing types argument actual → CLe (CTy.pure actual.value) input →
      Typing types (.strictApp function argument)
        ⟨output.value, functionRow ++ (actual.row ++ output.row)⟩
  | pair : Typing types left a → Typing types right b →
      Typing types (.pair left right) ⟨.pair a.value b.value, a.row ++ b.row⟩
  | fst : Typing types pair ⟨.pair a b, row⟩ → Typing types (.fst pair) ⟨a, row⟩
  | snd : Typing types pair ⟨.pair a b, row⟩ → Typing types (.snd pair) ⟨b, row⟩
  | letE : Typing types value input → Typing (Env.cons (CTy.pure input.value) types) body output →
      Typing types (.letE none value body) ⟨output.value, input.row ++ output.row⟩
  | request : Typing types payload ⟨.atom, row⟩ →
      Typing types (.request key payload) ⟨.atom, row ++ [raw key]⟩
  | boundary : Typing types body input →
      Typing types (.boundary boundary body) ⟨input.value, OperationalTyping.Boundary.row boundary input.row⟩
  | handler : Typing types action input →
      Typing (Env.cons (CTy.pure input.value) types) onReturn returned →
      Typing (operationTypes types input) onOperation operated →
      VLe returned.value target → VLe operated.value target →
      Typing types (.handler key action onReturn onOperation)
        ⟨target, residual [key] input.row ++ (returned.row ++ operated.row)⟩
  | widen : Typing types body input → CLe input target →
      Typing types body target

  | multiHandler {count : Nat} {operations : Operations Key count}
      {onOperation : Fin count → Term n Key Atom}
      {operated : Fin count → CTy n Key b} :
      Typing types action input →
      Typing (Env.cons (CTy.pure input.value) types) onReturn returned →
      (∀ index, Typing (operationTypes types input) (onOperation index) (operated index)) →
      VLe returned.value target → (∀ index, VLe (operated index).value target) →
      Typing types (.multiHandler operations action onReturn onOperation)
        ⟨target, residual operations.keys input.row ++
          (returned.row ++ collectRows (fun index => (operated index).row))⟩
  | partialHandler {count : Nat} {arms : Fin count → MultiOperationPayloadHandlers.Arm Key Atom}
      {onArm : Fin count → Term n Key Atom}
      {operated : Fin count → CTy n Key b} :
      Typing types action input →
      Typing (Env.cons (CTy.pure input.value) types) onReturn returned →
      (∀ index, Typing (operationTypes types input) (onArm index) (operated index)) →
      VLe returned.value target → (∀ index, VLe (operated index).value target) →
      Typing types (.partialHandler arms action onReturn onArm)
        ⟨target, residual (MultiOperationPayloadHandlers.removedKeys arms) input.row ++
          (returned.row ++ collectRows (fun index => (operated index).row))⟩

def model [DecidableEq Key] : TypingModel ⟨Key, Key, Fin n, Empty, Atom⟩ where
  Context := (Γ : List Shape) × Env (CTy n Key) Γ
  Result := (s : Shape) × CTy n Key s
  judgment := fun ⟨_, types⟩ expression ⟨_, output⟩ => Typing types expression output

theorem operational_preserved [DecidableEq Key]
    {Γ : List Shape} {s : Shape} {types : Env (CTy n Key) Γ}
    {expression : OperationalTyping.Expr n Key Atom Γ s} {output : CTy n Key s}
    (h : OperationalTyping.Typing types expression output) :
    Typing types (operational expression) output := by
  induction h
  all_goals simp only [operational] at *
  all_goals first
    | apply Typing.var <;> assumption
    | apply Typing.lit <;> assumption
    | apply Typing.lam <;> assumption
    | apply Typing.app <;> assumption
    | apply Typing.pair <;> assumption
    | apply Typing.fst <;> assumption
    | apply Typing.snd <;> assumption
    | apply Typing.letE <;> assumption
    | apply Typing.request <;> assumption
    | apply Typing.boundary <;> assumption
    | apply Typing.handler <;> assumption
    | apply Typing.widen <;> assumption

theorem multi_preserved [DecidableEq Key]
    {Γ : List Shape} {s : Shape} {types : Env (CTy n Key) Γ}
    {expression : MultiOperationHandlerTyping.Expr n Key Atom Γ s} {output : CTy n Key s}
    (h : MultiOperationHandlerTyping.Typing types expression output) :
    Typing types (multi expression) output := by
  induction h
  all_goals simp only [multi] at *
  case core h => exact operational_preserved h
  all_goals first
    | apply Typing.lam <;> assumption
    | apply Typing.strictApp <;> assumption
    | apply Typing.pair <;> assumption
    | apply Typing.fst <;> assumption
    | apply Typing.snd <;> assumption
    | apply Typing.letE <;> assumption
    | apply Typing.request <;> assumption
    | apply Typing.boundary <;> assumption
    | apply Typing.multiHandler <;> assumption
    | apply Typing.partialHandler <;> assumption
    | apply Typing.widen <;> assumption

theorem operational_core [DecidableEq Key]
    {Γ : List Shape} {s : Shape} {types : Env (CTy n Key) Γ}
    {expression : OperationalTyping.Expr n Key Atom Γ s} {output : CTy n Key s}
    (h : OperationalTyping.Typing types expression output) :
    Core.Typing model ⟨Γ, types⟩ (operational expression) ⟨s, output⟩ :=
  operational_preserved h

theorem multi_core [DecidableEq Key]
    {Γ : List Shape} {s : Shape} {types : Env (CTy n Key) Γ}
    {expression : MultiOperationHandlerTyping.Expr n Key Atom Γ s} {output : CTy n Key s}
    (h : MultiOperationHandlerTyping.Typing types expression output) :
    Core.Typing model ⟨Γ, types⟩ (multi expression) ⟨s, output⟩ :=
  multi_preserved h

/-- Concrete failure of reflection, even without lambda shapes: the original
widen node fixes a nonempty row, while the erased atom has a pure typing. -/
def annotated : OperationalTyping.Expr 0 Nat Unit [] .atom :=
  .widen ⟨.atom, [raw 0]⟩ (.lit ())

theorem annotation_erasure_typed :
    Core.Typing (model (n := 0) (Key := Nat) (Atom := Unit))
      ⟨[], Env.nil⟩ (operational annotated) ⟨.atom, CTy.pure .atom⟩ :=
  Typing.lit

theorem annotated_not_pure :
    ¬ OperationalTyping.Typing Env.nil annotated (CTy.pure .atom) := by
  intro h
  cases h

def multiAnnotated : MultiOperationHandlerTyping.Expr 0 Nat Unit [] .atom :=
  .widen ⟨.atom, [raw 0]⟩ (.lit ())

theorem multi_annotation_erasure_typed :
    Core.Typing (model (n := 0) (Key := Nat) (Atom := Unit))
      ⟨[], Env.nil⟩ (multi multiAnnotated) ⟨.atom, CTy.pure .atom⟩ :=
  Typing.lit

theorem multi_annotated_not_pure :
    ¬ MultiOperationHandlerTyping.Typing Env.nil multiAnnotated (CTy.pure .atom) := by
  intro h
  cases h

end Yulang.Core.Resolved
