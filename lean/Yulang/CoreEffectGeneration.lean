import Yulang.CoreEffectTyping

/-!
# Model-indexed generation (M2)

These are semantic constraints over an arbitrary supplied model, not the finite
first-order `RecursiveEffects.Formula` syntax. Generation recurses on Core syntax
and stores generated scheme predicates at value lets. Its leaves are only model
comparisons, permission tests and scheme lookups; it never calls Typing or a
solver. Reification to a model-independent finite formula remains a separate
obligation. Quantified arm-result functions are witnesses, not solver oracles.
-/
namespace Yulang.Core.EffectTyping
open Inference (Model Comp)
open RowInference (RowAlgebra RowView keysRow)
variable {s : Core.Signature} {m : Model} {algebra : RowAlgebra s.Key s.Scope}

abbrev SchemeEnv (m : Model) := List (Comp m → Prop)

def mono (m : Model) (input : Comp m) : Comp m → Prop := Comp.le m input

def lookup (Γ : SchemeEnv m) (n : Nat) (c : Comp m) : Prop :=
  ∃ scheme, Γ[n]? = some scheme ∧ scheme c

/-- Every recursive call is on a strict subexpression, including stored value
schemes and every operation arm. Unsupported Core constructors generate False. -/
def generate (view : RowView m algebra) (contract : Contract s m)
    (Γ : SchemeEnv m) (e : Core.Expr s) (c : Comp m) : Prop :=
  match e with
  | .var n => lookup Γ n c
  | .lit b => Comp.le m (Comp.pure m (m.base b)) c
  | .lam body => ∃ a b, generate view contract (mono m a :: Γ) body b ∧
      Comp.le m (Comp.pure m (Comp.arrow m a b)) c
  | .app f x => ∃ a b ef,
      generate view contract Γ f (Comp.arrow m a b, ef) ∧
      generate view contract Γ x a ∧ Comp.le m (b.1, m.join ef b.2) c
  | .letE none v body =>
      (v.isValue = true ∧ ∃ a, generate view contract Γ v (Comp.pure m a) ∧
        generate view contract
          ((fun d => generate view contract Γ v (Comp.pure m d.1) ∧ m.subRow m.empty d.2) :: Γ) body c) ∨
      (∃ a b, generate view contract Γ v a ∧
        generate view contract (mono m (Comp.pure m a.1) :: Γ) body b ∧
        Comp.le m (b.1, m.join a.2 b.2) c)
  | .branch g y n => ∃ eg a b, generate view contract Γ g (m.base .bool, eg) ∧
      generate view contract Γ y a ∧ generate view contract Γ n b ∧
      Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c
  | .pair x y => ∃ a b, generate view contract Γ x a ∧ generate view contract Γ y b ∧
      Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c
  | .fst x => ∃ a b er, generate view contract Γ x (m.pair a b, er) ∧ Comp.le m (a, er) c
  | .snd x => ∃ a b er, generate view contract Γ x (m.pair a b, er) ∧ Comp.le m (b, er) c
  | .emptyRecord => Comp.le m (Comp.pure m m.emptyRecord) c
  | .record l x rest => ∃ a b, generate view contract Γ x a ∧ generate view contract Γ rest b ∧
      m.subTy b.1 m.emptyRecord ∧ Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c
  | .field l x => ∃ a er, generate view contract Γ x (m.record l a m.emptyRecord, er) ∧
      Comp.le m (a, er) c
  | .variant l x => ∃ a, generate view contract Γ x a ∧ Comp.le m (m.variant l a.1, a.2) c
  | .request op payload => ∃ ι er,
      generate view contract Γ payload ((contract.operation op).input ι, er) ∧
      m.subTy ((contract.operation op).output ι) c.1 ∧
      algebra.le (algebra.join (view.decode er)
        (algebra.join (algebra.head (contract.operation op).key)
          (keysRow algebra (contract.operation op).extra))) (view.decode c.2)
  | .boundary boundary body => ∃ input, generate view contract Γ body input ∧
      m.subTy input.1 c.1 ∧ algebra.le (boundary.row algebra (view.decode input.2)) (view.decode c.2)
  | .handler op action onReturn onOperation =>
      contract.permission e (contract.operation op).key = true ∧
      ∃ input returned, ∃ (operated : (Fin (contract.operation op).locals → m.Ty) → Comp m),
      generate view contract Γ action input ∧
      generate view contract (mono m (Comp.pure m input.1) :: Γ) onReturn returned ∧
      (∀ ι, generate view contract
        (mono m (Comp.pure m ((contract.operation op).input ι)) ::
         mono m (Comp.pure m (Comp.arrow m (Comp.pure m ((contract.operation op).output ι)) input)) :: Γ)
        onOperation (operated ι)) ∧
      (∀ ι, m.subTy (m.union returned.1 (operated ι).1) c.1) ∧
      (∀ ι, algebra.le (algebra.join (algebra.residual [(contract.operation op).key] (view.decode input.2))
        (algebra.join (view.decode returned.2) (view.decode (operated ι).2))) (view.decode c.2))
  | .multiHandler ops action onReturn bodies =>
      (∀ i, contract.permission e (ops.key i) = true) ∧
      ∃ input returned, ∃
        (operated : ((i : Fin _) → Fin (contract.keySignature (ops.key i)).locals → m.Ty) → Fin _ → Comp m),
      generate view contract Γ action input ∧
      generate view contract (mono m (Comp.pure m input.1) :: Γ) onReturn returned ∧
      (∀ ι i, generate view contract
        (mono m (Comp.pure m ((contract.keySignature (ops.key i)).input (ι i))) ::
         mono m (Comp.pure m (Comp.arrow m
           (Comp.pure m ((contract.keySignature (ops.key i)).output (ι i))) input)) :: Γ)
        (bodies i) (operated ι i)) ∧
      (∀ ι, m.subTy (collectTypes m returned.1 (fun i => (operated ι i).1)) c.1) ∧
      (∀ ι, algebra.le (algebra.join (algebra.residual ops.keys (view.decode input.2))
        (algebra.join (view.decode returned.2) (view.decode (collectRows m (fun i => (operated ι i).2)))))
        (view.decode c.2))
  | .partialHandler arms action onReturn bodies =>
      (∀ i, contract.permission e (arms i).key = true) ∧
      ∃ input returned, ∃
        (operated : ((i : Fin _) → Fin (contract.keySignature (arms i).key).locals → m.Ty) → Fin _ → Comp m),
      generate view contract Γ action input ∧
      generate view contract (mono m (Comp.pure m input.1) :: Γ) onReturn returned ∧
      (∀ ι i, generate view contract
        (mono m (Comp.pure m ((contract.keySignature (arms i).key).input (ι i))) ::
         mono m (Comp.pure m (Comp.arrow m
           (Comp.pure m ((contract.keySignature (arms i).key).output (ι i))) input)) :: Γ)
        (bodies i) (operated ι i)) ∧
      (∀ ι, m.subTy (collectTypes m returned.1 (fun i => (operated ι i).1)) c.1) ∧
      (∀ ι, algebra.le (algebra.join
        (algebra.residual (MultiOperationPayloadHandlers.removedKeys arms) (view.decode input.2))
        (algebra.join (view.decode returned.2) (view.decode (collectRows m (fun i => (operated ι i).2)))))
        (view.decode c.2))
  | _ => False

variable {view : RowView m algebra} {contract : Contract s m}

/-- Scheme lookup equivalence, including captured polymorphic environments. -/
def EnvRel (sΓ : SchemeEnv m) (Γ : List (Binding m s)) : Prop :=
  ∀ n c, lookup sΓ n c ↔ ∃ b, Γ[n]? = some b ∧ BindingTyping m view contract b c

theorem EnvRel.nil : EnvRel (view := view) (contract := contract) [] [] := by
  intro n c
  simp [lookup]

theorem EnvRel.cons {sΓ : SchemeEnv m} {Γ : List (Binding m s)}
    (h : EnvRel (view := view) (contract := contract) sΓ Γ)
    {q : Comp m → Prop} {b : Binding m s}
    (head : ∀ c, q c ↔ BindingTyping m view contract b c) : EnvRel (view := view) (contract := contract) (q :: sΓ) (b :: Γ) := by
  intro n c
  cases n with
  | zero => simpa [lookup] using head c
  | succ n => simpa [lookup] using h n c

theorem EnvRel.mono {sΓ : SchemeEnv m} {Γ : List (Binding m s)}
    (h : EnvRel (view := view) (contract := contract) sΓ Γ) (a : Comp m) :
    EnvRel (view := view) (contract := contract) (mono m a :: sΓ) (.mono a :: Γ) := by
  apply h.cons
  intro c
  constructor
  · exact BindingTyping.mono
  · intro h; cases h; assumption

end Yulang.Core.EffectTyping
