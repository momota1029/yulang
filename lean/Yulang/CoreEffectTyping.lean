import Yulang.CoreEffects

/-!
# M2: independent effect rules with explicit contracts

One judgement covers the required-field base fragment and all five effect
constructors. Contracts are model-indexed, resolved inputs: permission discovery,
role-qualified signatures and source elaboration are not implemented here.
Operation locals range over value types only. The surrounding environment,
action/return computations and final result are fixed outside their quantifier;
the internal arm computation may vary, as in RowInference.PolyHandlerTyping.
-/
namespace Yulang.Core.EffectTyping
open Inference (Model Comp)
open RowInference (RowAlgebra RowView keysRow)
variable {s : Core.Signature} {algebra : RowAlgebra s.Key s.Scope}

structure LocalSignature (m : Model) where
  locals : Nat
  input : (Fin locals → m.Ty) → m.Ty
  output : (Fin locals → m.Ty) → m.Ty

structure OperationSignature (m : Model) (Key : Type) extends LocalSignature m where
  key : Key
  extra : List Key := []

structure Contract (s : Core.Signature) (m : Model) where
  operation : s.Op → OperationSignature m s.Key
  keySignature : s.Key → LocalSignature m
  /-- Request and key-indexed handler arms use the same resolved signature. -/
  coherent : ∀ op, (operation op).toLocalSignature = keySignature (operation op).key
  /-- A supplied incoming-action contract for each delimiter, not for its arms. -/
  permission : Core.Expr s → s.Key → Bool

/-- Written order, with the value-arm type as the final union summand. -/
def collectTypes (m : Model) (returned : m.Ty) (operated : Fin count → m.Ty) : m.Ty :=
  (List.finRange count).foldr (fun i rest => m.union (operated i) rest) returned

def collectRows (m : Model) (operated : Fin count → m.Row) : m.Row :=
  (List.finRange count).foldr (fun i rest => m.join (operated i) rest) m.empty

inductive Binding (m : Model) (s : Core.Signature) where
  | mono : Comp m → Binding m s
  | poly : Core.Expr s → List (Binding m s) → Binding m s
  /-- An independently prescribed signature quantifies value types only.
  Inferred row assignments and the lexical environment are captured by
  `instantiate`; no fresh row assignment is supplied at a call. -/
  | signature (n : Nat) (instantiate : (Fin n → m.Ty) → Comp m) : Binding m s

mutual
  inductive Typing (m : Model) (view : RowView m algebra) (contract : Contract s m) : List (Binding m s) → Core.Expr s → Comp m → Prop where
    | var : Γ[n]? = some b → BindingTyping m view contract b c → Typing m view contract Γ (.var n) c
    | lit : Comp.le m (Comp.pure m (m.base b)) c → Typing m view contract Γ (.lit b) c
    | lam : Typing m view contract (.mono a :: Γ) body b →
        Comp.le m (Comp.pure m (Comp.arrow m a b)) c → Typing m view contract Γ (.lam body) c
    | app : Typing m view contract Γ f (Comp.arrow m a b, ef) → Typing m view contract Γ x a →
        Comp.le m (b.1, m.join ef b.2) c → Typing m view contract Γ (.app f x) c
    | letValue : v.isValue = true → Typing m view contract Γ v (Comp.pure m a) →
        Typing m view contract (.poly v Γ :: Γ) body c → Typing m view contract Γ (.letE none v body) c
    | letComputed : Typing m view contract Γ v a →
        Typing m view contract (.mono (Comp.pure m a.1) :: Γ) body b →
        Comp.le m (b.1, m.join a.2 b.2) c → Typing m view contract Γ (.letE none v body) c
    | branch : Typing m view contract Γ condition (m.base .bool, eg) →
        Typing m view contract Γ yes a → Typing m view contract Γ no b →
        Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c →
        Typing m view contract Γ (.branch condition yes no) c
    | pair : Typing m view contract Γ x a → Typing m view contract Γ y b →
        Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c → Typing m view contract Γ (.pair x y) c
    | fst : Typing m view contract Γ x (m.pair a b, er) →
        Comp.le m (a, er) c → Typing m view contract Γ (.fst x) c
    | snd : Typing m view contract Γ x (m.pair a b, er) →
        Comp.le m (b, er) c → Typing m view contract Γ (.snd x) c
    | emptyRecord : Comp.le m (Comp.pure m m.emptyRecord) c →
        Typing m view contract Γ .emptyRecord c
    | record : Typing m view contract Γ x a → Typing m view contract Γ rest b → m.subTy b.1 m.emptyRecord →
        Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c →
        Typing m view contract Γ (.record l x rest) c
    | field : Typing m view contract Γ x (m.record l a m.emptyRecord, er) →
        Comp.le m (a, er) c → Typing m view contract Γ (.field l x) c
    | variant : Typing m view contract Γ x a →
        Comp.le m (m.variant l a.1, a.2) c → Typing m view contract Γ (.variant l x) c

    | request {ι : Fin (contract.operation op).locals → m.Ty} :
        Typing m view contract Γ payload ((contract.operation op).input ι, er) →
        m.subTy ((contract.operation op).output ι) c.1 →
        algebra.le (algebra.join (view.decode er)
          (algebra.join (algebra.head (contract.operation op).key)
            (keysRow algebra (contract.operation op).extra))) (view.decode c.2) →
        Typing m view contract Γ (.request op payload) c
    | boundary : Typing m view contract Γ body input → m.subTy input.1 c.1 →
        algebra.le (boundary.row algebra (view.decode input.2)) (view.decode c.2) →
        Typing m view contract Γ (.boundary boundary body) c
    | handler {operated : (Fin (contract.operation op).locals → m.Ty) → Comp m} :
        contract.permission (.handler op action onReturn onOperation) (contract.operation op).key = true →
        Typing m view contract Γ action input →
        Typing m view contract (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
        (∀ ι, Typing m view contract
            (.mono (Comp.pure m ((contract.operation op).input ι)) ::
             .mono (Comp.pure m (Comp.arrow m (Comp.pure m ((contract.operation op).output ι)) input)) :: Γ)
            onOperation (operated ι)) →
        (∀ ι, m.subTy (m.union returned.1 (operated ι).1) c.1) →
        (∀ ι, algebra.le (algebra.join (algebra.residual [(contract.operation op).key] (view.decode input.2))
            (algebra.join (view.decode returned.2) (view.decode (operated ι).2))) (view.decode c.2)) →
        Typing m view contract Γ (.handler op action onReturn onOperation) c
    | multiHandler {count : Nat} {ops : MultiOperationHandlers.Operations s.Key count}
        {bodies : Fin count → Core.Expr s}
        {operated : ((i : Fin count) → Fin (contract.keySignature (ops.key i)).locals → m.Ty) → Fin count → Comp m} :
        (∀ i, contract.permission (.multiHandler ops action onReturn bodies) (ops.key i) = true) →
        Typing m view contract Γ action input →
        Typing m view contract (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
        (∀ (ι : (i : Fin count) → Fin (contract.keySignature (ops.key i)).locals → m.Ty),
          ∀ i, Typing m view contract
            (.mono (Comp.pure m ((contract.keySignature (ops.key i)).input (ι i))) ::
             .mono (Comp.pure m (Comp.arrow m
               (Comp.pure m ((contract.keySignature (ops.key i)).output (ι i))) input)) :: Γ)
            (bodies i) (operated ι i)) →
        (∀ ι, m.subTy (collectTypes m returned.1 (fun i => (operated ι i).1)) c.1) →
        (∀ ι, algebra.le (algebra.join (algebra.residual ops.keys (view.decode input.2))
            (algebra.join (view.decode returned.2) (view.decode (collectRows m (fun i => (operated ι i).2)))))
            (view.decode c.2)) →
        Typing m view contract Γ (.multiHandler ops action onReturn bodies) c
    | partialHandler {count : Nat} {arms : Fin count → MultiOperationPayloadHandlers.Arm s.Key s.Atom}
        {bodies : Fin count → Core.Expr s}
        {operated : ((i : Fin count) → Fin (contract.keySignature ((arms i).key)).locals → m.Ty) → Fin count → Comp m} :
        (∀ i, contract.permission (.partialHandler arms action onReturn bodies) (arms i).key = true) →
        Typing m view contract Γ action input →
        Typing m view contract (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
        (∀ (ι : (i : Fin count) → Fin (contract.keySignature (arms i).key).locals → m.Ty),
          ∀ i, Typing m view contract
            (.mono (Comp.pure m ((contract.keySignature (arms i).key).input (ι i))) ::
             .mono (Comp.pure m (Comp.arrow m
               (Comp.pure m ((contract.keySignature (arms i).key).output (ι i))) input)) :: Γ)
            (bodies i) (operated ι i)) →
        (∀ ι, m.subTy (collectTypes m returned.1 (fun i => (operated ι i).1)) c.1) →
        (∀ ι, algebra.le (algebra.join
            (algebra.residual (MultiOperationPayloadHandlers.removedKeys arms) (view.decode input.2))
            (algebra.join (view.decode returned.2) (view.decode (collectRows m (fun i => (operated ι i).2)))))
            (view.decode c.2)) →
        Typing m view contract Γ (.partialHandler arms action onReturn bodies) c

  inductive BindingTyping (m : Model) (view : RowView m algebra) (contract : Contract s m) : Binding m s → Comp m → Prop where
    | mono : Comp.le m a c → BindingTyping m view contract (.mono a) c
    | poly : Typing m view contract Γ v (Comp.pure m c.1) → m.subRow m.empty c.2 →
        BindingTyping m view contract (.poly v Γ) c
    | signature {n : Nat} {instantiate : (Fin n → m.Ty) → Comp m} {ι : Fin n → m.Ty} :
        Comp.le m (instantiate ι) c →
        BindingTyping m view contract (.signature n instantiate) c
end


def model (m : Model) (view : RowView m algebra) (contract : Contract s m) :
    TypingModel s := ⟨List (Binding m s), Comp m, Typing m view contract⟩

end Yulang.Core.EffectTyping
