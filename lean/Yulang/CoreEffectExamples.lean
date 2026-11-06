import Yulang.CoreEffectExactness
import Yulang.SignedStructural
import Yulang.OperationalTransportExamples

/-! Concrete generated solutions use actual signed rows and structural types.
The forwarding equation uses the existing payload runtime, not an unproved
Core evaluator. The callback equation retains the existing explicit transport. -/
namespace Yulang.Core.EffectTyping.Examples
open Inference (Comp)
open Directed

abbrev signature : Core.Signature := ⟨Nat, Nat, Fin 1, Empty, Unit⟩
abbrev M := SignedStructural.model 1 Nat
abbrev view := SignedStructural.rowView 1 Nat
abbrev Term := Core.Expr signature
abbrev unitTy : M.Ty := .base .unit
abbrev pureUnit : Comp M := (unitTy, [])

def localSignature : LocalSignature M := ⟨0, fun _ => unitTy, fun _ => unitTy⟩

def contract : Contract signature M where
  operation := fun key => { toLocalSignature := localSignature, key := key }
  keySignature := fun _ => localSignature
  coherent := fun _ => rfl
  permission := fun _ _ => true

private theorem lit (Γ : List (Binding M signature)) :
    Typing M view contract Γ (.lit .unit) pureUnit :=
  .lit ⟨.refl _, SignedStructural.row_refl _⟩

private theorem request (Γ : List (Binding M signature)) (key : Nat) :
    Typing M view contract Γ (.request key (.lit .unit)) (unitTy, [raw key]) := by
  apply Typing.request (op := key) (ι := Fin.elim0) (lit Γ)
  · exact .refl _
  · exact SignedStructural.row_refl _

def operations : MultiOperationHandlers.Operations Nat 2 :=
  ⟨Fin.val, fun _ _ h => Fin.ext h⟩

def action : Term := .letE none (.request 0 (.lit .unit)) (.request 1 (.lit .unit))
def twoOperations : Term := .multiHandler operations action (.lit .unit) (fun _ => .lit .unit)

private theorem action_typed : Typing M view contract [] action (unitTy, [raw 0, raw 1]) := by
  apply Typing.letComputed (request [] 0) (request _ 1)
  exact ⟨.refl _, SignedStructural.row_refl _⟩

/-- A single delimiter has two operations and one value arm. -/
theorem two_operations_typed : Typing M view contract [] twoOperations pureUnit := by
  apply Typing.multiHandler (operated := fun _ _ => pureUnit)
    (fun _ => rfl) action_typed (lit _) (fun _ _ => lit _)
  · intro _
    exact .unionElim (.refl _) (.unionElim (.refl _) (.refl _))
  · intro _
    change SignedStructural.RowLe
      (residual [0, 1] [raw 0, raw 1] ++ ([] ++ ([] ++ ([] ++ [])))) []
    simp [residual, Capturable, raw]
    exact SignedStructural.row_refl _

theorem two_operations_generated : generate view contract [] twoOperations pureUnit :=
  (principal_exact _ _).mpr two_operations_typed

def partialArms : Fin 1 → MultiOperationPayloadHandlers.Arm Nat Unit :=
  fun _ => ⟨0, .test (fun _ => false), none⟩

def partialTerm : Term := .partialHandler partialArms (.request 0 (.lit .unit))
  (.lit .unit) (fun _ => .lit .unit)

theorem partial_removed_keys : MultiOperationPayloadHandlers.removedKeys partialArms = [] := rfl

/-- A refutable arm keeps the key even when the value arm is pure. -/
theorem partial_typed : Typing M view contract [] partialTerm (unitTy, [raw 0]) := by
  apply Typing.partialHandler (operated := fun _ _ => pureUnit)
    (fun _ => rfl) (request [] 0) (lit _) (fun _ _ => lit _)
  · intro _
    exact .unionElim (.refl _) (.refl _)
  · intro _
    change SignedStructural.RowLe (residual [] [raw 0] ++ ([] ++ ([] ++ []))) [raw 0]
    simp [residual, Capturable]
    exact SignedStructural.row_refl _

theorem partial_generated : generate view contract [] partialTerm (unitTy, [raw 0]) :=
  (principal_exact _ _).mpr partial_typed

/-- The same arm table actually forwards the unmatched occurrence and payload. -/
theorem partial_forwards :
    MultiOperationPayloadHandlers.handle partialArms
      (fun _ : Unit => Computation.pure ())
      (fun _ _ _ => Computation.pure ())
      (Computation.request (raw (n := 1) 0) () (fun _ : Unit => Computation.pure ())) =
    Computation.request (raw 0) () (fun _ : Unit => Computation.pure ()) := rfl

/-- A callback with a latent request has a genuine generated typing. -/
theorem callback_generated :
    generate view contract [] (.lam (.request 0 (.lit .unit)))
      (Comp.pure M (Comp.arrow M pureUnit (unitTy, [raw 0]))) := by
  apply (principal_exact _ _).mpr
  exact .lam (request _ 0) ⟨.refl _, SignedStructural.row_refl _⟩

/-- Signed boundaries cancel in the callback body while retaining its latent
request row. The separate transport equation below concerns a returned closure. -/
theorem callback_boundary_roundtrip_generated :
    generate view contract []
      (.lam (.boundary (.release 0 allowNone)
        (.boundary (.protect 0 allowNone) (.request 0 (.lit .unit)))))
      (Comp.pure M (Comp.arrow M pureUnit (unitTy, [raw 0]))) := by
  apply (principal_exact _ _).mpr
  apply Typing.lam (a := pureUnit) (b := (unitTy, [raw 0]))
  · apply Typing.boundary (input := (unitTy, [protect 0 allowNone (raw 0)]))
    · apply Typing.boundary (input := (unitTy, [raw 0])) (request _ 0)
      · exact .refl _
      · exact SignedStructural.row_refl _
    · exact .refl _
    · change SignedStructural.RowLe [release 0 allowNone (protect 0 allowNone (raw 0))] [raw 0]
      rw [release_protect]
      exact SignedStructural.row_refl _
  · exact ⟨.refl _, SignedStructural.row_refl _⟩

/-- Existing explicit higher-order transport restores the callback after a
protect/release round trip. This does not assert that Core.boundary inserts it. -/
theorem callback_transport_roundtrip :
    OperationalTransportExamples.invokePair
      (OperationalTransport.tree 0 allowNone OperationalTransportExamples.PairShape .release
        OperationalTransportExamples.protectedPair) =
      OperationalTransportExamples.invokePair
        (OperationalTyping.eval OperationalTyping.Env.nil OperationalTransportExamples.callbackPair) :=
  OperationalTransportExamples.returned_pair_roundtrip_restores_callback

end Yulang.Core.EffectTyping.Examples
