import Yulang.CommonEffectRequestGeneration
import Yulang.MultiOperationPayloadHandlers

/-! Finite resolved handler-arm coverage metadata. Payload elaboration and
its bindings belong to the pattern layer. This records precisely the static
distinction already used by CoreEffectTyping: only an unguarded irrefutable
arm may subtract its operation key. It does not inspect a semantic test. -/
namespace Yulang.CommonEffectArmCoverage

inductive PayloadCoverage where
  | irrefutable
  | refutable
  deriving DecidableEq, Repr

structure Arm where
  operation : Nat
  payload : PayloadCoverage
  guarded : Bool
  deriving DecidableEq, Repr

def Arm.total (arm : Arm) : Bool :=
  match arm.payload with
  | .irrefutable => !arm.guarded
  | .refutable => false

def ofResolved (operation : Nat) (arm : MultiOperationPayloadHandlers.Arm Nat Payload) : Arm :=
  ⟨operation, match arm.pattern with | .irrefutable => .irrefutable | .test _ => .refutable, arm.guard.isSome⟩

theorem ofResolved_total (operation : Nat) (arm : MultiOperationPayloadHandlers.Arm Nat Payload) :
    (ofResolved operation arm).total = arm.total := by
  cases arm with
  | mk key pattern guard => cases pattern <;> cases guard <;> rfl

@[simp] theorem ofResolved_operation (operation : Nat) (arm : MultiOperationPayloadHandlers.Arm Nat Payload) :
    (ofResolved operation arm).operation = operation := rfl

def removedKeys (keys : Fin count → Nat) (arms : Fin count → Arm) : List Nat :=
  ((List.finRange count).filter (fun i => (arms i).total)).map keys

theorem mem_removedKeys (keys : Fin count → Nat) (arms : Fin count → Arm) (key : Nat) :
    key ∈ removedKeys keys arms ↔ ∃ i, (arms i).total = true ∧ keys i = key := by
  simp [removedKeys]

theorem resolved_removedKeys (operations : Fin count → Nat) (arms : Fin count → MultiOperationPayloadHandlers.Arm Nat Payload) :
    removedKeys (fun i => (arms i).key) (fun i => ofResolved (operations i) (arms i)) =
      MultiOperationPayloadHandlers.removedKeys arms := by
  simp only [removedKeys, ofResolved_total, MultiOperationPayloadHandlers.removedKeys]
end Yulang.CommonEffectArmCoverage
