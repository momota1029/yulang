import Yulang.GeneralDeclarativeI65I74NativeProducerGrammar465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open CommonRecursiveNominalIntervals (Endpoint Bounds)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessNativeOrder362 (node)

def matchesNode : Code → Endpoint Nat → Bool
  | .leaf n, .ordinary (.var m) => decide (n = m)
  | .nullary k, .nominal j [] => decide (k = j)
  | .unary k c, .nominal j [.inl (.point p)] =>
    decide (k = j) && matchesNode c p
  | _,_ => false

theorem checked_compiler_node_recovers_exact_endpoint (c : Code) (e : Endpoint Nat) :
    matchesNode c e = true ↔ node c = e := by
  induction c generalizing e with
  | leaf n =>
    cases e with
    | ordinary t => cases t <;> simp [matchesNode,node]
    | nominal => simp [matchesNode,node]
  | nullary k =>
    cases e with
    | ordinary => simp [matchesNode,node]
    | nominal j children =>
      cases children <;> simp [matchesNode,node]
  | unary k c ih =>
    cases e with
    | ordinary => simp [matchesNode,node]
    | nominal j xs =>
      cases xs with
      | nil => simp [matchesNode,node]
      | cons x rest =>
        cases rest with
        | cons _ _ => simp [matchesNode,node]
        | nil =>
          cases x with
          | inr => simp [matchesNode,node]
          | inl span =>
            cases span with
            | point child => simp [matchesNode,node,ih]
            | interval _ _ => simp [matchesNode,node]

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465
