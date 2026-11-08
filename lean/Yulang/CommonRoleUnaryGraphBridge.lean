import Yulang.CommonRoleGraphBisimulation
import Yulang.Common

/-!
# A source-carrier bridge for finite unary variant graphs

This fragment connects the graph observations used by K2 to the existing
Common regular carrier. It covers arbitrary finite graphs whose nodes are
unary variants. Records, merged rows, nominal metadata, and open bounds are
not modeled by this bridge.
-/
namespace Yulang.CommonRoleUnaryGraphBridge

open CommonRoleRegularGraph CommonRoleGraphBisimulation

abbrev UnaryGraph (n : Nat) := Fin n → Nat × Fin n

def graph (source : UnaryGraph n) : Graph n := fun node =>
  .structural (source node).1 [(source node).2]

def body (source : UnaryGraph n) :
    Fin n → CommonSyntax.Layer Common.Row (Fin n ⊕ CommonSyntax.State Common.Row) := fun node =>
  .variant (source node).1 (.inl (source node).2)

def common (source : UnaryGraph n) (node : Fin n) : Common.Ty :=
  CommonSyntax.graph Common.Row (CommonSyntax.closeBlock (body source) node)

def finite (source : UnaryGraph n) : Nat → Fin n → CommonFinite.Ty Common.Row
  | 0, _ => .bottom
  | depth + 1, node => .variant (source node).1 (finite source depth (source node).2)

def viewFinite : View → CommonFinite.Ty Common.Row
  | .structural name [child] => .variant name (viewFinite child)
  | _ => .bottom
termination_by view => sizeOf view

theorem graph_observe (source : UnaryGraph n) (depth : Nat) (node : Fin n) :
    viewFinite (observe (graph source) depth node) = finite source depth node := by
  induction depth generalizing node with
  | zero => simp [observe, viewFinite, finite]
  | succ depth ih => simp [observe, graph, viewFinite, finite, ih]

theorem block_observe (source : UnaryGraph n) (depth : Nat) (node : Fin n) :
    CommonSyntax.observe (CommonSyntax.blockGraph (body source)) depth (.inl node) = finite source depth node := by
  induction depth generalizing node with
  | zero => rfl
  | succ depth ih =>
      simp [CommonSyntax.observe, CommonSyntax.blockGraph, body, CommonSyntax.Layer.evalAt, finite, ih]

theorem common_observe (source : UnaryGraph n) (depth : Nat) (node : Fin n) :
    Common.observeTy depth (common source node) = finite source (depth + 1) node := by
  change CommonSyntax.observe (CommonSyntax.graph Common.Row) (depth + 1)
      (CommonSyntax.blockRef (body source) (.inl node)) = _
  rw [CommonSyntax.block_observe_exact]
  exact block_observe source (depth + 1) node

/-- Bisimilar graph nodes produce equivalent Common regular types. -/
theorem bisimilar_common (source : UnaryGraph n) (first last : Fin n)
    (related : bisimilar (graph source) first last = true) :
    Common.Equivalent (common source first) (common source last) := by
  have same (depth : Nat) : Common.observeTy depth (common source first) =
      Common.observeTy depth (common source last) := by
    rw [common_observe, common_observe, ← graph_observe, ← graph_observe]
    exact congrArg viewFinite (bisimilar_observations (graph source) first last related (depth + 1))
  constructor <;> intro depth <;> rw [same depth] <;> exact CommonFinite.producerLe_refl _

/-- One finite unrolling of the unary variant loop is Common-equivalent to
the loop node, and is recognized as regular despite not being an identity
cycle itself. This is a graph observation, not a whole-resolver result. -/
def unrolledLoop : UnaryGraph 2 := fun _ => (7, 1)

theorem unrolled_loop_common :
    recursiveAt (graph unrolledLoop) 0 = false ∧
    regularAt (graph unrolledLoop) 0 = true ∧
    Common.Equivalent (common unrolledLoop 0) (common unrolledLoop 1) := by
  refine ⟨?_, ?_, bisimilar_common unrolledLoop 0 1 ?_⟩ <;> decide +kernel

end Yulang.CommonRoleUnaryGraphBridge
