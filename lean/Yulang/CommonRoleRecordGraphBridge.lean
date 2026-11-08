import Yulang.CommonRoleGraphBisimulation
import Yulang.CommonRoleGraphInspectionExamples
import Yulang.Common

/-!
# A source-carrier bridge for finite one-field record graphs

Each graph node represents a Common required-field type, retaining its field
label and payload edge, with the fixed width tail `emptyRecord`. This covers
arbitrary finite regular graphs in that fragment, including the
`box`/recursive-`next` shape in K2. It does not cover arbitrary record tails,
hidden fields, variants, nominal types, or full role resolution.
-/
namespace Yulang.CommonRoleRecordGraphBridge

open CommonRoleRegularGraph CommonRoleGraphBisimulation

abbrev RecordGraph (n : Nat) := Fin n → Nat × Fin n

def graph (source : RecordGraph n) : Graph n := fun node =>
  .structural (source node).1 [(source node).2]

def body (source : RecordGraph n) :
    Fin n → CommonSyntax.Layer Common.Row (Fin n ⊕ CommonSyntax.State Common.Row) := fun node =>
  .record (source node).1 (.inl (source node).2) .emptyRecord

def common (source : RecordGraph n) (node : Fin n) : Common.Ty :=
  CommonSyntax.graph Common.Row (CommonSyntax.closeBlock (body source) node)

def finite (source : RecordGraph n) : Nat → Fin n → CommonFinite.Ty Common.Row
  | 0, _ => .bottom
  | depth + 1, node => CommonFinite.required (source node).1 (finite source depth (source node).2)

def viewFinite : View → CommonFinite.Ty Common.Row
  | .structural name [child] => CommonFinite.required name (viewFinite child)
  | _ => .bottom
termination_by view => sizeOf view

theorem graph_observe (source : RecordGraph n) (depth : Nat) (node : Fin n) :
    viewFinite (observe (graph source) depth node) = finite source depth node := by
  induction depth generalizing node with
  | zero => simp [observe, viewFinite, finite]
  | succ depth ih => simp [observe, graph, viewFinite, finite, ih]

theorem block_observe (source : RecordGraph n) (depth : Nat) (node : Fin n) :
    CommonSyntax.observe (CommonSyntax.blockGraph (body source)) depth (.inl node) = finite source depth node := by
  induction depth generalizing node with
  | zero => rfl
  | succ depth ih =>
      simp [CommonSyntax.observe, CommonSyntax.blockGraph, body, CommonSyntax.Layer.evalAt,
        CommonFinite.required, finite, ih]

theorem common_observe (source : RecordGraph n) (depth : Nat) (node : Fin n) :
    Common.observeTy depth (common source node) = finite source (depth + 1) node := by
  change CommonSyntax.observe (CommonSyntax.graph Common.Row) (depth + 1)
      (CommonSyntax.blockRef (body source) (.inl node)) = _
  rw [CommonSyntax.block_observe_exact]
  exact block_observe source (depth + 1) node

/-- The Common meaning at a node unfolds to that node's original required
field and the Common meaning of its original payload node. -/
theorem common_unfold (source : RecordGraph n) (node : Fin n) :
    Common.Equivalent (common source node)
      (Common.required (source node).1 (common source (source node).2)) := by
  have equal (depth : Nat) :
      Common.observeTy depth (common source node) =
        Common.observeTy depth (Common.required (source node).1 (common source (source node).2)) := by
    cases depth with
    | zero =>
        rw [common_observe]
        rfl
    | succ depth =>
        rw [common_observe]
        change CommonFinite.required (source node).1 (finite source (depth + 1) (source node).2) =
          CommonFinite.required (source node).1 (Common.observeTy depth (common source (source node).2))
        rw [common_observe]
  constructor <;> intro depth <;> rw [equal depth] <;> exact CommonFinite.producerLe_refl _

theorem bisimilar_common (source : RecordGraph n) (first last : Fin n)
    (related : bisimilar (graph source) first last = true) :
    Common.Equivalent (common source first) (common source last) := by
  have same (depth : Nat) : Common.observeTy depth (common source first) =
      Common.observeTy depth (common source last) := by
    rw [common_observe, common_observe, ← graph_observe, ← graph_observe]
    exact congrArg viewFinite (bisimilar_observations (graph source) first last related (depth + 1))
  constructor <;> intro depth <;> rw [same depth] <;> exact CommonFinite.producerLe_refl _

/-- The type `μ = {next: μ}` has the same Common meaning after one explicit
unrolling, and the unrolled description is recognized as regular. -/
def unrolledLoop : RecordGraph 2 := fun _ => (1, 1)

theorem unrolled_loop_common :
    recursiveAt (graph unrolledLoop) 0 = false ∧
    regularAt (graph unrolledLoop) 0 = true ∧
    Common.Equivalent (common unrolledLoop 0) (common unrolledLoop 1) := by
  refine ⟨?_, ?_, bisimilar_common unrolledLoop 0 1 ?_⟩ <;> decide +kernel

/-- The exact lower-head graph used for the boxed K2 inspection example. -/
def boxedLoopSource : RecordGraph 2 := fun node =>
  if node = 0 then (0, 1) else (1, 1)

theorem boxed_loop_graph : graph boxedLoopSource = CommonRoleGraphInspectionExamples.boxedLoop := by
  funext node
  by_cases same : node = 0 <;>
    simp [graph, boxedLoopSource, CommonRoleGraphInspectionExamples.boxedLoop, same]

theorem boxed_loop_unfolds :
    Common.Equivalent (common boxedLoopSource 0) (Common.required 0 (common boxedLoopSource 1)) ∧
      Common.Equivalent (common boxedLoopSource 1) (Common.required 1 (common boxedLoopSource 1)) ∧
      regularAt (graph boxedLoopSource) 0 = false ∧ regularAt (graph boxedLoopSource) 1 = true := by
  refine ⟨common_unfold boxedLoopSource 0, common_unfold boxedLoopSource 1, ?_, ?_⟩ <;> decide +kernel

end Yulang.CommonRoleRecordGraphBridge
