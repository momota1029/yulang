import Yulang.CertifiedRowSummaries

/-!
# Exact erasure of guards unreachable in the erased graph

Head guards are executed before creating a seed edge. A sufficient condition
for erasing slot-edge guards is that none of their forbidden inputs is reachable
in the erased graph. This condition concerns each intermediate source state,
not merely the final displacement. It admits arbitrary branching, signed cycles and infinite
sets of reachable weights, with no externally supplied affine potential.

The semilinear presentation of the erased graph makes this a finite family of
semilinear nonmembership questions. This module proves the reduction and exact
transport to the original row AST. The executable membership layer is separate.
-/

namespace Yulang.GuardedRowErasure

open Directed (Occurrence raw)
open FinitePointGuards (GuardedEdge GuardedGraph GuardedReachable)
open RowTransportNormalForm (NormalForm)
open SemilinearWeights (Weight Semi Meaning zero add)
open GuardedAffineRows (weightedGraph weightedEdge mem_weightedGraph)

variable {n : Nat} {Key Slot : Type}

/-- A source configuration forbidden by any slot edge is unreachable even
after all slot guards have been erased. Failed head guards remain disabled. -/
def Harmless [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key) : Prop :=
  ∀ (source target : Slot) (transport : NormalForm n Key),
    (⟨.slot source, transport, target⟩ : GuardedEdge n Key Slot) ∈ graph →
    ∀ point ∈ transport.excluded, point.key = key →
      ¬ WeightedPaths.Path (weightedGraph graph key) none (some source) point.weights

def State [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key) :
    Option Slot → Weight n → Prop
  | none, weight => weight = zero
  | some slot, weight => GuardedReachable graph slot ⟨key, weight⟩

theorem edge_state [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (harmless : Harmless graph key) (original : GuardedEdge n Key Slot)
    (declared : original ∈ graph) (edge : WeightedPaths.Edge n (Option Slot))
    (selected : weightedEdge key original = some edge)
    (initial : Weight n) (state : State graph key edge.source initial) :
    State graph key edge.target (add initial edge.weight) := by
  cases original with
  | mk source transport target =>
      cases source with
      | slot source =>
          cases Option.some.inj selected
          have absent : (⟨key, initial⟩ : Occurrence n Key) ∉ transport.excluded := by
            intro member
            exact harmless source target transport declared _ member rfl
              (GuardedAffineRows.guarded_path graph key state rfl)
          have execution : transport.run ⟨key, initial⟩ =
              some ⟨key, add initial transport.displacement⟩ := by
            simp only [NormalForm.run, absent, ↓reduceIte]
            rfl
          exact GuardedReachable.step declared state execution
      | head sourceKey =>
          by_cases same : sourceKey = key
          · subst sourceKey
            cases execution : transport.run (raw key) with
            | none => simp [weightedEdge, execution] at selected
            | some output =>
                simp only [weightedEdge, ↓reduceIte, execution] at selected
                cases Option.some.inj selected
                change initial = zero at state
                subst initial
                simp only [SemilinearWeights.zero_add]
                have sameOutput : output = ⟨key, output.weights⟩ := by
                  apply Occurrence.ext
                  · exact GuardedAffineRows.normal_run_key (input := raw key) execution
                  · intro index; rfl
                change GuardedReachable graph target ⟨key, output.weights⟩
                rw [← sameOutput]
                exact GuardedReachable.head declared execution
          · simp [weightedEdge, same] at selected

theorem path_state [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (harmless : Harmless graph key) {first last : Option Slot} {weight : Weight n}
    (path : WeightedPaths.Path (weightedGraph graph key) first last weight) :
    ∀ initial, State graph key first initial →
      State graph key last (add initial weight) := by
  induction path with
  | nil vertex => intro initial state; simpa using state
  | @cons edge target rest member path ih =>
      intro initial state
      obtain ⟨original, declared, selected⟩ := (mem_weightedGraph graph key edge).mp member
      have next := edge_state graph key harmless original declared edge selected initial state
      simpa only [SemilinearWeights.add_assoc] using ih (add initial edge.weight) next

/-- A harmless guard is never crossed at an excluded point. This proves the
converse to the unconditional overapproximation by erased paths. -/
theorem paths_exact [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (harmless : Harmless graph key) (slot : Slot) (weight : Weight n) :
    WeightedPaths.Path (weightedGraph graph key) none (some slot) weight ↔
      GuardedReachable graph slot ⟨key, weight⟩ := by
  constructor
  · intro path
    have reached := path_state graph key harmless path zero rfl
    simpa only [State, SemilinearWeights.zero_add] using reached
  · intro reached
    exact GuardedAffineRows.guarded_path graph key reached rfl

theorem summary_exact [DecidableEq Key] [DecidableEq Slot]
    (graph : GuardedGraph n Key Slot) (key : Key) (harmless : Harmless graph key)
    (slot : Slot) (weight : Weight n) :
    Meaning (GuardedAffineRows.summary graph key slot) weight ↔
      GuardedReachable graph slot ⟨key, weight⟩ := by
  rw [GuardedAffineRows.summary, WeightedPaths.solveFinite_exact]
  exact paths_exact graph key harmless slot weight

/-- Directly preserve the original input row problem, not just a problem
constructed by re-encoding a separately supplied graph. -/
theorem original_summary_exact [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key)
    (harmless : Harmless (CertifiedRowSummaries.normalizedProblem key problem) key)
    (slot : Slot) (weight : Weight n) :
    Meaning (CertifiedRowSummaries.summary problem key slot) weight ↔
      RecursiveRows.Derives problem slot ⟨key, weight⟩ :=
  (summary_exact _ key harmless slot weight).trans
    (CertifiedRowSummaries.normalized_derives_exact key problem slot ⟨key, weight⟩ rfl)

/-- Every previously accepted coordinate/potential certificate satisfies this
more general reachability condition. No certificate needs to be supplied to
the eventual semilinear nonmembership checker. -/
theorem harmless_of_certified [DecidableEq Key] (graph : GuardedGraph n Key Slot)
    (key : Key) (coordinate : Fin n) (potential : Slot → Int)
    (certified : GuardedAffineRows.Certified graph key coordinate potential) :
    Harmless graph key := by
  intro source target transport declared point member same path
  have certifiedEdge := certified ⟨.slot source, transport, target⟩ declared
  change transport.displacement coordinate + potential source = potential target ∧
    (∀ point ∈ transport.excluded, point.key ≠ key ∨ point.weights coordinate ≠ potential source)
    at certifiedEdge
  have reached := GuardedAffineRows.path_state graph key coordinate potential certified path zero rfl
  have height : point.weights coordinate = potential source := by
    simpa only [SemilinearWeights.zero_add] using reached.2
  rcases certifiedEdge.2 point member with wrongKey | wrongHeight
  · exact wrongKey same
  · exact wrongHeight height

end Yulang.GuardedRowErasure
