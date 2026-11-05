import Yulang.RowTransportNormalForm
import Yulang.WeightedPaths

/-!
# Finite semilinear presentations of unguarded recursive row solutions

For a fixed operation key, normalize every compiled transport program. If all
exclusion lists are empty, every edge is an unconditional integer translation.
Matching head edges start at a fresh seed vertex; slot edges connect row
variables. The seed has no incoming edge, so every path from that seed to a row
vertex contains exactly one head and never adds the weights of unrelated seeds.

The resulting weighted paths agree with the existing guarded `Reachable`
relation and hence with the original `RecursiveRows.Derives`, including all
coordinates, negative weights, arbitrary finite paths and mutual recursion.
Finite state elimination then produces a semilinear presentation of the actual
least solution. A checked entry point returns no unguarded summary when any
point guard remains for this key. This does not decide membership/inclusion of arbitrary
semilinear sets or guarded recursive row graphs.
-/

namespace Yulang.SemilinearRows

open Directed
open SemilinearWeights (Weight Semi add zero)
open RecursiveRowGraph (Program Graph Reachable)
open RowTransportNormalForm (normalize)

variable {n : Nat} {Key Slot : Type}

def occurrence (key : Key) (weights : Weight n) : Occurrence n Key := ⟨key, weights⟩

def Unguarded [DecidableEq Key] (key : Key) (graph : Graph n Key Slot) : Prop :=
  ∀ edge ∈ graph, (normalize key edge.program).excluded = []

def checkUnguarded [DecidableEq Key] (key : Key) (graph : Graph n Key Slot) : Bool :=
  graph.all fun edge => (normalize key edge.program).excluded.isEmpty

theorem checkUnguarded_exact [DecidableEq Key] (key : Key) (graph : Graph n Key Slot) :
    checkUnguarded key graph = true ↔ Unguarded key graph := by
  simp [checkUnguarded, Unguarded]

def weightedEdge [DecidableEq Key] (key : Key) (edge : RecursiveRowGraph.Edge n Key Slot) :
    Option (WeightedPaths.Edge n (Option Slot)) :=
  match edge.source with
  | .head original =>
      if original = key then some ⟨none, some edge.target, (normalize key edge.program).displacement⟩
      else none
  | .slot source => some ⟨some source, some edge.target, (normalize key edge.program).displacement⟩

def weightedGraph [DecidableEq Key] (key : Key) (graph : Graph n Key Slot) :
    WeightedPaths.Graph n (Option Slot) := graph.filterMap (weightedEdge key)

theorem weighted_head_mem [DecidableEq Key] (key : Key) (graph : Graph n Key Slot)
    (program : Program n Key) (target : Slot)
    (member : ⟨.head key, program, target⟩ ∈ graph) :
    (⟨none, some target, (normalize key program).displacement⟩ : WeightedPaths.Edge n (Option Slot)) ∈
      weightedGraph key graph :=
  List.mem_filterMap.mpr ⟨⟨.head key, program, target⟩, member, by simp [weightedEdge]⟩

theorem weighted_slot_mem [DecidableEq Key] (key : Key) (graph : Graph n Key Slot)
    (source target : Slot) (program : Program n Key)
    (member : ⟨.slot source, program, target⟩ ∈ graph) :
    (⟨some source, some target, (normalize key program).displacement⟩ : WeightedPaths.Edge n (Option Slot)) ∈
      weightedGraph key graph :=
  List.mem_filterMap.mpr ⟨⟨.slot source, program, target⟩, member, rfl⟩

theorem run_unguarded [DecidableEq Key] (key : Key) (program : Program n Key)
    (free : (normalize key program).excluded = []) (weights : Weight n) :
    Program.run program (occurrence key weights) =
      some (occurrence key (add weights (normalize key program).displacement)) := by
  apply (RowTransportNormalForm.execution_normal_form key program _ _ rfl).mpr
  exact ⟨by simp [free], rfl⟩

theorem execution_weights [DecidableEq Key] (key : Key) (program : Program n Key)
    (input output : Occurrence n Key) (sameKey : input.key = key)
    (execution : Program.run program input = some output) :
    output.weights = add input.weights (normalize key program).displacement := by
  have form := (RowTransportNormalForm.execution_normal_form key program input output sameKey).mp execution
  rw [form.2]
  rfl

/-- Forgetting point guards is always a sound overapproximation. The converse
below requires their normalized exclusion lists to be empty. -/
theorem reachable_to_path [DecidableEq Key] (key : Key) (graph : Graph n Key Slot)
    {target : Slot} {output : Occurrence n Key} (reached : Reachable graph target output)
    (sameKey : output.key = key) :
    WeightedPaths.Path (weightedGraph key graph) none (some target) output.weights := by
  induction reached with
  | @head output original program target member execution =>
      have same : original = key :=
        (Program.run_key program (raw original) output execution).symm.trans sameKey
      subst original
      have weights := execution_weights key program (raw key) output rfl execution
      have weightForm : output.weights = (normalize key program).displacement := by
        change output.weights = add zero (normalize key program).displacement at weights
        simpa only [SemilinearWeights.zero_add] using weights
      rw [weightForm]
      exact WeightedPaths.Path.single (weighted_head_mem key graph program target member)
  | @step input output source target program member reached execution ih =>
      have previousKey : input.key = key := (Program.run_key program input output execution).symm.trans sameKey
      rw [execution_weights key program input output previousKey execution]
      exact (ih previousKey).append
        (WeightedPaths.Path.single (weighted_slot_mem key graph source target program member))

/-- The fresh seed can hold only zero; an ordinary vertex holds precisely an
already established occurrence in the original recursive-row graph. -/
def State [DecidableEq Key] (key : Key) (graph : Graph n Key Slot) : Option Slot → Weight n → Prop
  | none, weights => weights = zero
  | some slot, weights => Reachable graph slot (occurrence key weights)

theorem weighted_edge_preserves_state [DecidableEq Key] (key : Key) (graph : Graph n Key Slot)
    (free : Unguarded key graph) (edge : WeightedPaths.Edge n (Option Slot))
    (member : edge ∈ weightedGraph key graph) (weights : Weight n)
    (initial : State key graph edge.source weights) :
    State key graph edge.target (add weights edge.weight) := by
  obtain ⟨original, declared, converted⟩ := List.mem_filterMap.mp member
  rcases original with ⟨source, program, target⟩
  cases source with
  | head original =>
      by_cases same : original = key
      · subst original
        have equality : (⟨none, some target, (normalize key program).displacement⟩ :
            WeightedPaths.Edge n (Option Slot)) = edge := by simpa [weightedEdge] using converted
        cases equality
        change weights = zero at initial
        subst weights
        exact Reachable.head declared (run_unguarded key program (free _ declared) zero)
      · simp [weightedEdge, same] at converted
  | slot source =>
      have equality : (⟨some source, some target, (normalize key program).displacement⟩ :
          WeightedPaths.Edge n (Option Slot)) = edge := Option.some.inj converted
      cases equality
      exact Reachable.step declared initial (run_unguarded key program (free _ declared) weights)

theorem path_preserves_state [DecidableEq Key] (key : Key) (graph : Graph n Key Slot)
    (free : Unguarded key graph) {source target : Option Slot} {displacement : Weight n}
    (path : WeightedPaths.Path (weightedGraph key graph) source target displacement)
    (weights : Weight n) (initial : State key graph source weights) :
    State key graph target (add weights displacement) := by
  induction path generalizing weights with
  | nil => simpa using initial
  | cons member path ih =>
      have next := weighted_edge_preserves_state key graph free _ member weights initial
      simpa only [SemilinearWeights.add_assoc] using ih _ next

theorem path_reachable_exact [DecidableEq Key] (key : Key) (graph : Graph n Key Slot)
    (free : Unguarded key graph) (target : Slot) (weights : Weight n) :
    WeightedPaths.Path (weightedGraph key graph) none (some target) weights ↔
      Reachable graph target (occurrence key weights) := by
  constructor
  · intro path
    have result := path_preserves_state key graph free path zero rfl
    simpa only [SemilinearWeights.zero_add, State] using result
  · intro reached
    exact reachable_to_path key graph reached rfl

theorem path_derives_exact [DecidableEq Key] (key : Key) (problem : RecursiveRows.Problem n Key Slot)
    (free : Unguarded key (RecursiveRowGraph.compile problem)) (target : Slot) (weights : Weight n) :
    WeightedPaths.Path (weightedGraph key (RecursiveRowGraph.compile problem)) none (some target) weights ↔
      RecursiveRows.Derives problem target (occurrence key weights) :=
  (path_reachable_exact key _ free target weights).trans
    (RecursiveRowGraph.reachable_iff_derives problem target _)

def vertices (slots : List Slot) : List (Option Slot) := none :: slots.map some

theorem vertices_complete (slots : List Slot) (complete : ∀ slot, slot ∈ slots) :
    ∀ vertex, vertex ∈ vertices slots := by
  intro vertex
  cases vertex with
  | none => simp [vertices]
  | some slot => simp [vertices, complete slot]

def presentation [DecidableEq Key] [DecidableEq Slot] (key : Key) (slots : List Slot)
    (problem : RecursiveRows.Problem n Key Slot) (target : Slot) : Semi n :=
  WeightedPaths.solve (vertices slots) (weightedGraph key (RecursiveRowGraph.compile problem)) none (some target)

/-- The finite semilinear result represents the original least row solution,
not merely a chosen post-fixed point or a bounded path enumeration. -/
theorem presentation_exact [DecidableEq Key] [DecidableEq Slot] (key : Key) (slots : List Slot)
    (complete : ∀ slot, slot ∈ slots) (problem : RecursiveRows.Problem n Key Slot)
    (free : Unguarded key (RecursiveRowGraph.compile problem)) (target : Slot) (weights : Weight n) :
    SemilinearWeights.Meaning (presentation key slots problem target) weights ↔
      RecursiveRows.Derives problem target (occurrence key weights) :=
  (WeightedPaths.solve_exact (vertices slots) (vertices_complete slots complete) _ none (some target) weights).trans
    (path_derives_exact key problem free target weights)

def summarize [DecidableEq Key] [DecidableEq Slot] (key : Key) (slots : List Slot)
    (problem : RecursiveRows.Problem n Key Slot) (target : Slot) : Option (Semi n) :=
  if checkUnguarded key (RecursiveRowGraph.compile problem) then
    some (presentation key slots problem target)
  else none

theorem summarize_accepts_iff [DecidableEq Key] [DecidableEq Slot] (key : Key) (slots : List Slot)
    (problem : RecursiveRows.Problem n Key Slot) (target : Slot) :
    (∃ result, summarize key slots problem target = some result) ↔
      Unguarded key (RecursiveRowGraph.compile problem) := by
  simp [summarize, ← checkUnguarded_exact]

theorem summarize_exact [DecidableEq Key] [DecidableEq Slot] (key : Key) (slots : List Slot)
    (complete : ∀ slot, slot ∈ slots) (problem : RecursiveRows.Problem n Key Slot)
    (target : Slot) (result : Semi n) (accepted : summarize key slots problem target = some result)
    (weights : Weight n) :
    SemilinearWeights.Meaning result weights ↔
      RecursiveRows.Derives problem target (occurrence key weights) := by
  have free := (summarize_accepts_iff key slots problem target).mp ⟨result, accepted⟩
  have checked := (checkUnguarded_exact key _).mpr free
  have same : presentation key slots problem target = result := by simpa [summarize, checked] using accepted
  rw [← same]
  exact presentation_exact key slots complete problem free target weights

/-- No global enumeration of the slot identifier type is needed: the compiled
finite graph supplies all intermediate vertices used by state elimination. -/
def presentationFinite [DecidableEq Key] [DecidableEq Slot] (key : Key)
    (problem : RecursiveRows.Problem n Key Slot) (target : Slot) : Semi n :=
  WeightedPaths.solveFinite (weightedGraph key (RecursiveRowGraph.compile problem)) none (some target)

theorem presentationFinite_exact [DecidableEq Key] [DecidableEq Slot] (key : Key)
    (problem : RecursiveRows.Problem n Key Slot)
    (free : Unguarded key (RecursiveRowGraph.compile problem)) (target : Slot) (weights : Weight n) :
    SemilinearWeights.Meaning (presentationFinite key problem target) weights ↔
      RecursiveRows.Derives problem target (occurrence key weights) :=
  (WeightedPaths.solveFinite_exact _ none (some target) weights).trans
    (path_derives_exact key problem free target weights)

def summarizeFinite [DecidableEq Key] [DecidableEq Slot] (key : Key)
    (problem : RecursiveRows.Problem n Key Slot) (target : Slot) : Option (Semi n) :=
  if checkUnguarded key (RecursiveRowGraph.compile problem) then
    some (presentationFinite key problem target)
  else none

theorem summarizeFinite_exact [DecidableEq Key] [DecidableEq Slot] (key : Key)
    (problem : RecursiveRows.Problem n Key Slot) (target : Slot) (result : Semi n)
    (accepted : summarizeFinite key problem target = some result) (weights : Weight n) :
    SemilinearWeights.Meaning result weights ↔
      RecursiveRows.Derives problem target (occurrence key weights) := by
  unfold summarizeFinite at accepted
  split at accepted
  next checked =>
    have same := Option.some.inj accepted
    rw [← same]
    exact presentationFinite_exact key problem ((checkUnguarded_exact key _).mp checked) target weights
  next => cases accepted

end Yulang.SemilinearRows
