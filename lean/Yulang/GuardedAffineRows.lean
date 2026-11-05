import Yulang.FinitePointGuards
import Yulang.WeightedPaths

/-!
# Checked affine certificates for harmless finite point guards

For a fixed operation key, a supplied coordinate and slot potential define an
affine invariant: that coordinate always equals the potential of the current
slot. A finite check verifies every slot-edge translation and that every
excluded point either has another key or lies outside this invariant. Head
edges run their actual guard on the raw occurrence: failed heads are omitted,
successful heads must establish the target invariant, and other keys are
ignored.

When the certificate passes, erasing the guards preserves all paths, including
arbitrary branching and interacting positive or negative cycles. The resulting
weighted graph has an executable finite semilinear summary, exactly equal to
`RecursiveRows.Derives` for the original embedded row problem.

This is one checked certificate family. It neither searches for certificates
nor decides general guarded reachability. Failed certificates return
`unsupported`; they do not reject a language program. No path-length, weight,
or cycle-count bound is imposed.
-/

namespace Yulang.GuardedAffineRows

open Directed (Occurrence raw)
open FinitePointGuards
open RowTransportNormalForm (NormalForm translate)
open RecursiveRowGraph (Source)
open SemilinearWeights (Weight Semi zero add Meaning)

variable {n : Nat} {Key Slot : Type}

theorem normal_run_output [DecidableEq Key] {normal : NormalForm n Key}
    {input output : Occurrence n Key} (execution : normal.run input = some output) :
    output = translate normal.displacement input := by
  unfold NormalForm.run at execution
  split at execution
  · cases execution
  · exact (Option.some.inj execution).symm

theorem normal_run_key [DecidableEq Key] {normal : NormalForm n Key}
    {input output : Occurrence n Key} (execution : normal.run input = some output) :
    output.key = input.key := by
  rw [normal_run_output execution]
  rfl

theorem normal_run_weights [DecidableEq Key] {normal : NormalForm n Key}
    {input output : Occurrence n Key} (execution : normal.run input = some output) :
    output.weights = add input.weights normal.displacement := by
  rw [normal_run_output execution]
  rfl

def EdgeInvariant [DecidableEq Key] (key : Key) (coordinate : Fin n) (potential : Slot → Int)
    (edge : GuardedEdge n Key Slot) : Prop :=
  match edge.source with
  | .slot source =>
      edge.transport.displacement coordinate + potential source = potential edge.target ∧
        ∀ point ∈ edge.transport.excluded,
          point.key ≠ key ∨ point.weights coordinate ≠ potential source
  | .head sourceKey => sourceKey = key → ∀ output,
      edge.transport.run (raw key) = some output → output.weights coordinate = potential edge.target

def checkEdge [DecidableEq Key] (key : Key) (coordinate : Fin n) (potential : Slot → Int)
    (edge : GuardedEdge n Key Slot) : Bool :=
  match edge.source with
  | .slot source =>
      decide (edge.transport.displacement coordinate + potential source = potential edge.target) &&
        edge.transport.excluded.all (fun point =>
          decide (point.key ≠ key ∨ point.weights coordinate ≠ potential source))
  | .head sourceKey =>
      if sourceKey = key then
        match edge.transport.run (raw key) with
        | none => true
        | some output => decide (output.weights coordinate = potential edge.target)
      else true

theorem checkEdge_exact [DecidableEq Key] (key : Key) (coordinate : Fin n)
    (potential : Slot → Int) (edge : GuardedEdge n Key Slot) :
    checkEdge key coordinate potential edge = true ↔ EdgeInvariant key coordinate potential edge := by
  cases edge with
  | mk source transport target =>
      cases source with
      | slot source => simp [checkEdge, EdgeInvariant, List.all_eq_true]
      | head sourceKey =>
          by_cases same : sourceKey = key
          · cases execution : transport.run (raw key) <;>
              simp [checkEdge, EdgeInvariant, same, execution]
          · simp [checkEdge, EdgeInvariant, same]

def Certified [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (coordinate : Fin n) (potential : Slot → Int) : Prop :=
  ∀ edge ∈ graph, EdgeInvariant key coordinate potential edge

def check [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (coordinate : Fin n) (potential : Slot → Int) : Bool :=
  graph.all (checkEdge key coordinate potential)

theorem check_exact [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (coordinate : Fin n) (potential : Slot → Int) :
    check graph key coordinate potential = true ↔ Certified graph key coordinate potential := by
  simp [check, Certified, List.all_eq_true, checkEdge_exact]

/-- `none` is the fresh seed vertex. Every edge targets a real slot. -/
def weightedEdge [DecidableEq Key] (key : Key) (edge : GuardedEdge n Key Slot) :
    Option (WeightedPaths.Edge n (Option Slot)) :=
  match edge.source with
  | .slot source => some ⟨some source, some edge.target, edge.transport.displacement⟩
  | .head sourceKey =>
      if sourceKey = key then
        match edge.transport.run (raw key) with
        | none => none
        | some output => some ⟨none, some edge.target, output.weights⟩
      else none

def weightedGraph [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key) :
    WeightedPaths.Graph n (Option Slot) := graph.filterMap (weightedEdge key)

theorem mem_weightedGraph [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (edge : WeightedPaths.Edge n (Option Slot)) :
    edge ∈ weightedGraph graph key ↔
      ∃ original ∈ graph, weightedEdge key original = some edge := by
  simp only [weightedGraph, List.mem_filterMap]

theorem weightedEdge_target [DecidableEq Key] (key : Key) (original : GuardedEdge n Key Slot)
    (edge : WeightedPaths.Edge n (Option Slot)) (selected : weightedEdge key original = some edge) :
    edge.target = some original.target := by
  cases original with
  | mk source transport target =>
      cases source with
      | slot source =>
          cases Option.some.inj selected
          rfl
      | head sourceKey =>
          by_cases same : sourceKey = key
          · cases execution : transport.run (raw key) <;> simp [weightedEdge, same, execution] at selected
            cases selected
            rfl
          · simp [weightedEdge, same] at selected

theorem no_incoming_seed [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (edge : WeightedPaths.Edge n (Option Slot)) (member : edge ∈ weightedGraph graph key) :
    edge.target ≠ none := by
  obtain ⟨original, _, selected⟩ := (mem_weightedGraph graph key edge).mp member
  rw [weightedEdge_target key original edge selected]
  exact Option.some_ne_none _

theorem guard_passes_on_invariant [DecidableEq Key] (key : Key) (coordinate : Fin n)
    (expected : Int) (normal : NormalForm n Key)
    (separated : ∀ point ∈ normal.excluded, point.key ≠ key ∨ point.weights coordinate ≠ expected)
    (weight : Weight n) (invariant : weight coordinate = expected) :
    normal.run ⟨key, weight⟩ = some ⟨key, add weight normal.displacement⟩ := by
  have absent : (⟨key, weight⟩ : Occurrence n Key) ∉ normal.excluded := by
    intro member
    rcases separated _ member with wrongKey | wrongCoordinate
    · exact wrongKey rfl
    · exact wrongCoordinate invariant
  rw [NormalForm.run, ite_eq_right absent]
  rfl

/-- The seed has zero accumulated weight. Real vertices carry a derivation
using the original guards as well as the affine invariant needed by the next
edge. This state predicate follows the whole path, not its final sum alone. -/
def State [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (coordinate : Fin n) (potential : Slot → Int) : Option Slot → Weight n → Prop
  | none, weight => weight = zero
  | some slot, weight =>
      GuardedReachable graph slot ⟨key, weight⟩ ∧ weight coordinate = potential slot

theorem edge_state [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (coordinate : Fin n) (potential : Slot → Int) (original : GuardedEdge n Key Slot)
    (declared : original ∈ graph) (certified : EdgeInvariant key coordinate potential original)
    (edge : WeightedPaths.Edge n (Option Slot)) (selected : weightedEdge key original = some edge)
    (initial : Weight n) (state : State graph key coordinate potential edge.source initial) :
    State graph key coordinate potential edge.target (add initial edge.weight) := by
  cases original with
  | mk source transport target =>
      cases source with
      | slot source =>
          cases Option.some.inj selected
          obtain ⟨translation, separated⟩ := certified
          obtain ⟨reached, invariant⟩ := state
          refine ⟨GuardedReachable.step declared reached
            (guard_passes_on_invariant key coordinate (potential source) transport separated initial invariant), ?_⟩
          change initial coordinate + transport.displacement coordinate = potential target
          change transport.displacement coordinate + potential source = potential target at translation
          change initial coordinate = potential source at invariant
          omega
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
                  · exact normal_run_key (input := raw key) execution
                  · intro index; rfl
                exact ⟨sameOutput ▸ GuardedReachable.head declared execution,
                  certified rfl output execution⟩
          · simp [weightedEdge, same] at selected

theorem path_state [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (coordinate : Fin n) (potential : Slot → Int) (certified : Certified graph key coordinate potential)
    {first last : Option Slot} {weight : Weight n}
    (path : WeightedPaths.Path (weightedGraph graph key) first last weight) :
    ∀ initial, State graph key coordinate potential first initial →
      State graph key coordinate potential last (add initial weight) := by
  induction path with
  | nil vertex => intro initial state; simpa using state
  | @cons edge target rest member path ih =>
      intro initial state
      obtain ⟨original, declared, selected⟩ := (mem_weightedGraph graph key edge).mp member
      have next := edge_state graph key coordinate potential original declared
        (certified original declared) edge selected initial state
      simpa only [SemilinearWeights.add_assoc] using ih (add initial edge.weight) next

theorem path_guarded [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (coordinate : Fin n) (potential : Slot → Int) (certified : Certified graph key coordinate potential)
    (slot : Slot) (weight : Weight n)
    (path : WeightedPaths.Path (weightedGraph graph key) none (some slot) weight) :
    GuardedReachable graph slot ⟨key, weight⟩ := by
  have state := path_state graph key coordinate potential certified path zero rfl
  simpa only [SemilinearWeights.zero_add] using state.1

theorem guarded_path [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    {slot : Slot} {output : Occurrence n Key} (reached : GuardedReachable graph slot output) :
    output.key = key → WeightedPaths.Path (weightedGraph graph key) none (some slot) output.weights := by
  induction reached with
  | @head output headKey transport target declared execution =>
      intro same
      have sameHead : headKey = key := (normal_run_key execution).symm.trans same
      subst headKey
      apply WeightedPaths.Path.single (edge := ⟨none, some target, output.weights⟩)
      apply (mem_weightedGraph graph key _).mpr
      exact ⟨⟨.head key, transport, target⟩, declared, by simp [weightedEdge, execution]⟩
  | @step input output source target transport declared reached execution ih =>
      intro same
      have inputKey : input.key = key := (normal_run_key execution).symm.trans same
      have first := ih inputKey
      have next : (⟨some source, some target, transport.displacement⟩ : WeightedPaths.Edge n (Option Slot)) ∈
          weightedGraph graph key :=
        (mem_weightedGraph graph key _).mpr ⟨⟨.slot source, transport, target⟩, declared, rfl⟩
      have entire := first.append (WeightedPaths.Path.single next)
      rw [← normal_run_weights execution] at entire
      exact entire

theorem paths_exact [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (coordinate : Fin n) (potential : Slot → Int) (certified : Certified graph key coordinate potential)
    (slot : Slot) (weight : Weight n) :
    WeightedPaths.Path (weightedGraph graph key) none (some slot) weight ↔
      GuardedReachable graph slot ⟨key, weight⟩ :=
  ⟨path_guarded graph key coordinate potential certified slot weight,
    fun reached => guarded_path graph key reached rfl⟩

/-- State elimination obtains its finite vertex support from the graph itself;
the ambient slot identifier type may be infinite. -/
def summary [DecidableEq Key] [DecidableEq Slot] (graph : GuardedGraph n Key Slot)
    (key : Key) (slot : Slot) : Semi n :=
  WeightedPaths.solveFinite (weightedGraph graph key) none (some slot)

theorem summary_exact [DecidableEq Key] [DecidableEq Slot] (graph : GuardedGraph n Key Slot)
    (key : Key) (coordinate : Fin n) (potential : Slot → Int)
    (certified : Certified graph key coordinate potential) (slot : Slot) (weight : Weight n) :
    Meaning (summary graph key slot) weight ↔
      RecursiveRows.Derives (rowProblem graph) slot ⟨key, weight⟩ := by
  rw [summary, WeightedPaths.solveFinite_exact, paths_exact graph key coordinate potential certified]
  exact guarded_graph_exact graph slot ⟨key, weight⟩

inductive Attempt (n : Nat) where
  | unsupported
  | summarized (semi : Semi n)

/-- The finite certificate check is the public gate to guard erasure. Failure
means that this certificate family supplies no answer, not that reachability
or the source program is rejected. -/
def checkedSummary [DecidableEq Key] [DecidableEq Slot] (graph : GuardedGraph n Key Slot)
    (key : Key) (coordinate : Fin n) (potential : Slot → Int) (slot : Slot) : Attempt n :=
  if check graph key coordinate potential then .summarized (summary graph key slot) else .unsupported

theorem checkedSummary_exact [DecidableEq Key] [DecidableEq Slot] (graph : GuardedGraph n Key Slot)
    (key : Key) (coordinate : Fin n) (potential : Slot → Int) (slot : Slot) (semi : Semi n) :
    checkedSummary graph key coordinate potential slot = .summarized semi ↔
      check graph key coordinate potential = true ∧ summary graph key slot = semi := by
  unfold checkedSummary
  split <;> simp_all

theorem checkedSummary_unsupported_iff [DecidableEq Key] [DecidableEq Slot]
    (graph : GuardedGraph n Key Slot) (key : Key) (coordinate : Fin n)
    (potential : Slot → Int) (slot : Slot) :
    checkedSummary graph key coordinate potential slot = .unsupported ↔
      check graph key coordinate potential = false := by
  unfold checkedSummary
  split <;> simp_all

/-- Every accepted executable summary is exact for all integer weight vectors
in the original embedded row problem. No semantic guard-safety premise remains
outside the finite certificate check. -/
theorem checkedSummary_derives [DecidableEq Key] [DecidableEq Slot] (graph : GuardedGraph n Key Slot)
    (key : Key) (coordinate : Fin n) (potential : Slot → Int) (slot : Slot) (semi : Semi n)
    (accepted : checkedSummary graph key coordinate potential slot = .summarized semi)
    (weight : Weight n) :
    Meaning semi weight ↔ RecursiveRows.Derives (rowProblem graph) slot ⟨key, weight⟩ := by
  obtain ⟨checked, rfl⟩ := (checkedSummary_exact graph key coordinate potential slot semi).mp accepted
  exact summary_exact graph key coordinate potential ((check_exact graph key coordinate potential).mp checked)
    slot weight

namespace Examples

def pair (first second : Int) : Weight 2 := fun coordinate => if coordinate = 0 then first else second

theorem pair_add (a b c d : Int) : add (pair a b) (pair c d) = pair (a + c) (b + d) := by
  funext coordinate
  by_cases first : coordinate = 0 <;> simp [SemilinearWeights.add, pair, first]

def point (height : Int) : Occurrence 2 Nat := ⟨0, pair 1 height⟩
def seed : GuardedEdge 2 Nat Unit := .seed () (point 0)
def step (amount : Int) : GuardedEdge 2 Nat Unit :=
  ⟨.slot (), ⟨pair 0 amount, [raw 0]⟩, ()⟩
def graph : GuardedGraph 2 Nat Unit := [seed, step 1, step (-1)]
def potential : Unit → Int := fun _ => 1

/-- Both cycles have a nonempty exclusion set. Its first coordinate is zero,
while all reachable occurrences have first coordinate one. -/
theorem nonempty_guards : (step 1).transport.excluded ≠ [] ∧ (step (-1)).transport.excluded ≠ [] := by
  decide

theorem certificate_passes : check graph 0 0 potential = true := by decide

theorem summary_returned :
    checkedSummary graph 0 0 potential () = .summarized (summary graph 0 ()) := by
  simp [checkedSummary, certificate_passes]

theorem guarded_summary_exact (weight : Weight 2) :
    Meaning (summary graph 0 ()) weight ↔ RecursiveRows.Derives (rowProblem graph) () ⟨0, weight⟩ :=
  checkedSummary_derives graph 0 0 potential () _ summary_returned weight

theorem step_runs (amount height : Int) :
    (step amount).transport.run (point height) = some (point (height + amount)) := by
  have separated : ∀ excluded ∈ ([raw 0] : List (Occurrence 2 Nat)),
      excluded.key ≠ 0 ∨ excluded.weights 0 ≠ (1 : Int) := by
    intro excluded member
    have same : excluded = raw 0 := List.mem_singleton.mp member
    subst excluded
    exact Or.inr (by decide)
  have execution := guard_passes_on_invariant 0 (0 : Fin 2) 1
    (⟨pair 0 amount, [raw 0]⟩ : NormalForm 2 Nat) separated (pair 1 height) (by simp [pair])
  simpa only [step, point, pair_add, Int.add_zero] using execution

theorem zero_reachable : GuardedReachable graph () (point 0) :=
  seed_reachable graph () (point 0) (by simp [graph, seed])

theorem positive_reachable (count : Nat) : GuardedReachable graph () (point (count : Int)) := by
  induction count with
  | zero => exact zero_reachable
  | succ count ih =>
      have reached := GuardedReachable.step (graph := graph)
        (source := ()) (target := ()) (transport := (step 1).transport)
        (by simp [graph, step]) ih (step_runs 1 (count : Int))
      simpa only [Int.natCast_succ] using reached

theorem negative_reachable (count : Nat) : GuardedReachable graph () (point (-(count : Int))) := by
  induction count with
  | zero => exact zero_reachable
  | succ count ih =>
      have reached := GuardedReachable.step (graph := graph)
        (source := ()) (target := ()) (transport := (step (-1)).transport)
        (by simp [graph, step]) ih (step_runs (-1) (-(count : Int)))
      simpa only [Int.natCast_succ, Int.neg_add] using reached

/-- The interacting positive and negative cycles produce every integer in the
second coordinate, with no bound and with the original guards still active. -/
theorem every_integer_reachable (height : Int) : GuardedReachable graph () (point height) := by
  cases height with
  | ofNat count => exact positive_reachable count
  | negSucc count => simpa only [Int.negSucc_eq, Int.natCast_succ] using negative_reachable (count + 1)

theorem summary_contains_every_integer (height : Int) : Meaning (summary graph 0 ()) (pair 1 height) :=
  (guarded_summary_exact _).mpr ((guarded_graph_exact graph () (point height)).mp
    (every_integer_reachable height))

/-- This excluded point lies on the claimed invariant and is the actual seed.
The same potential therefore does not justify deleting this guard. -/
def unsafeGraph : GuardedGraph 2 Nat Unit :=
  [seed, ⟨.slot (), ⟨pair 0 1, [point 0]⟩, ()⟩]

theorem unsafe_certificate_rejected : check unsafeGraph 0 0 potential = false := by decide

theorem unsafe_returns_unsupported : checkedSummary unsafeGraph 0 0 potential () = .unsupported :=
  (checkedSummary_unsupported_iff unsafeGraph 0 0 potential ()).mpr unsafe_certificate_rejected

end Examples

end Yulang.GuardedAffineRows
