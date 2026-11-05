import Yulang.GuardedRowErasure
import Yulang.SemilinearDecisions

/-!
# Automatic exact summaries and membership for harmless guarded row problems

The original finite row AST is the input. Its fixed-key transport graph is
normalized, failed head guards are kept disabled, and the erased reachability
set at each slot-edge source is represented semilinearly. The total signed
semilinear membership checker then verifies that every excluded input is absent
from the appropriate source set. Successful checking proves every intermediate
guard harmless and returns the exact least row solution.

No coordinate, potential, finite universe of slots, path bound or correctness
certificate is supplied by the caller. A failed guard check means unsupported
by this erasure algorithm; it is never a language rejection or a negative
membership answer. Both true and false answers of a successful query are exact.
-/

namespace Yulang.AutomaticRowSummaries

open Directed (Occurrence)
open FinitePointGuards (GuardedEdge GuardedGraph)
open SemilinearWeights (Weight Semi Meaning)

variable {n : Nat} {Key Slot : Type}

def SafeEdge [DecidableEq Key] (graph : GuardedGraph n Key Slot) (key : Key)
    (edge : GuardedEdge n Key Slot) : Prop :=
  match edge.source with
  | .head _ => True
  | .slot source => ∀ point ∈ edge.transport.excluded, point.key = key →
      ¬ WeightedPaths.Path (GuardedAffineRows.weightedGraph graph key)
        none (some source) point.weights

def checkEdge [DecidableEq Key] [DecidableEq Slot]
    (graph : GuardedGraph n Key Slot) (key : Key) (edge : GuardedEdge n Key Slot) : Bool :=
  match edge.source with
  | .head _ => true
  | .slot source =>
      if edge.transport.excluded.all (fun point => decide (point.key ≠ key)) then true
      else
        let sourceSummary := GuardedAffineRows.summary graph key source
        edge.transport.excluded.all fun point =>
          decide (point.key ≠ key) || !SemilinearDecisions.check sourceSummary point.weights

theorem checkEdge_exact [DecidableEq Key] [DecidableEq Slot]
    (graph : GuardedGraph n Key Slot) (key : Key) (edge : GuardedEdge n Key Slot) :
    checkEdge graph key edge = true ↔ SafeEdge graph key edge := by
  cases edge with
  | mk source transport target =>
      cases source with
      | head sourceKey => simp [checkEdge, SafeEdge]
      | slot source =>
          simp only [checkEdge, SafeEdge]
          split
          · rename_i irrelevant
            have absent := List.all_eq_true.mp irrelevant
            constructor
            · intro _ point member same
              exact ((of_decide_eq_true (absent point member)) same).elim
            · intro _; rfl
          · simp only [List.all_eq_true, Bool.or_eq_true,
              decide_eq_true_eq, Bool.not_eq_true', SemilinearDecisions.check_rejects,
              GuardedAffineRows.summary, WeightedPaths.solveFinite_exact]
            constructor
            · intro checked point member same
              exact (checked point member).resolve_left (fun different => different same)
            · intro safe point member
              by_cases same : point.key = key
              · exact Or.inr (safe point member same)
              · exact Or.inl same

def check [DecidableEq Key] [DecidableEq Slot]
    (graph : GuardedGraph n Key Slot) (key : Key) : Bool :=
  graph.all (checkEdge graph key)

theorem check_exact [DecidableEq Key] [DecidableEq Slot]
    (graph : GuardedGraph n Key Slot) (key : Key) :
    check graph key = true ↔ GuardedRowErasure.Harmless graph key := by
  rw [check, List.all_eq_true]
  simp only [checkEdge_exact]
  constructor
  · intro safe source target transport member
    exact safe ⟨.slot source, transport, target⟩ member
  · intro safe edge member
    cases edge with
    | mk source transport target =>
        cases source with
        | head sourceKey => trivial
        | slot source => exact safe source target transport member

/-- Construct a summary of the original row problem only after the automatic
guard check succeeds. `none` is a solver-fragment boundary, not rejection. -/
def summarize [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (slot : Slot) : Option (Semi n) :=
  if check (CertifiedRowSummaries.normalizedProblem key problem) key then
    some (CertifiedRowSummaries.summary problem key slot)
  else none

theorem summarize_returned_iff [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (slot : Slot) (semi : Semi n) :
    summarize problem key slot = some semi ↔
      check (CertifiedRowSummaries.normalizedProblem key problem) key = true ∧
        CertifiedRowSummaries.summary problem key slot = semi := by
  unfold summarize
  split <;> simp_all

theorem summarize_exact [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (slot : Slot) (semi : Semi n)
    (returned : summarize problem key slot = some semi) (weight : Weight n) :
    Meaning semi weight ↔ RecursiveRows.Derives problem slot ⟨key, weight⟩ := by
  obtain ⟨accepted, rfl⟩ := (summarize_returned_iff problem key slot semi).mp returned
  exact GuardedRowErasure.original_summary_exact problem key
    ((check_exact _ key).mp accepted) slot weight

def query [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (slot : Slot)
    (weight : Weight n) : Option Bool :=
  (summarize problem key slot).map fun semi => SemilinearDecisions.check semi weight

/-- An actual returned answer, including `false`, is equivalent to membership
in the original recursive problem's least solution. -/
theorem query_exact [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (slot : Slot)
    (weight : Weight n) (answer : Bool) (returned : query problem key slot weight = some answer) :
    answer = true ↔ RecursiveRows.Derives problem slot ⟨key, weight⟩ := by
  unfold query at returned
  cases result : summarize problem key slot with
  | none => simp [result] at returned
  | some semi =>
      simp only [result, Option.map_some, Option.some.injEq] at returned
      rw [← returned, SemilinearDecisions.check_exact]
      exact summarize_exact problem key slot semi result weight

theorem query_false [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (slot : Slot)
    (weight : Weight n) (returned : query problem key slot weight = some false) :
    ¬ RecursiveRows.Derives problem slot ⟨key, weight⟩ := by
  intro member
  have impossible := (query_exact problem key slot weight false returned).mpr member
  contradiction

/-- Every formerly certified coordinate/potential example is recognized
without supplying that certificate to the new executable entry. -/
theorem certified_is_supported [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (coordinate : Fin n)
    (potential : Slot → Int)
    (certified : GuardedAffineRows.Certified (CertifiedRowSummaries.normalizedProblem key problem)
      key coordinate potential) (slot : Slot) :
    summarize problem key slot = some (CertifiedRowSummaries.summary problem key slot) := by
  apply (summarize_returned_iff problem key slot _).mpr
  refine ⟨(check_exact _ key).mpr ?_, rfl⟩
  exact GuardedRowErasure.harmless_of_certified _ key coordinate potential certified

end Yulang.AutomaticRowSummaries
