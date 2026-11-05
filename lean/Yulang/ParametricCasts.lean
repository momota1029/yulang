import Yulang.ParametricCastUniverse
import Yulang.FiniteReachability

/-!
# Terminating exact exploration of parametric cast chains

The finite instance universe is computed from checked declarations and the
ground source, rather than supplied by the caller. Canonical one-way matching
provides every outgoing instance. The shared finite graph closure then decides
the independent `Path` judgement, including paths of arbitrary finite length.
There is no user-selected fuel, maximum chain length, or acyclicity assumption.

This executable reference algorithm enumerates bounded types and Boolean graph
valuations. It establishes decidability, not production complexity. Cycles can
still be traversed forever by a naive evaluator; this decision procedure does
not traverse such a chain blindly.

`query` checks endpoint-size admissibility and source groundness before search.
Pure-body checking and duplicate-direct/overlapping-declaration diagnostics are
separate from endpoint reachability. Encoding the source type language into
these first-order constructor terms remains the elaborator's obligation.
-/

namespace Yulang.ParametricCasts

open Roles

instance (term : Term) : Decidable (Ground term) :=
  inferInstanceAs (Decidable (term.bound = 0))

def instanceGraph (rules : List Rule) (types : List Term) :
    FiniteReachability.Adj types.length :=
  fun source => (List.finRange types.length).filter fun target =>
    decide (types.get target ∈ successors rules (types.get source))

def initialVertices (types : List Term) (source : Term) : List (Fin types.length) :=
  (List.finRange types.length).filter fun vertex => decide (types.get vertex = source)

theorem mem_instanceGraph (rules : List Rule) (valid : Valid rules) (types : List Term)
    (source target : Fin types.length) :
    target ∈ instanceGraph rules types source ↔ Step rules (types.get source) (types.get target) := by
  simp only [instanceGraph, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
    mem_successors rules valid]

theorem mem_initialVertices (types : List Term) (source : Term) (vertex : Fin types.length) :
    vertex ∈ initialVertices types source ↔ types.get vertex = source := by
  simp [initialVertices]

theorem instance_path_sound (rules : List Rule) (valid : Valid rules) (types : List Term)
    (source : Term) (vertex : Fin types.length)
    (path : FiniteReachability.Reach (instanceGraph rules types) (initialVertices types source)
      vertex) : Path rules source (types.get vertex) := by
  induction path with
  | seed member =>
      have same := (mem_initialVertices types source _).mp member
      rw [same]
      exact .refl
  | step _ edge ih => exact .step ih ((mem_instanceGraph rules valid types _ _).mp edge)

theorem instance_path_complete (rules : List Rule) (valid : Valid rules) (source : Term)
    (ground : Ground source) {target : Term} (path : Path rules source target)
    (vertex : Fin (instanceUniverse rules source).length)
    (same : (instanceUniverse rules source).get vertex = target) :
    FiniteReachability.Reach (instanceGraph rules (instanceUniverse rules source))
      (initialVertices (instanceUniverse rules source) source) vertex := by
  induction path generalizing vertex with
  | refl => exact .seed ((mem_initialVertices _ _ _).mpr same)
  | step path edge ih =>
      obtain ⟨previous, previousEq⟩ :=
        List.mem_iff_get.mp (path_mem_universe rules valid ground path)
      apply FiniteReachability.Reach.step (ih previous previousEq)
      apply (mem_instanceGraph rules valid _ previous vertex).mpr
      simpa only [previousEq, same] using edge

def search (rules : List Rule) (source target : Term) : Bool :=
  let types := instanceUniverse rules source
  (List.finRange types.length).any fun vertex =>
    decide (types.get vertex = target) &&
      FiniteReachability.closure (instanceGraph rules types) (initialVertices types source) vertex

/-- Both directions quantify over every target; no finite-graph premise remains. -/
theorem search_exact (rules : List Rule) (valid : Valid rules) (source target : Term)
    (ground : Ground source) : search rules source target = true ↔ Path rules source target := by
  simp only [search, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨vertex, _, same, reached⟩
    have path := instance_path_sound rules valid _ source vertex
      ((FiniteReachability.closure_exact _ _ _).mp reached)
    simpa only [same] using path
  · intro path
    obtain ⟨vertex, same⟩ := List.mem_iff_get.mp (path_mem_universe rules valid ground path)
    exact ⟨vertex, List.mem_finRange vertex, same,
      (FiniteReachability.closure_exact _ _ _).mpr
        (instance_path_complete rules valid source ground path vertex same)⟩

/-- `none` rejects declarations or a non-ground query before constructing the graph. -/
def query (rules : List Rule) (source target : Term) : Option Bool :=
  if checkRules rules && decide (Ground source) then some (search rules source target) else none

theorem query_checked (rules : List Rule) (valid : Valid rules) (source target : Term)
    (ground : Ground source) : query rules source target = some (search rules source target) := by
  simp [query, (checkRules_exact rules).mpr valid, ground]

theorem query_rejected_iff (rules : List Rule) (source target : Term) :
    query rules source target = none ↔ ¬ (Valid rules ∧ Ground source) := by
  by_cases accepted : checkRules rules = true
  · have valid := (checkRules_exact rules).mp accepted
    by_cases ground : Ground source <;> simp [query, accepted, valid, ground]
  · have invalid : ¬ Valid rules := fun valid => accepted ((checkRules_exact rules).mpr valid)
    simp [query, accepted, invalid]

theorem query_success_iff (rules : List Rule) (source target : Term) :
    query rules source target = some true ↔
      Valid rules ∧ Ground source ∧ Path rules source target := by
  by_cases valid : Valid rules
  · by_cases ground : Ground source
    · rw [query_checked rules valid source target ground, Option.some.injEq,
        search_exact rules valid source target ground]
      simp [valid, ground]
    · have rejected := (query_rejected_iff rules source target).mpr (by simp [ground])
      simp [rejected, ground]
  · have rejected := (query_rejected_iff rules source target).mpr (by simp [valid])
    simp [rejected, valid]

theorem query_failure_iff (rules : List Rule) (source target : Term) :
    query rules source target = some false ↔
      Valid rules ∧ Ground source ∧ ¬ Path rules source target := by
  by_cases valid : Valid rules
  · by_cases ground : Ground source
    · rw [query_checked rules valid source target ground, Option.some.injEq]
      have exactness := search_exact rules valid source target ground
      cases answer : search rules source target <;> simp_all
    · have rejected := (query_rejected_iff rules source target).mpr (by simp [ground])
      simp [rejected, ground]
  · have rejected := (query_rejected_iff rules source target).mpr (by simp [valid])
    simp [rejected, valid]

theorem Path.rules_mono {rules other : List Rule}
    (included : ∀ rule, rule ∈ rules → rule ∈ other) {source target : Term}
    (path : Path rules source target) : Path other source target := by
  induction path with
  | refl => exact .refl
  | step _ edge ih =>
      rcases edge with ⟨rule, member, instanceOf⟩
      exact .step ih ⟨rule, included rule member, instanceOf⟩

theorem search_rules_perm {rules other : List Rule} (permutation : rules.Perm other)
    (valid : Valid rules) (source target : Term) (ground : Ground source) :
    search rules source target = search other source target := by
  have otherValid : Valid other := fun rule member =>
    valid rule (permutation.mem_iff.mpr member)
  have paths : Path rules source target ↔ Path other source target :=
    ⟨Path.rules_mono (fun _ member => permutation.mem_iff.mp member),
      Path.rules_mono (fun _ member => permutation.mem_iff.mpr member)⟩
  have same : search rules source target = true ↔ search other source target = true := by
    rw [search_exact rules valid source target ground,
      search_exact other otherValid source target ground]
    exact paths
  cases left : search rules source target <;> cases right : search other source target <;> simp_all

end Yulang.ParametricCasts
