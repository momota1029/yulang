import Yulang.Casts
import Yulang.FiniteReachability

/-!
# Finite ground cast registration and boundary checking

The registry contains distinct ground nominal endpoints and visible direct
rules. Two declarations of the same direct source/target pair are rejected.
Different paths through the graph are allowed; reachability is exact for paths
of every finite length and does not use a search-depth cutoff.

`checkBoundary` first validates the registry, then checks ordinary compatibility.
Only a mismatch invokes conversion search. The result records whether the value
is kept or converted; it does not synthesize conversion code or equate the runtime
behaviour of different paths. Grounding polymorphic declarations and establishing
that their reachable instance graph is finite remain outside this module.
-/

namespace Yulang.CastGraph

open Casts

abbrev Rule (n : Nat) := Fin n × Fin n

def adjacency (rules : List (Rule n)) : FiniteReachability.Adj n :=
  fun source => (rules.filter (fun rule => decide (rule.1 = source))).map Prod.snd

@[simp] theorem mem_adjacency (rules : List (Rule n)) (source target : Fin n) :
    target ∈ adjacency rules source ↔ (source, target) ∈ rules := by
  simp only [adjacency, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨origin, destination⟩, ⟨present, sameSource⟩, sameTarget⟩
    cases sameSource
    cases sameTarget
    exact present
  · intro present
    exact ⟨(source, target), ⟨present, rfl⟩, rfl⟩

def reachable (rules : List (Rule n)) (source target : Fin n) : Bool :=
  FiniteReachability.closure (adjacency rules) [source] target

abbrev Path (rules : List (Rule n)) (source target : Fin n) : Prop :=
  FiniteReachability.Reach (adjacency rules) [source] target

theorem reachable_exact (rules : List (Rule n)) (source target : Fin n) :
    reachable rules source target = true ↔ Path rules source target :=
  FiniteReachability.closure_exact _ _ _

theorem reachable_perm {left right : List (Rule n)} (permutation : left.Perm right)
    (source target : Fin n) : reachable left source target = reachable right source target := by
  apply congrFun
  apply FiniteReachability.closure_congr (fun _ => Iff.rfl)
  intro origin destination
  simpa only [mem_adjacency] using permutation.mem_iff (a := (origin, destination))

structure Registry (n : Nat) where
  types : Fin n → Ty
  rules : List (Rule n)

/-- One vertex per ground type, nominal endpoints, and one direct declaration
per ordered pair. This does not demand a unique transitive path. -/
def Registry.WellFormed (registry : Registry n) : Prop :=
  registry.rules.Nodup ∧ (∀ vertex, (registry.types vertex).isNominal = true) ∧
    ∀ left right, registry.types left = registry.types right → left = right

instance (registry : Registry n) : Decidable registry.WellFormed := by
  unfold Registry.WellFormed
  infer_instance

def Registry.validate (registry : Registry n) : Bool := decide registry.WellFormed

@[simp] theorem Registry.validate_exact (registry : Registry n) :
    registry.validate = true ↔ registry.WellFormed := by
  simp [Registry.validate]

def Registry.Explicit (registry : Registry n) (source target : Ty) : Prop :=
  ∃ first, registry.types first = source ∧
    ∃ last, registry.types last = target ∧ Path registry.rules first last

def Registry.find (registry : Registry n) (source target : Ty) : Bool :=
  (List.finRange n).any (fun first => decide (registry.types first = source) &&
    (List.finRange n).any (fun last => decide (registry.types last = target) &&
      reachable registry.rules first last))

theorem Registry.find_exact (registry : Registry n) (source target : Ty) :
    registry.find source target = true ↔ registry.Explicit source target := by
  simp [Registry.find, Registry.Explicit, List.any_eq_true, reachable_exact]

def Registry.oracle (registry : Registry n) : ExplicitCasts where
  Rel := registry.Explicit
  check := registry.find
  exact := registry.find_exact

inductive Result where
  | invalidRegistry
  | unchanged
  | converted
  | rejected
  deriving DecidableEq, Repr

def Result.accepted : Result → Bool
  | .unchanged | .converted => true
  | .invalidRegistry | .rejected => false

def checkBoundary (fits : Compatibility) (registry : Registry n) (source target : Ty) : Result :=
  if registry.validate then
    if fits.check source target then .unchanged
    else if converts fits.check registry.find source target then .converted else .rejected
  else .invalidRegistry

theorem checkBoundary_accepted_iff (fits : Compatibility) (registry : Registry n) (source target : Ty) :
    (checkBoundary fits registry source target).accepted = true ↔
      registry.WellFormed ∧ Boundary fits.Rel registry.Explicit source target := by
  have boundary := accepts_exact fits registry.oracle source target
  by_cases valid : registry.validate = true
  · have wellFormed := (registry.validate_exact).mp valid
    cases matching : fits.check source target <;>
      cases converted : converts fits.check registry.find source target <;>
        simpa [checkBoundary, valid, wellFormed, Result.accepted, accepts, Registry.oracle,
          matching, converted] using boundary
  · have malformed : ¬ registry.WellFormed := fun wf => valid ((registry.validate_exact).mpr wf)
    simp [checkBoundary, valid, malformed, Result.accepted]

theorem checkBoundary_unchanged_iff (fits : Compatibility) (registry : Registry n) (source target : Ty) :
    checkBoundary fits registry source target = .unchanged ↔
      registry.WellFormed ∧ fits.Rel source target := by
  by_cases valid : registry.validate = true
  · by_cases matching : fits.check source target = true
    · simp [checkBoundary, valid, matching, (registry.validate_exact).mp valid,
        (fits.exact source target).mp matching]
    · have mismatch : ¬ fits.Rel source target := fun h => matching ((fits.exact source target).mpr h)
      cases converted : converts fits.check registry.find source target <;>
        simp [checkBoundary, valid, matching, converted, mismatch]
  · have malformed : ¬ registry.WellFormed := fun wf => valid ((registry.validate_exact).mpr wf)
    simp [checkBoundary, valid, malformed]

/-- A compatible boundary does not consult cast paths, even when such paths exist. -/
theorem compatible_kept (fits : Compatibility) (registry : Registry n) (source target : Ty)
    (valid : registry.WellFormed) (matching : fits.Rel source target) :
    checkBoundary fits registry source target = .unchanged :=
  (checkBoundary_unchanged_iff fits registry source target).mpr ⟨valid, matching⟩

theorem checkBoundary_invalid_iff (fits : Compatibility) (registry : Registry n) (source target : Ty) :
    checkBoundary fits registry source target = .invalidRegistry ↔ ¬ registry.WellFormed := by
  by_cases valid : registry.validate = true
  · have wellFormed := (registry.validate_exact).mp valid
    cases matching : fits.check source target <;>
      cases converted : converts fits.check registry.find source target <;>
        simp [checkBoundary, valid, matching, converted, wellFormed]
  · have malformed : ¬ registry.WellFormed := fun wf => valid ((registry.validate_exact).mpr wf)
    simp [checkBoundary, valid, malformed]

theorem duplicate_direct_rule_rejected (fits : Compatibility) (registry : Registry n)
    (duplicate : ¬ registry.rules.Nodup) (source target : Ty) :
    checkBoundary fits registry source target = .invalidRegistry :=
  (checkBoundary_invalid_iff fits registry source target).mpr (fun wf => duplicate wf.1)

end Yulang.CastGraph
