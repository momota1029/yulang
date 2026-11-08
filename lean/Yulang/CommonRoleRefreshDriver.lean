import Yulang.CommonRoleCacheInvalidation

/-! State-changing refresh of actual-producer caches, on the int-only unary
source-template fragment. The input is a finite trace of ordinary states, NOT an
autonomous ordinary solver driver. No bound on the supplied trace is claimed. -/
namespace Yulang.CommonRoleRefreshDriver
open CommonRoleMaterializedDomain CommonRoleSourceWorklist CommonRoleCacheInvalidation
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledConstraints (State)

abbrev Cache (registry : Registry) (root : SourceRequest n) :=
  Node registry root → List (SourceRequest n)

def Valid (registry : Registry) (root : SourceRequest n) (s : State n)
    (cache : Cache registry root) : Prop :=
  ∀ q, cache q = actualNext registry s q.val

def initialCache (registry : Registry) (root : SourceRequest n) (s : State n) :
    Cache registry root := fun q => actualNext registry s q.val

def refresh (registry : Registry) (root : SourceRequest n) (before after : State n)
    (cache : Cache registry root) : Cache registry root := fun q =>
  if dirty before after q.val = [] then cache q else actualNext registry after q.val

theorem initialCache_valid (registry : Registry) (root : SourceRequest n) (s : State n) :
    Valid registry root s (initialCache registry root s) := fun _ => rfl

/-- All rows, including parents not previously reachable, are refreshed. -/
theorem refresh_valid (registry : Registry) (root : SourceRequest n) (before after : State n)
    (cache : Cache registry root) (valid : Valid registry root before cache) :
    Valid registry root after (refresh registry root before after cache) := by
  intro q
  unfold refresh
  split
  · rename_i clean
    exact (valid q).trans (actual_next_cache_valid registry before after q.val clean)
  · rfl

theorem clean_row_reused (registry : Registry) (root : SourceRequest n) (before after : State n)
    (cache : Cache registry root) (q : Node registry root)
    (clean : dirty before after q.val = []) :
    refresh registry root before after cache q = cache q := by simp [refresh, clean]

theorem dirty_row_recomputed (registry : Registry) (root : SourceRequest n) (before after : State n)
    (cache : Cache registry root) (q : Node registry root)
    (changed : dirty before after q.val ≠ []) :
    refresh registry root before after cache q = actualNext registry after q.val := by
  simp [refresh, changed]

def cachedRules (registry : Registry) (root : SourceRequest n) (cache : Cache registry root) :
    List (FiniteHorn.Rule (Node registry root)) :=
  ⟨[], rootNode registry root⟩ :: (nodes registry root).flatMap (fun parent =>
    ((nodes registry root).filter fun child => child.val ∈ cache parent).map (edgeRule parent))

def cachedSaturate (registry : Registry) (root : SourceRequest n) (cache : Cache registry root) :
    List (Node registry root) := FiniteHorn.saturate (cachedRules registry root cache) (nodes registry root)

theorem cached_rules_exact (registry : Registry) (root : SourceRequest n) (s : State n)
    (cache : Cache registry root) (valid : Valid registry root s cache) :
    cachedRules registry root cache = rules registry root s := by
  have rows : ∀ q, cache q = actualNext registry s q.val := valid
  simp only [cachedRules, rules, rows]

theorem cached_saturate_exact (registry : Registry) (root : SourceRequest n) (s : State n)
    (cache : Cache registry root) (valid : Valid registry root s cache) (q : Node registry root) :
    q ∈ cachedSaturate registry root cache ↔ Reach registry root s q := by
  rw [cachedSaturate, cached_rules_exact registry root s cache valid]
  exact saturate_exact registry root s q

/-- A finite trace is supplied externally. Refresh regenerates children, then the
final closure is recomputed from those edges, never unioned with stale visits. -/
def replay (registry : Registry) (root : SourceRequest n) (s : State n)
    (cache : Cache registry root) : List (State n) → State n × Cache registry root
  | [] => (s, cache)
  | next :: rest => replay registry root next (refresh registry root s next cache) rest

theorem replay_valid (registry : Registry) (root : SourceRequest n) (s : State n)
    (cache : Cache registry root) (valid : Valid registry root s cache) (trace : List (State n)) :
    Valid registry root (replay registry root s cache trace).1
      (replay registry root s cache trace).2 := by
  induction trace generalizing s cache with
  | nil => exact valid
  | cons next rest ih =>
    exact ih next _ (refresh_valid registry root s next cache valid)

def finalState (s : State n) : List (State n) → State n
  | [] => s
  | next :: rest => finalState next rest

theorem replay_state (registry : Registry) (root : SourceRequest n) (s : State n)
    (cache : Cache registry root) (trace : List (State n)) :
    (replay registry root s cache trace).1 = finalState s trace := by
  induction trace generalizing s cache with
  | nil => rfl
  | cons next rest ih => exact ih next _

def run (registry : Registry) (root : SourceRequest n) (initial : State n)
    (trace : List (State n)) : List (Node registry root) :=
  cachedSaturate registry root (replay registry root initial (initialCache registry root initial) trace).2

/-- Soundness and completeness for arbitrary finite state changes in the stated
implementation fragment. No monotonicity, consistency or final-cache premise is
supplied. The trace itself is input, so this is NOT full B4 resolve_exact. -/
theorem run_exact (registry : Registry) (root : SourceRequest n) (initial : State n)
    (trace : List (State n)) (q : Node registry root) :
    q ∈ run registry root initial trace ↔ Reach registry root (finalState initial trace) q := by
  have valid := replay_valid registry root initial (initialCache registry root initial)
    (initialCache_valid registry root initial) trace
  rw [replay_state] at valid
  exact cached_saturate_exact registry root _ _ valid q

theorem run_root (registry : Registry) (root : SourceRequest n) (initial : State n)
    (trace : List (State n)) : rootNode registry root ∈ run registry root initial trace :=
  (run_exact registry root initial trace _).mpr .root

theorem run_actual_closed (registry : Registry) (root : SourceRequest n) (initial : State n)
    (trace : List (State n)) (parent : Node registry root)
    (present : parent ∈ run registry root initial trace) (child : SourceRequest n)
    (edge : child ∈ actualNext registry (finalState initial trace) parent.val) :
    ∃ q ∈ run registry root initial trace, q.val = child := by
  have generated := actual_next_generated registry (finalState initial trace) parent.val child edge
  let q : Node registry root := ⟨child, CommonRoleSourceTemplateClosure.generated_closed
    registry root parent.val child parent.property generated⟩
  exact ⟨q, (run_exact registry root initial trace q).mpr
    (.step ((run_exact registry root initial trace parent).mp present) edge), rfl⟩

theorem run_nodup (registry : Registry) (root : SourceRequest n) (initial : State n)
    (trace : List (State n)) : (run registry root initial trace).Nodup :=
  FiniteHorn.saturate_nodup _ _

theorem run_capacity (registry : Registry) (root : SourceRequest n) (initial : State n)
    (trace : List (State n)) :
    (run registry root initial trace).length ≤ (CommonRoleSourceTemplateClosure.closure registry root).length := by
  simpa [nodes] using (run_nodup registry root initial trace).length_le_of_subset
    (l₂ := nodes registry root) (fun q _ => nodes_complete registry root q)

/-- Least final-state closure: stale nodes have no special privilege after refresh. -/
theorem run_least (registry : Registry) (root : SourceRequest n) (initial : State n)
    (trace : List (State n)) (holds : Node registry root → Prop)
    (seed : holds (rootNode registry root))
    (closed : ∀ parent child, holds parent →
      child.val ∈ actualNext registry (finalState initial trace) parent.val → holds child)
    (q : Node registry root) (present : q ∈ run registry root initial trace) : holds q := by
  have reach := (run_exact registry root initial trace q).mp present
  clear present
  induction reach with
  | root => exact seed
  | step _ edge ih => exact closed _ _ ih edge

/-- Different update histories ending at the same observed ordinary evidence have
exactly the same reachable source nodes. This is membership, not list-order equality. -/
theorem run_observational_independent (registry : Registry) (root : SourceRequest n)
    (a b : State n) (left right : List (State n))
    (same : ∀ i, known (finalState a left) i = known (finalState b right) i)
    (q : Node registry root) :
    q ∈ run registry root a left ↔ q ∈ run registry root b right := by
  rw [run_exact, run_exact]
  apply reach_cache_valid registry root
  intro node
  exact (clean_iff ..).mpr (fun i _ => same i)

end Yulang.CommonRoleRefreshDriver
