import Yulang.GeneralRebaseSourceEdgeBasis279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseProjectedEdgeCount279
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralRebaseQuietBound277 (Counted remaining_le)
open GeneralRebaseSourceEdgeBasis279 (project finite_projected_edges)
open GeneralRebaseWitnessRegressions279 (uncount)
open GeneralNominalFiniteProgress (remaining remaining_monotone remaining_decreases)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split)

def Seen (state : State roles) (edge : Nat × Nat) : Prop :=
  edge ∈ state.core.erased.current.edges.map project

def Fresh (before after : State roles) : Prop :=
  ∃ e, ¬ Seen before e ∧ Seen after e

theorem monotone {before after : State roles} {root : Occurrence roles} (step : Actual r root before after) :
    ∀ key, Seen before key → Seen after key := by
  intro key visible
  obtain ⟨edge,recorded,same⟩ := List.mem_map.mp visible
  exact List.mem_map.mpr ⟨edge,(GeneralNominalVersionedMixedGrowth234.step step).edges recorded,same⟩

theorem is_installation {before after : State roles} {root : Occurrence roles}
    (reached : Reachable r root before) (step : Actual r root before after) (novel : Fresh before after) :
    ∃ effect, after = GeneralNominalVersionedInstall232.install before effect := by
  rcases split reached step with admin | ⟨effect,_,_,same⟩
  · obtain ⟨edge,absent,appeared⟩ := novel
    exfalso
    apply absent
    cases admin <;> exact appeared
  · exact ⟨effect,same⟩

inductive Trace (r : Registry) (root : Occurrence roles) : State roles → Nat → Nat → State roles → Prop
  | nil : Trace r root start 0 0 start
  | quiet : Trace r root start n k before → Actual r root before after →
    ¬ Fresh before after → Trace r root start (n+1) k after
  | grown : Trace r root start n k before → Actual r root before after →
    Fresh before after → Trace r root start (n+1) (k+1) after

theorem annotate {root : Occurrence roles} {start after : State roles}
    (walk : Counted (Actual r root) start n after) : ∃ k, Trace r root start n k after := by
  classical
  induction walk with
  | nil => exact ⟨0,.nil⟩
  | @tail n before after _ action ih =>
    obtain ⟨k,marked⟩ := ih
    by_cases fresh : Fresh before after
    · exact ⟨k+1,.grown marked action fresh⟩
    · exact ⟨k,.quiet marked action fresh⟩

theorem trace_rank {root : Occurrence roles} {start after : State roles} (pool : List (Nat × Nat))
    (bounded : ∀ state, B4Target.Steps (Actual r root) start state → ∀ edge, Seen state edge → edge ∈ pool)
    (walk : Trace r root start n k after) :
    B4Target.Steps (Actual r root) start after ∧ k + remaining Seen pool after ≤ remaining Seen pool start := by
  induction walk with
  | nil => exact ⟨.refl,by simp⟩
  | quiet _ action _noNew ih =>
    have smaller := remaining_monotone Seen pool (monotone action)
    exact ⟨.tail ih.1 action,by omega⟩
  | grown _ action fresh ih =>
    obtain ⟨edge,absent,appeared⟩ := fresh
    have present := bounded _ (.tail ih.1 action) edge appeared
    have smaller := remaining_decreases Seen pool (monotone action) present absent appeared
    exact ⟨.tail ih.1 action,by omega⟩

theorem finite_new_id_pair_steps {root : Occurrence roles} {start : State roles}
    (source : (boundary roles).Initial r root start) :
    ∃ cap, ∀ after n k, Trace r root start n k after → k ≤ cap := by
  obtain ⟨pool,cover⟩ := finite_projected_edges source
  refine ⟨pool.length,?_⟩
  intro after n k walk
  have listed (state : State roles) (trace : B4Target.Steps (Actual r root) start state)
      (edge : Nat × Nat) (seen : Seen state edge) : edge ∈ pool := by
    obtain ⟨e,member,rfl⟩ := List.mem_map.mp seen
    exact cover state trace e member
  have budget := (trace_rank pool listed walk).2
  have initial := remaining_le Seen pool start
  omega

end Yulang.GeneralRebaseProjectedEdgeCount279
