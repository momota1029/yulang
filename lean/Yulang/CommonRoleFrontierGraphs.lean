import Yulang.CommonRoleFrontierReachability

/-! Actual ordinary graphs for complete plans, beside an unchanged diagnostic
tree. Existing atoms and all source demands are conjoined within each alternative.
No graph consistency, state materialization, general solver decision, saturation,
final language classification, or invocation allocation is assumed or concluded. -/
namespace Yulang.CommonRoleFrontierGraphs
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleIntervalWorkClosure (Checked)
open CommonRoleGuardedIntervalPlans (Sources Plan Derives)
open CommonRoleGuardedIntervalFrontier (Tree build plans)
open CommonRoleCaptureBatchModels (SharedFits)
open CommonRoleSourceIntervalBatches (generate)
open CommonPresenceConstraintGraph (Compiled compile)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)

/-- Internal graph nodes may differ between alternatives; input slots and rows
remain original. An empty family does not assign a language failure class. -/
def graphs (existing : List (Atom (Fin n))) (old : Plan (Fin n))
    (tree : Tree (Fin n)) : List (Compiled n) :=
  (plans tree).map fun plan => compile (existing ++ generate (old ++ plan))

/-- This keeps the same tree, including branches without any complete plans. -/
def run (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (existing : List (Atom (Fin n))) (old : Plan (Fin n)) (goal : Goal) :=
  (CommonRoleGuardedIntervalFrontier.run registry slots sources goal).map
    fun tree => (tree, graphs existing old tree)

/-- A graph represents an original assignment when some internal model has that
literal readback. This is a semantic relation, not a Boolean feasibility test. -/
def Represents (family : List (Compiled n)) (assignment : Fin n → Comp Common.model) : Prop :=
  ∃ graph ∈ family, ∃ values : Fin graph.size → Common.Ty,
    graph.Models (fun i => (assignment i).2) values ∧
      graph.readback (fun i => (assignment i).2) values = assignment

/-- Every plan has a graph, including inconsistent plans; order is preserved. -/
theorem graph_count (existing : List (Atom (Fin n))) (old : Plan (Fin n))
    (tree : Tree (Fin n)) : (graphs existing old tree).length = (plans tree).length := by
  simp [graphs]

theorem graphs_exact (existing : List (Atom (Fin n))) (old : Plan (Fin n))
    (tree : Tree (Fin n)) (assignment : Fin n → Comp Common.model) :
    Represents (graphs existing old tree) assignment ↔
      All Common.model assignment existing ∧
        ∃ atoms ∈ CommonRoleGuardedIntervalFrontier.ordinary old tree,
          All Common.model assignment atoms := by
  constructor
  · rintro ⟨graph, member, values, models, readback⟩
    obtain ⟨plan, present, rfl⟩ := List.mem_map.mp member
    have fits := (CommonPresenceConstraintGraph.compile_atoms_exact _ assignment).mpr
      ⟨values, models, readback⟩
    obtain ⟨prior, fresh⟩ := (PresenceNormalForm.all_append ..).mp fits
    exact ⟨prior, _, List.mem_map.mpr ⟨plan, present, rfl⟩, fresh⟩
  · rintro ⟨prior, atoms, member, fits⟩
    obtain ⟨plan, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨values, models, readback⟩ :=
      (CommonPresenceConstraintGraph.compile_atoms_exact _ assignment).mp
        ((PresenceNormalForm.all_append ..).mpr ⟨prior,fits⟩)
    exact ⟨_, List.mem_map.mpr ⟨plan,present,rfl⟩, values,models,readback⟩

/-- All assignments, not just one chosen witness, agree with independent source
meaning. Prior atoms can be inconsistent and need no grammar certificates. -/
theorem build_models_exact (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (existing : List (Atom (Fin n)))
    (old : Plan (Fin n)) (goal : Goal) (assignment : Fin n → Comp Common.model) :
    Represents (graphs existing old (build registry checked slots sources goal)) assignment ↔
      All Common.model assignment existing ∧ ∃ sourceValues,
        SharedFits assignment sourceValues old ∧
          Derives registry slots sources assignment sourceValues goal := by
  rw [graphs_exact, CommonRoleGuardedIntervalFrontier.ordinary_models_exact]

/-- No supplied check or successful child is needed by the public computation. -/
theorem run_models_exact (registry : List Declaration) (slots : Nat → Fin n)
    (sources : Sources) (existing : List (Atom (Fin n))) (old : Plan (Fin n))
    (goal : Goal) (assignment : Fin n → Comp Common.model) :
    (∃ output, run registry slots sources existing old goal = some output ∧
      Represents output.2 assignment) ↔
    Checked registry ∧ All Common.model assignment existing ∧ ∃ sourceValues,
      SharedFits assignment sourceValues old ∧
        Derives registry slots sources assignment sourceValues goal := by
  constructor
  · rintro ⟨output, returned, represented⟩
    obtain ⟨tree, found, rfl⟩ := Option.map_eq_some_iff.mp returned
    obtain ⟨checked,rfl⟩ := (CommonRoleGuardedIntervalFrontier.run_exact ..).mp found
    exact ⟨checked,(build_models_exact ..).mp represented⟩
  · rintro ⟨checked,models⟩
    have found := (CommonRoleGuardedIntervalFrontier.run_exact registry slots sources goal
      (build registry checked slots sources goal)).mpr ⟨checked,rfl⟩
    exact ⟨(build registry checked slots sources goal,
      graphs existing old (build registry checked slots sources goal)),
      by simp [run,found],(build_models_exact ..).mpr models⟩

/-- Graph production leaves the entire diagnostic tree and its order unchanged. -/
theorem run_tree_exact (registry : List Declaration) (slots : Nat → Fin n)
    (sources : Sources) (existing : List (Atom (Fin n))) (old : Plan (Fin n))
    (goal : Goal) :
    (run registry slots sources existing old goal).map Prod.fst =
      CommonRoleGuardedIntervalFrontier.run registry slots sources goal := by
  simp [run, Function.comp_def]

/-- Every model of every produced graph reflects the same independent source
meaning. No internal graph model is privileged by the compiler. -/
theorem graph_reflects (registry : List Declaration) (slots : Nat → Fin n)
    (sources : Sources) (existing : List (Atom (Fin n))) (old : Plan (Fin n))
    (goal : Goal) (output) (returned : run registry slots sources existing old goal = some output)
    (graph : Compiled n) (member : graph ∈ output.2) (rows : Fin n → Common.Row)
    (values : Fin graph.size → Common.Ty) (models : graph.Models rows values) :
    let assignment := graph.readback rows values
    Checked registry ∧ All Common.model assignment existing ∧ ∃ sourceValues,
      SharedFits assignment sourceValues old ∧
        Derives registry slots sources assignment sourceValues goal := by
  apply (run_models_exact ..).mp
  exact ⟨output,returned,graph,member,values,models,rfl⟩

/-- Distinct original input slots are never coalesced by graph allocation. -/
theorem graph_input_injective (existing : List (Atom (Fin n))) (old : Plan (Fin n))
    (tree : Tree (Fin n)) (graph : Compiled n) (member : graph ∈ graphs existing old tree) :
    Function.Injective graph.input := by
  obtain ⟨plan, _, rfl⟩ := List.mem_map.mp member
  exact CommonPresenceConstraintGraph.compile_input_injective _

/-- Recompiling after arbitrary additional ordinary constraints preserves exactly
old represented assignments satisfying those constraints, not internal indices. -/
theorem advance_exact (existing fresh : List (Atom (Fin n))) (old : Plan (Fin n))
    (tree : Tree (Fin n)) (assignment : Fin n → Comp Common.model) :
    Represents (graphs (existing ++ fresh) old tree) assignment ↔
      Represents (graphs existing old tree) assignment ∧ All Common.model assignment fresh := by
  rw [graphs_exact, graphs_exact, PresenceNormalForm.all_append]
  exact and_right_comm

/-- Any later graph model replays into an earlier graph at identical original
readback. The earlier graph may have a different number of internal nodes. -/
theorem advance_replays (existing fresh : List (Atom (Fin n))) (old : Plan (Fin n))
    (tree : Tree (Fin n)) (graph : Compiled n)
    (member : graph ∈ graphs (existing ++ fresh) old tree) (rows : Fin n → Common.Row)
    (values : Fin graph.size → Common.Ty) (models : graph.Models rows values) :
    Represents (graphs existing old tree) (graph.readback rows values) := by
  apply ((advance_exact existing fresh old tree _).mp ?_).1
  exact ⟨graph,member,values,models,rfl⟩

end Yulang.CommonRoleFrontierGraphs
