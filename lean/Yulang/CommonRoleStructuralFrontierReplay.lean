import Yulang.CommonRoleStructuralMaterializationDomain

/-! Full diagnostic replay for closed structural ordinary materialization.
Literal tree caching is sound on arbitrary states. Inclusive computed updates
permit at most two rebuild events per original variable occurrence. Fresh
ordinary graphs and all failed diagnostic structure are retained. This is not
a terminating generator of the externally supplied finite batch sequence. -/
namespace Yulang.CommonRoleStructuralFrontierReplay
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleIntervalWorkClosure (Checked closure)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleGuardedIntervalFrontier (Tree build)
open CommonRoleStructuralOrdinaryMaterialization (materializeGoal)
open CommonRoleStructuralMaterializationProgress (Chain changes)
open PresenceNormalForm (Atom)

structure Replay (n : Nat) where
  snapshots : List (Tree (Fin n))
  rebuilds : Nat
  visits : Nat

/-- Accounting metric: full preorder occurrences in one rebuilt tree, not
every operation or internal traversal of the implementation. -/
def nodeCount (tree : Tree α) : Nat := (CommonRoleFrontierReachability.goals tree).length

/-- The previous complete tree is reused only on literal materialized-goal
identity. Later states are processed even after arbitrarily many plateaus. -/
def replayFrom (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial : List (Atom (Fin n))) (cached : Tree (Fin n)) :
    List (List (Atom (Fin n))) → Replay n
  | [] => ⟨[],0,0⟩
  | next :: rest =>
      let same := materializeGoal next slots original = materializeGoal initial slots original
      let tree := if same then cached else build registry checked slots sources (materializeGoal next slots original)
      let tail := replayFrom registry checked slots sources original next tree rest
      ⟨tree :: tail.snapshots, (if same then 0 else 1) + tail.rebuilds,
        (if same then 0 else nodeCount tree) + tail.visits⟩

/-- Builds the initial tree once, then reuses it across unchanged observations.
Snapshots still have the full input-stream length; only rebuilding is bounded. -/
def replay (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n)))) : Replay n :=
  let first := build registry checked slots sources (materializeGoal initial slots original)
  let tail := replayFrom registry checked slots sources original initial first states
  ⟨first :: tail.snapshots,1 + tail.rebuilds,nodeCount first + tail.visits⟩

/-- No consistency or inclusion premise: caching preserves every complete
snapshot even for contradictory or nonmonotone input streams. -/
theorem replayFrom_snapshots (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial : List (Atom (Fin n))) (cached : Tree (Fin n))
    (states : List (List (Atom (Fin n))))
    (valid : cached = build registry checked slots sources (materializeGoal initial slots original)) :
    (replayFrom registry checked slots sources original initial cached states).snapshots =
      states.map (fun atoms => build registry checked slots sources (materializeGoal atoms slots original)) := by
  induction states generalizing initial cached with
  | nil => rfl
  | cons next rest ih =>
      simp only [replayFrom,List.map_cons]
      split
      · rename_i same
        have nextValid : cached = build registry checked slots sources (materializeGoal next slots original) := by
          rw [same]; exact valid
        rw [ih next cached nextValid,nextValid]
      · exact congrArg (List.cons _) (ih next _ rfl)

theorem replay_snapshots (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n)))) :
    (replay registry checked slots sources original initial states).snapshots =
      (initial :: states).map (fun atoms => build registry checked slots sources (materializeGoal atoms slots original)) := by
  simp only [replay,List.map_cons]
  rw [replayFrom_snapshots registry checked slots sources original initial _ states rfl]

theorem replayFrom_rebuilds (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial : List (Atom (Fin n))) (cached : Tree (Fin n))
    (states : List (List (Atom (Fin n)))) :
    (replayFrom registry checked slots sources original initial cached states).rebuilds =
      changes slots original initial states := by
  induction states generalizing initial cached with
  | nil => rfl
  | cons next rest ih => simp only [replayFrom,changes]; split <;> simp only [ih]

theorem replay_rebuilds (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n)))) :
    (replay registry checked slots sources original initial states).rebuilds =
      1 + changes slots original initial states := by
  simp only [replay,replayFrom_rebuilds]

/-- Public entry computes the existing declaration checker once. -/
def run (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n)))) :
    Option (Replay n) :=
  if checked : registry.all CommonRoleStablePaterson.check = true then
    some (replay registry (List.all_eq_true.mp checked) slots sources original initial states)
  else none

theorem run_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (output : Replay n) :
    run registry slots sources original initial states = some output ↔
      ∃ checked : Checked registry, output = replay registry checked slots sources original initial states := by
  unfold run
  split
  · constructor
    · intro same; exact ⟨_,Option.some.inj same.symm⟩
    · rintro ⟨_,rfl⟩; rfl
  · rename_i notChecked
    constructor
    · intro impossible; cases impossible
    · rintro ⟨checked,_⟩; exact False.elim (notChecked (List.all_eq_true.mpr checked))

/-- Replay snapshots equal the actual public graph-run tree projections at
all supplied states. Old demands may vary with the state; graphs are not cached. -/
theorem run_graph_snapshots (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (output : Replay n) (returned : run registry slots sources original initial states = some output)
    (old : List (Atom (Fin n)) → Plan (Fin n)) :
    output.snapshots.map some = (initial :: states).map (fun atoms =>
      (CommonRoleStructuralOrdinaryMaterialization.run registry slots sources atoms (old atoms) original).map Prod.fst) := by
  obtain ⟨checked,rfl⟩ := (run_exact ..).mp returned
  rw [replay_snapshots,List.map_map]
  apply List.map_congr_left
  intro atoms _
  simp only [Function.comp_def,CommonRoleStructuralOrdinaryMaterialization.run,
    CommonRoleFrontierGraphs.run_tree_exact]
  exact ((CommonRoleGuardedIntervalFrontier.run_exact ..).mpr ⟨checked,rfl⟩).symm

/-- Refresh ordinary graphs at every input occurrence with independently indexed old demands while reusing its cached
complete diagnostic tree. Mismatched lengths fail rather than dropping states. -/
def refreshGraphs (old : Nat → Plan (Fin n)) :
    List (List (Atom (Fin n))) → List (Tree (Fin n)) →
      Option (List (Tree (Fin n) × List (CommonPresenceConstraintGraph.Compiled n)))
  | [], [] => some []
  | atoms :: states, tree :: trees =>
      (refreshGraphs (fun i => old (i + 1)) states trees).map ((tree,CommonRoleFrontierGraphs.graphs atoms (old 0) tree) :: ·)
  | _, _ => none

theorem refreshGraphs_exact (old : Nat → Plan (Fin n))
    (draw : List (Atom (Fin n)) → Tree (Fin n)) (states : List (List (Atom (Fin n)))) :
    refreshGraphs old states (states.map draw) = some (states.mapIdx (fun i atoms =>
      (draw atoms,CommonRoleFrontierGraphs.graphs atoms (old i) (draw atoms)))) := by
  induction states generalizing old with
  | nil => rfl
  | cons atoms rest ih => simp [refreshGraphs,ih]

/-- State graphs are always freshly compiled, including on tree plateaus.
No represented model, successful plan or solver result is required. -/
def runGraphs (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (old : Nat → Plan (Fin n)) :=
  (run registry slots sources original initial states).bind fun output =>
    (refreshGraphs old (initial :: states) output.snapshots).map fun graphs => (output,graphs)

/-- Every successful replay refreshes the full public graph result exactly,
not just its tree projection. Even repeated atom lists can have different per-occurrence old demands. -/
theorem runGraphs_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (old : Nat → Plan (Fin n)) (output : Replay n)
    (returned : run registry slots sources original initial states = some output) :
    ∃ graphs, runGraphs registry slots sources original initial states old = some (output,graphs) ∧
      graphs.map some = (initial :: states).mapIdx (fun i atoms =>
        CommonRoleStructuralOrdinaryMaterialization.run registry slots sources atoms (old i) original) := by
  obtain ⟨checked,equal⟩ := (run_exact ..).mp returned
  let draw := fun atoms => build registry checked slots sources (materializeGoal atoms slots original)
  refine ⟨(initial :: states).mapIdx (fun i atoms =>
    (draw atoms,CommonRoleFrontierGraphs.graphs atoms (old i) (draw atoms))),?_,?_⟩
  · simp only [runGraphs,returned,Option.bind_some]
    rw [equal,replay_snapshots,refreshGraphs_exact]
    rfl
  · simp only [List.mapIdx_eq_zipIdx_map,List.map_map]
    apply List.map_congr_left
    intro entry _
    have built := (CommonRoleGuardedIntervalFrontier.run_exact registry slots sources
      (materializeGoal entry.1 slots original) (draw entry.1)).mpr ⟨checked,rfl⟩
    simp only [Function.comp_def,CommonRoleStructuralOrdinaryMaterialization.run,
      CommonRoleFrontierGraphs.run,built,Option.map_some]


private theorem block_length_le (xs : List α) (f : α → List β) (x : α) (member : x ∈ xs) :
    (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | inside
    · subst x; simp only [List.flatMap_cons,List.length_append]; omega
    · have bound := ih inside
      simp only [List.flatMap_cons,List.length_append]; omega

open CommonRoleStructuralMaterializationProgress (Included)
open CommonRoleStructuralMaterializationDomain (domain workDomain)

/-- Multiplicity is accounted for: each actual closure is a whole block in the
computed domain, not merely a subset of the set of domain nodes. -/
theorem nodeCount_le_domain (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (atoms envelope : List (Atom (Fin n))) (included : Included atoms envelope) :
    nodeCount (build registry checked slots sources (materializeGoal atoms slots original)) ≤
      (domain registry checked envelope slots original).length := by
  rw [nodeCount,CommonRoleFrontierReachability.build_goals]
  exact block_length_le _ _ _ (CommonRoleStructuralMaterializationDomain.goal_present included slots original)

theorem replayFrom_visits (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial envelope : List (Atom (Fin n))) (cached : Tree (Fin n))
    (states : List (List (Atom (Fin n))))
    (covered : ∀ atoms ∈ states, Included atoms envelope) :
    (replayFrom registry checked slots sources original initial cached states).visits ≤
      changes slots original initial states * (domain registry checked envelope slots original).length := by
  induction states generalizing initial cached with
  | nil => simp [replayFrom,changes]
  | cons next rest ih =>
    have tailCovered : ∀ atoms ∈ rest, Included atoms envelope :=
      fun atoms member => covered atoms (List.mem_cons_of_mem _ member)
    simp only [replayFrom,changes]
    split
    · simpa using ih next cached tailCovered
    · have tail := ih next (build registry checked slots sources (materializeGoal next slots original)) tailCovered
      have count := nodeCount_le_domain registry checked slots sources original next envelope
        (covered next List.mem_cons_self)
      simp only [Nat.add_mul,Nat.one_mul]
      omega

/-- Inclusive traces may lose unique syntax on consistent evidence. The budget
allows both acquisition and loss, and does not stop on a plateau. -/
theorem replay_bounded (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial envelope : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (chain : Chain initial states) (covered : ∀ atoms ∈ initial :: states, Included atoms envelope) :
    (replay registry checked slots sources original initial states).rebuilds ≤
      1 + 2 * CommonRoleMaterializationProgress.potential original ∧
    (replay registry checked slots sources original initial states).visits ≤
      (1 + 2 * CommonRoleMaterializationProgress.potential original) *
        (domain registry checked envelope slots original).length := by
  have bound := CommonRoleStructuralMaterializationProgress.changes_bounded slots original initial states chain
  constructor
  · rw [replay_rebuilds]; omega
  · have tail := replayFrom_visits registry checked slots sources original initial envelope
      (build registry checked slots sources (materializeGoal initial slots original)) states
      (fun atoms member => covered atoms (List.mem_cons_of_mem _ member))
    have first := nodeCount_le_domain registry checked slots sources original initial envelope
      (covered initial List.mem_cons_self)
    have product := Nat.mul_le_mul_right (domain registry checked envelope slots original).length bound
    simp only [replay,Nat.add_mul,Nat.one_mul]
    omega

/-- Every snapshot keeps all generated children in the actual atom envelope's
computed closure, including outside and unsuccessful candidate branches. -/
theorem replay_work_present (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial envelope : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (covered : ∀ atoms ∈ initial :: states, Included atoms envelope)
    (tree : Tree (Fin n)) (member : tree ∈ (replay registry checked slots sources original initial states).snapshots)
    (target : Goal) (node : target ∈ CommonRoleFrontierReachability.goals tree) :
    target ∈ domain registry checked envelope slots original := by
  rw [replay_snapshots] at member
  obtain ⟨atoms,present,rfl⟩ := List.mem_map.mp member
  rw [CommonRoleFrontierReachability.build_goals] at node
  exact CommonRoleStructuralMaterializationDomain.regenerated_reach_present registry checked
    (covered atoms present) slots original target ((CommonRoleIntervalWorkClosure.closure_exact ..).mp node)

/-- The actual ordinary solver checks every internally computed cumulative
state; the public runner takes no trace, model, Chain or checked-registry proof. -/
def runBatches (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : CommonRoleSettledConstraints.State n)
    (batches : List (CommonRoleSettledConstraints.State n)) : Option (Replay n) :=
  if CommonRoleCheckedOrdinaryReplay.validate initial batches then
    run registry slots sources original initial.atoms
      ((CommonRoleCheckedOrdinaryReplay.trace initial batches).map CommonRoleSettledConstraints.State.atoms)
  else none

theorem runBatches_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : CommonRoleSettledConstraints.State n)
    (batches : List (CommonRoleSettledConstraints.State n)) (output : Replay n) :
    runBatches registry slots sources original initial batches = some output ↔
      (CommonRoleCheckedOrdinaryReplay.final initial batches).Models ∧
        ∃ checked : Checked registry, output = replay registry checked slots sources original initial.atoms
          ((CommonRoleCheckedOrdinaryReplay.trace initial batches).map CommonRoleSettledConstraints.State.atoms) := by
  unfold runBatches
  split
  · rename_i valid
    rw [run_exact]
    exact (and_iff_right ((CommonRoleCheckedOrdinaryReplay.validate_exact ..).mp valid)).symm
  · rename_i invalid
    constructor
    · intro impossible; cases impossible
    · rintro ⟨models,_⟩
      exact False.elim (invalid ((CommonRoleCheckedOrdinaryReplay.validate_exact ..).mpr models))

theorem runBatches_exists_iff (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : CommonRoleSettledConstraints.State n)
    (batches : List (CommonRoleSettledConstraints.State n)) :
    (∃ output, runBatches registry slots sources original initial batches = some output) ↔
      (CommonRoleCheckedOrdinaryReplay.final initial batches).Models ∧ Checked registry := by
  constructor
  · rintro ⟨output,returned⟩
    obtain ⟨models,checked,_⟩ := (runBatches_exact ..).mp returned
    exact ⟨models,checked⟩
  · rintro ⟨models,checked⟩
    exact ⟨_,(runBatches_exact ..).mpr ⟨models,checked,rfl⟩⟩

theorem batches_covered (initial : CommonRoleSettledConstraints.State n)
    (batches : List (CommonRoleSettledConstraints.State n)) :
    ∀ atoms ∈ initial.atoms :: (CommonRoleCheckedOrdinaryReplay.trace initial batches).map
        CommonRoleSettledConstraints.State.atoms,
      Included atoms (CommonRoleCheckedOrdinaryReplay.final initial batches).atoms := by
  intro atoms member
  rcases List.mem_cons.mp member with same | later
  · subst atoms; exact CommonRoleCheckedOrdinaryReplay.final_includes initial batches
  · obtain ⟨state,present,rfl⟩ := List.mem_map.mp later
    exact CommonRoleStructuralMaterializationDomain.trace_includes_final initial batches state present

/-- Domain, state trace and both cost bounds are computed for the finite job.
The source-only factor bounds rebuild events, not future payload sizes or the
number of externally submitted ordinary batches. -/
theorem runBatches_computed_bound (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : CommonRoleSettledConstraints.State n)
    (batches : List (CommonRoleSettledConstraints.State n)) (output : Replay n)
    (returned : runBatches registry slots sources original initial batches = some output) :
    ∃ bound, workDomain registry (CommonRoleCheckedOrdinaryReplay.final initial batches).atoms slots original = some bound ∧
      output.snapshots.length = 1 + batches.length ∧
      output.rebuilds ≤ 1 + 2 * CommonRoleMaterializationProgress.potential original ∧
      output.visits ≤ (1 + 2 * CommonRoleMaterializationProgress.potential original) * bound.length ∧
      ∀ tree ∈ output.snapshots, ∀ target ∈ CommonRoleFrontierReachability.goals tree, target ∈ bound := by
  obtain ⟨_,checked,rfl⟩ := (runBatches_exact ..).mp returned
  refine ⟨_,(CommonRoleStructuralMaterializationDomain.workDomain_exact ..).mpr ⟨checked,rfl⟩,?_,?_,?_,?_⟩
  · rw [replay_snapshots,List.length_map,List.length_cons,List.length_map,
      CommonRoleCheckedOrdinaryReplay.trace_length]
    omega
  · exact (replay_bounded registry checked slots sources original initial.atoms _ _
      (CommonRoleStructuralMaterializationProgress.computed_chain initial batches) (batches_covered initial batches)).1
  · exact (replay_bounded registry checked slots sources original initial.atoms _ _
      (CommonRoleStructuralMaterializationProgress.computed_chain initial batches) (batches_covered initial batches)).2
  · intro tree member target node
    exact replay_work_present registry checked slots sources original initial.atoms _ _
      (batches_covered initial batches) tree member target node

def runBatchGraphs (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : CommonRoleSettledConstraints.State n)
    (batches : List (CommonRoleSettledConstraints.State n)) (old : Nat → Plan (Fin n)) :=
  if CommonRoleCheckedOrdinaryReplay.validate initial batches then
    runGraphs registry slots sources original initial.atoms
      ((CommonRoleCheckedOrdinaryReplay.trace initial batches).map CommonRoleSettledConstraints.State.atoms) old
  else none

/-- Full graph outputs, not just trees, equal rerunning the public structural
frontier at every computed state. Repeated states retain indexed old demands. -/
theorem runBatchGraphs_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : CommonRoleSettledConstraints.State n)
    (batches : List (CommonRoleSettledConstraints.State n)) (old : Nat → Plan (Fin n)) (output : Replay n)
    (returned : runBatches registry slots sources original initial batches = some output) :
    ∃ graphs, runBatchGraphs registry slots sources original initial batches old = some (output,graphs) ∧
      graphs.map some = (initial.atoms :: (CommonRoleCheckedOrdinaryReplay.trace initial batches).map
        CommonRoleSettledConstraints.State.atoms).mapIdx (fun i atoms =>
          CommonRoleStructuralOrdinaryMaterialization.run registry slots sources atoms (old i) original) := by
  have valid := (CommonRoleCheckedOrdinaryReplay.validate_exact ..).mpr ((runBatches_exact ..).mp returned).1
  simp only [runBatchGraphs,valid,ite_true]
  apply runGraphs_exact
  simpa only [runBatches,valid,ite_true] using returned

end Yulang.CommonRoleStructuralFrontierReplay
