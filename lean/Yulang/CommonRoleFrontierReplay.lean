import Yulang.CommonRoleMaterializationProgress

/-! Change-triggered replay of complete materialized diagnostic trees.
The supplied finite update stream is not a solver execution. Only the diagnostic
tree is reused, never ordinary graphs. Counts measure rebuilds and full preorder
node visits, not total runtime, graph vertices or all ordinary-state work. -/
namespace Yulang.CommonRoleFrontierReplay
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleIntervalWorkClosure (Checked closure)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleGuardedIntervalFrontier (Tree build)
open CommonRoleStateMaterializedFrontier (materializeGoal domain)
open CommonRoleMaterializationProgress (Chain changes potential)
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

private theorem block_length_le (xs : List α) (f : α → List β) (x : α) (member : x ∈ xs) :
    (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | inside
      · subst x; simp only [List.flatMap_cons,List.length_append]; omega
      · have bound := ih inside
        simp only [List.flatMap_cons,List.length_append]; omega

/-- Multiplicity-sensitive bound: an actual closure is a whole block in the
computed variant domain, not merely a subset of its set of goals. -/
theorem nodeCount_le_domain (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal) (atoms : List (Atom (Fin n))) :
    nodeCount (build registry checked slots sources (materializeGoal atoms slots original)) ≤
      (domain registry checked original).length := by
  rw [nodeCount,CommonRoleFrontierReachability.build_goals]
  exact block_length_le _ _ _ (CommonRoleStateMaterializedFrontier.goal_present atoms slots original)

theorem replayFrom_visits (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial : List (Atom (Fin n))) (cached : Tree (Fin n))
    (states : List (List (Atom (Fin n)))) :
    (replayFrom registry checked slots sources original initial cached states).visits ≤
      changes slots original initial states * (domain registry checked original).length := by
  induction states generalizing initial cached with
  | nil => simp [replayFrom,changes]
  | cons next rest ih =>
      simp only [replayFrom,changes]
      split
      · simpa using ih next cached
      · have tail := ih next (build registry checked slots sources (materializeGoal next slots original))
        have count := nodeCount_le_domain registry checked slots sources original next
        simp only [Nat.add_mul,Nat.one_mul]
        omega

/-- Both bounds are computed from original syntax and declarations. Chain is
an explicit theorem premise about supplied states, not an execution oracle. -/
theorem replay_bounded (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (chain : Chain initial states) :
    (replay registry checked slots sources original initial states).rebuilds ≤ 1 + potential original ∧
    (replay registry checked slots sources original initial states).visits ≤
      (1 + potential original) * (domain registry checked original).length := by
  have changesBound := CommonRoleMaterializationProgress.changes_bounded slots original initial states chain
  constructor
  · rw [replay_rebuilds]; omega
  · have tail := replayFrom_visits registry checked slots sources original initial
      (build registry checked slots sources (materializeGoal initial slots original)) states
    have first := nodeCount_le_domain registry checked slots sources original initial
    have product := Nat.mul_le_mul_right (domain registry checked original).length changesBound
    simp only [replay,Nat.add_mul,Nat.one_mul]
    omega

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
      (CommonRoleStateMaterializedFrontier.run registry slots sources atoms (old atoms) original).map Prod.fst) := by
  obtain ⟨checked,rfl⟩ := (run_exact ..).mp returned
  rw [replay_snapshots,List.map_map]
  apply List.map_congr_left
  intro atoms _
  simp only [Function.comp_def,CommonRoleStateMaterializedFrontier.run,
    CommonRoleFrontierGraphs.run_tree_exact]
  exact ((CommonRoleGuardedIntervalFrontier.run_exact ..).mpr ⟨checked,rfl⟩).symm

/-- Public bounds need no supplied checker proof or work list. The supplied
Chain is still not an adequacy theorem for a real ordinary solver trace. -/
theorem run_computed_bound (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (output : Replay n) (returned : run registry slots sources original initial states = some output)
    (chain : Chain initial states) :
    ∃ bound, CommonRoleStateMaterializedFrontier.workDomain registry original = some bound ∧
      output.snapshots.length = 1 + states.length ∧
      output.rebuilds ≤ 1 + potential original ∧
      output.visits ≤ (1 + potential original) * bound.length := by
  obtain ⟨checked,rfl⟩ := (run_exact ..).mp returned
  refine ⟨domain registry checked original,
    (CommonRoleStateMaterializedFrontier.workDomain_exact ..).mpr ⟨checked,rfl⟩,?_,
    replay_bounded registry checked slots sources original initial states chain⟩
  rw [replay_snapshots,List.length_map,List.length_cons]
  omega

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
        CommonRoleStateMaterializedFrontier.run registry slots sources atoms (old i) original) := by
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
    simp only [Function.comp_def,CommonRoleStateMaterializedFrontier.run,
      CommonRoleFrontierGraphs.run,built,Option.map_some]

end Yulang.CommonRoleFrontierReplay
