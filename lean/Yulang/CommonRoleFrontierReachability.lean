import Yulang.CommonRoleGuardedIntervalFrontier

/-! Full recursive diagnostics of the retained fixed-interval frontier.
Traversal never consults plan counts or satisfiability. Its exact list is the
independently generated finite work closure, including every unfinished child.
This is not dynamic saturation, a final language classification, or dictionary
selection. Sources retain the caller-supplied tuple alias boundary. -/
namespace Yulang.CommonRoleFrontierReachability
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal expand size)
open CommonRoleIntervalCapture (Bindings total)
open CommonRoleIntervalCandidates (Accepts Rejects inspect)
open CommonRoleIntervalWorkClosure (Checked Reach closure children childrenOf)
open CommonRoleGuardedIntervalPlans (Sources candidates)
open CommonRoleGuardedIntervalFrontier (Tree root branches outside rejects build run)

/-- Preorder traversal retains each occurrence, even under zero-plan branches. -/
def nodes : Tree α → List (Tree α)
  | .node goal accepted unsupported rejected =>
      .node goal accepted unsupported rejected :: accepted.flatMap fun entry =>
        entry.2.2.2.flatMap nodes
decreasing_by
  rename_i he t ht
  have outer := List.sizeOf_lt_of_mem he
  have inner := List.sizeOf_lt_of_mem ht
  rcases entry with ⟨d, b, localDemands, descendants⟩
  simp only [Prod.mk.sizeOf_spec, Tree.node.sizeOf_spec] at *
  omega

def goals (tree : Tree α) : List Goal := (nodes tree).map root

def boundaries (tree : Tree α) : List (Goal × Declaration) :=
  (nodes tree).flatMap fun node => (outside node).map (root node, ·)

/-- Local rigid rejections are not a classification of the enclosing goal. -/
def failures (tree : Tree α) : List (Goal × Declaration) :=
  (nodes tree).flatMap fun node => (rejects node).map (root node, ·)

private theorem attach_flatMap (xs : List β) (f : β → List γ) :
    xs.attach.flatMap (fun entry => f entry.val) = xs.flatMap f := by
  simp [List.flatMap_def]

/-- Candidate traversal preserves the complete generated child list, including
its order and duplicates. No descendant completion premise appears. -/
theorem candidates_children (registry : List Declaration) (goal : Goal) :
    (candidates registry goal).flatMap (fun entry => expand entry.val.1 (total entry.val.2)) =
      children registry goal := by
  unfold candidates children
  rw [List.flatMap_assoc]
  simp only [List.flatMap_def]
  rw [← List.attach_map_val (l := registry) (f := fun d => childrenOf d goal)]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro declaration _
  split <;> simp_all [childrenOf]


/-- Exact list correspondence, stronger than equality of reachable sets. -/
theorem build_nodes (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal) :
    nodes (build registry checked slots sources goal) =
      (closure registry checked goal).map (build registry checked slots sources) := by
  rw [build, nodes, closure, List.map_cons]
  congr 1
  · rw [build]
  · simp only [List.flatMap_map, List.map_flatMap]
    have replace :
        (candidates registry goal).flatMap (fun entry =>
          (expand entry.val.1 (total entry.val.2)).attach.flatMap (fun next =>
            nodes (build registry checked slots sources next.val))) =
        (candidates registry goal).flatMap (fun entry =>
          (expand entry.val.1 (total entry.val.2)).flatMap (fun next =>
            (closure registry checked next).map (build registry checked slots sources))) := by
      apply congrArg List.flatten
      apply List.map_congr_left
      intro entry _
      rw [← attach_flatMap (expand entry.val.1 (total entry.val.2))]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro next _
      exact build_nodes registry checked slots sources next.val
    rw [replace, ← List.flatMap_assoc, candidates_children]
    exact (attach_flatMap (children registry goal) _).symm
termination_by size goal.arguments
decreasing_by
  obtain ⟨requirement, included, equal⟩ := List.mem_map.mp next.property
  rw [← equal]
  exact CommonRoleIntervalCandidates.accepted_child_decreases _
    (checked _ entry.property.1) _ _ entry.property.2 _ included

theorem build_goals (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal) :
    goals (build registry checked slots sources goal) = closure registry checked goal := by
  simp [goals, build_nodes, List.map_map, Function.comp_def]

/-- Flattening the actual tree agrees with the separately computed boundary
work list, rather than silently replacing the tree with a new scan. -/
theorem build_boundaries (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal) :
    boundaries (build registry checked slots sources goal) =
      CommonRoleIntervalWorkClosure.boundaries registry checked goal := by
  simp only [boundaries, build_nodes, List.flatMap_map,
    CommonRoleIntervalWorkClosure.boundaries]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro next _
  rw [build]
  rfl

theorem boundaries_exact (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (initial target : Goal) (d : Declaration) :
    (target,d) ∈ boundaries (build registry checked slots sources initial) ↔
      Reach registry initial target ∧ d ∈ registry ∧ inspect d target = none := by
  rw [build_boundaries]
  exact CommonRoleIntervalWorkClosure.boundaries_exact ..

theorem failures_exact (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (initial target : Goal) (d : Declaration) :
    (target,d) ∈ failures (build registry checked slots sources initial) ↔
      Reach registry initial target ∧ d ∈ registry ∧ Rejects d target := by
  simp only [failures, build_nodes, List.flatMap_map, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨next, member, declaration, rejected, same⟩
    have sameGoal : target = next := by simpa using congrArg Prod.fst same.symm
    have sameDecl : declaration = d := congrArg Prod.snd same
    subst target; subst declaration
    exact ⟨(CommonRoleIntervalWorkClosure.closure_exact ..).mp member,
      (CommonRoleGuardedIntervalFrontier.rejects_exact ..).mp rejected⟩
  · rintro ⟨reachable, present, rejected⟩
    exact ⟨target, (CommonRoleIntervalWorkClosure.closure_exact ..).mpr reachable, d,
      (CommonRoleGuardedIntervalFrontier.rejects_exact ..).mpr ⟨present,rejected⟩, by simp⟩

theorem run_reach_exact (registry : List Declaration) (slots : Nat → α) (sources : Sources)
    (initial target : Goal) :
    (∃ tree, run registry slots sources initial = some tree ∧ target ∈ goals tree) ↔
      Checked registry ∧ Reach registry initial target := by
  constructor
  · rintro ⟨tree, returned, member⟩
    obtain ⟨checked, rfl⟩ := (CommonRoleGuardedIntervalFrontier.run_exact ..).mp returned
    rw [build_goals] at member
    exact ⟨checked, (CommonRoleIntervalWorkClosure.closure_exact ..).mp member⟩
  · rintro ⟨checked, reachable⟩
    refine ⟨build registry checked slots sources initial,
      (CommonRoleGuardedIntervalFrontier.run_exact ..).mpr ⟨checked,rfl⟩, ?_⟩
    rw [build_goals]
    exact (CommonRoleIntervalWorkClosure.closure_exact ..).mpr reachable

theorem run_boundaries_exact (registry : List Declaration) (slots : Nat → α) (sources : Sources)
    (initial target : Goal) (d : Declaration) :
    (∃ tree, run registry slots sources initial = some tree ∧ (target,d) ∈ boundaries tree) ↔
      Checked registry ∧ Reach registry initial target ∧ d ∈ registry ∧ inspect d target = none := by
  constructor
  · rintro ⟨tree, returned, member⟩
    obtain ⟨checked,rfl⟩ := (CommonRoleGuardedIntervalFrontier.run_exact ..).mp returned
    exact ⟨checked, (boundaries_exact ..).mp member⟩
  · rintro ⟨checked, evidence⟩
    exact ⟨build registry checked slots sources initial,
      (CommonRoleGuardedIntervalFrontier.run_exact ..).mpr ⟨checked,rfl⟩,
      (boundaries_exact ..).mpr evidence⟩

theorem run_failures_exact (registry : List Declaration) (slots : Nat → α) (sources : Sources)
    (initial target : Goal) (d : Declaration) :
    (∃ tree, run registry slots sources initial = some tree ∧ (target,d) ∈ failures tree) ↔
      Checked registry ∧ Reach registry initial target ∧ d ∈ registry ∧ Rejects d target := by
  constructor
  · rintro ⟨tree, returned, member⟩
    obtain ⟨checked,rfl⟩ := (CommonRoleGuardedIntervalFrontier.run_exact ..).mp returned
    exact ⟨checked, (failures_exact ..).mp member⟩
  · rintro ⟨checked, evidence⟩
    exact ⟨build registry checked slots sources initial,
      (CommonRoleGuardedIntervalFrontier.run_exact ..).mpr ⟨checked,rfl⟩,
      (failures_exact ..).mpr evidence⟩
end Yulang.CommonRoleFrontierReachability
