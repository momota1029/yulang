import Yulang.CommonRoleGuardedIntervalPlans

/-! Candidate-preserving diagnostic trees for fixed interval syntax. An accepted
parent retains every child, including children with no complete plans. Outside
scans and rigid rejects remain distinct. Erasure yields the previous exact
shared-source plan semantics. This is not state saturation or final language
classification, and does not select or compare dictionaries. -/
namespace Yulang.CommonRoleGuardedIntervalFrontier
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal expand size)
open CommonRoleIntervalCapture (Bindings total)
open CommonRoleIntervalCandidates (Accepts Rejects inspect)
open CommonRoleIntervalWorkClosure (Checked)
open CommonRoleGuardedIntervalPlans (Sources Plan candidates products Derives)
open CommonRoleCaptureBatchModels (SharedFits demands)
open CommonRoleWhereSourceModels (captureJob)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

/-- Accepted branches remain present independently of descendant success. The
branch tuple is declaration, captured bindings, local demands, and all children.
Lists retain their own source order and multiplicity. -/
inductive Tree (α : Type) where
  | node (goal : Goal)
      (branches : List (Declaration × Bindings × Plan α × List (Tree α)))
      (outside rejects : List Declaration) : Tree α

def root : Tree α → Goal
  | .node goal _ _ _ => goal

def branches : Tree α → List (Declaration × Bindings × Plan α × List (Tree α))
  | .node _ accepted _ _ => accepted

def outside : Tree α → List Declaration
  | .node _ _ unsupported _ => unsupported

def rejects : Tree α → List Declaration
  | .node _ _ _ rejected => rejected

/-- Every accepted branch is built, without consulting descendant plan counts.
There is no fuel, external finite work list, or child solver assumption. -/
def build (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal) : Tree α :=
  .node goal ((candidates registry goal).map fun entry =>
    (entry.val.1, entry.val.2,
      demands slots (captureJob entry.val.1 goal (sources goal entry.val.1)) entry.val.2,
      (expand entry.val.1 (total entry.val.2)).attach.map fun next =>
        build registry checked slots sources next.val))
    (CommonRoleIntervalWorkClosure.outside registry goal)
    (registry.filter fun d => inspect d goal == some none)
termination_by size goal.arguments
decreasing_by
  obtain ⟨requirement, included, equal⟩ := List.mem_map.mp next.property
  rw [← equal]
  exact CommonRoleIntervalCandidates.accepted_child_decreases _
    (checked _ entry.property.1) _ _ entry.property.2 _ included

/-- Forget the diagnostic structure only when complete plans are requested.
This erasure intentionally drops unsuccessful branches, not the stored tree. -/
def plans : Tree α → List (Plan α)
  | .node _ accepted _ _ => accepted.flatMap fun entry =>
      (products (entry.2.2.2.map plans)).map (entry.2.2.1 ++ ·)
decreasing_by
  rename_i g os rs he t ht
  have outer := List.sizeOf_lt_of_mem he
  have inner := List.sizeOf_lt_of_mem ht
  rcases entry with ⟨d, b, localDemands, children⟩
  simp only [Prod.mk.sizeOf_spec, Tree.node.sizeOf_spec] at *
  omega

@[simp] theorem build_root (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal) :
    root (build registry checked slots sources goal) = goal := by rw [build]; rfl

/-- Exact list equality preserves the order and multiplicity of complete plans. -/
theorem build_plans (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal) :
    plans (build registry checked slots sources goal) =
      CommonRoleGuardedIntervalPlans.compile registry checked slots sources goal := by
  rw [build, plans, CommonRoleGuardedIntervalPlans.compile]
  simp only [List.flatMap_map, List.map_map]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro entry member
  congr 2
  apply List.map_congr_left
  intro next included
  exact build_plans registry checked slots sources next.val
termination_by size goal.arguments
decreasing_by
  obtain ⟨requirement, included, equal⟩ := List.mem_map.mp next.property
  rw [← equal]
  exact CommonRoleIntervalCandidates.accepted_child_decreases _
    (checked _ entry.property.1) _ _ entry.property.2 _ included

/-- No descendant success premise: the exact full child list is retained even
when one or more children have no complete plans. -/
theorem accepted_retained (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal)
    (d : Declaration) (b : Bindings) (present : d ∈ registry) (accepted : Accepts d goal b) :
    ∃ children,
      (d, b, demands slots (captureJob d goal (sources goal d)) b, children) ∈
        branches (build registry checked slots sources goal) ∧
      children = (expand d (total b)).attach.map
        (fun next => build registry checked slots sources next.val) ∧
      children.map root = expand d (total b) := by
  obtain ⟨entry, member, same⟩ :=
    CommonRoleGuardedIntervalPlans.candidates_complete registry goal d b present accepted
  rw [build, branches]
  refine ⟨(expand d (total b)).attach.map (fun next => build registry checked slots sources next.val),
    List.mem_map.mpr ⟨entry, member, ?_⟩, rfl, ?_⟩
  · rcases entry with ⟨⟨d', b'⟩, property⟩
    cases same
    rfl
  · simp [List.map_map, Function.comp_def, build_root]

/-- Every retained branch is an actual accepted declaration. -/
theorem branch_sound (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal)
    (entry : Declaration × Bindings × Plan α × List (Tree α))
    (member : entry ∈ branches (build registry checked slots sources goal)) :
    entry.1 ∈ registry ∧ Accepts entry.1 goal entry.2.1 := by
  rw [build, branches] at member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact original.property

/-- Local demands and the exact recursive child payload of every retained
branch come from the original accepted capture, not an arbitrary replacement. -/
theorem branch_payload_exact (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal)
    (entry : Declaration × Bindings × Plan α × List (Tree α))
    (member : entry ∈ branches (build registry checked slots sources goal)) :
    entry.2.2.1 = demands slots (captureJob entry.1 goal (sources goal entry.1)) entry.2.1 ∧
    entry.2.2.2 = (expand entry.1 (total entry.2.1)).attach.map
      (fun next => build registry checked slots sources next.val) ∧
    entry.2.2.2.map root = expand entry.1 (total entry.2.1) := by
  rw [build, branches] at member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  refine ⟨rfl, rfl, ?_⟩
  simp [List.map_map, Function.comp_def, build_root]

theorem outside_exact (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal) (d : Declaration) :
    d ∈ outside (build registry checked slots sources goal) ↔
      d ∈ registry ∧ inspect d goal = none := by
  rw [build, outside]
  exact CommonRoleIntervalWorkClosure.outside_exact registry goal d

theorem rejects_exact (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal) (d : Declaration) :
    d ∈ rejects (build registry checked slots sources goal) ↔
      d ∈ registry ∧ Rejects d goal := by
  rw [build, rejects]
  simp only [List.mem_filter, beq_iff_eq]
  rw [CommonRoleIntervalCandidates.inspect_rejects_exact]

/-- Real ordinary generation still sees all siblings and old demands together. -/
def ordinary (old : Plan α) (tree : Tree α) :=
  (plans tree).map fun plan => CommonRoleSourceIntervalBatches.generate (old ++ plan)

theorem ordinary_models_exact (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (old : Plan α) (goal : Goal)
    (assignment : α → Comp Common.model) :
    (∃ atoms ∈ ordinary old (build registry checked slots sources goal),
      All Common.model assignment atoms) ↔
    ∃ values, SharedFits assignment values old ∧
      Derives registry slots sources assignment values goal := by
  unfold ordinary
  rw [build_plans]
  exact CommonRoleGuardedIntervalPlans.ordinary_exact registry checked slots sources old goal assignment

/-- The public result is the diagnostic tree itself, including unfinished
children. The declaration check is computed, never supplied by callers. -/
def run (registry : List Declaration) (slots : Nat → α) (sources : Sources) (goal : Goal) :=
  if checked : registry.all CommonRoleStablePaterson.check = true then
    some (build registry (List.all_eq_true.mp checked) slots sources goal)
  else none

theorem run_exact (registry : List Declaration) (slots : Nat → α) (sources : Sources)
    (goal : Goal) (tree : Tree α) :
    run registry slots sources goal = some tree ↔
      ∃ checked : Checked registry, tree = build registry checked slots sources goal := by
  unfold run
  split
  · rename_i checked
    constructor
    · intro same; exact ⟨List.all_eq_true.mp checked, Option.some.inj same.symm⟩
    · rintro ⟨_, rfl⟩; rfl
  · rename_i notChecked
    constructor
    · intro impossible; cases impossible
    · rintro ⟨checked, _⟩
      exact False.elim (notChecked (List.all_eq_true.mpr checked))

/-- All-model correspondence for the computed frontier, without caller check,
model, child-success, or finite-visit assumptions. This is not four-way B4. -/
theorem run_models_exact (registry : List Declaration) (slots : Nat → α) (sources : Sources)
    (old : Plan α) (goal : Goal) (assignment : α → Comp Common.model) :
    (∃ tree, run registry slots sources goal = some tree ∧
      ∃ atoms ∈ ordinary old tree, All Common.model assignment atoms) ↔
    Checked registry ∧ ∃ values, SharedFits assignment values old ∧
      Derives registry slots sources assignment values goal := by
  constructor
  · rintro ⟨tree, returned, models⟩
    obtain ⟨checked, rfl⟩ := (run_exact ..).mp returned
    exact ⟨checked, (ordinary_models_exact ..).mp models⟩
  · rintro ⟨checked, models⟩
    exact ⟨build registry checked slots sources goal, (run_exact ..).mpr ⟨checked, rfl⟩,
      (ordinary_models_exact ..).mpr models⟩

end Yulang.CommonRoleGuardedIntervalFrontier
