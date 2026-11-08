import Yulang.CommonRoleGraphInspection
import Yulang.CommonRoleDeferredBounds

/-!
# Lower-bound graph snapshots for role head inspection

The existing demand collector follows actual lower seeds and variable-flow
edges. Here its head projection is fixed by the graph: a node has a known
head exactly when it is not `unresolved`. All currently known lower heads
are retained in source collector order; none is selected as a representative.
Unresolved lower seeds are omitted, not represented as pending entries. A
nonempty result does not imply that every lower seed is known, and an empty
result by itself is not the whole resolver's pending outcome.
The caller still has to build this graph from source constraints, reconcile
multiple lower heads, propagate ordinary constraints, and re-run after graph
updates. The resulting list is not a whole-resolver classification.
-/
namespace Yulang.CommonRoleGraphDemandSnapshots

open CommonRoleRegularGraph CommonRoleGraphInspection
open LayerBoundTemplates (Problem Reaches)

/-- Preserve every original lower contribution, including unresolved nodes. -/
def lowerContributions (problem : Problem n (Fin m)) (slot : Fin n) : List (Fin m) :=
  DemandBoundPropagation.request problem ⟨slot, .lower⟩

theorem lower_contribution_origin (problem : Problem n (Fin m)) (slot : Fin n) (head : Fin m) :
    head ∈ lowerContributions problem slot ↔
      ∃ source, .lower head source ∈ problem ∧ Reaches problem source slot := by
  simp only [lowerContributions, DemandBoundPropagation.request, DemandBoundPropagation.lowerBounds_exact]
  exact PresenceBoundCoalescing.mem_lowerBounds problem slot head

/-- Preserve the original source slot for each lower contribution. -/
def lowerOrigins (problem : Problem n (Fin m)) (slot : Fin n) : List (Fin m × Fin n) :=
  (LayerBoundTemplates.lowerSeeds problem).filter fun entry =>
    decide (slot ∈ LayerBoundTemplates.reachable problem entry.2)

theorem lower_origins_exact (problem : Problem n (Fin m)) (slot source : Fin n) (head : Fin m) :
    (head, source) ∈ lowerOrigins problem slot ↔
      .lower head source ∈ problem ∧ Reaches problem source slot := by
  have seedExact : (head, source) ∈ LayerBoundTemplates.lowerSeeds problem ↔
      .lower head source ∈ problem := by
    simp only [LayerBoundTemplates.lowerSeeds, List.mem_filterMap]
    constructor
    · rintro ⟨constraint, member, found⟩
      cases constraint with
      | lower actual target =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
          exact member
      | _ => cases found
    · intro member
      exact ⟨.lower head source, member, rfl⟩
  simp only [lowerOrigins, List.mem_filter, decide_eq_true_eq, seedExact,
    LayerBoundTemplates.reachable_exact]

theorem lower_origins_project (problem : Problem n (Fin m)) (slot : Fin n) :
    (lowerOrigins problem slot).map Prod.fst = lowerContributions problem slot := by
  simp only [lowerContributions, DemandBoundPropagation.request, DemandBoundPropagation.lowerBounds_exact,
    LayerBoundTemplates.lowerBounds, lowerOrigins]
  generalize LayerBoundTemplates.lowerSeeds problem = seeds
  induction seeds with
  | nil => rfl
  | cons entry rest ih =>
      by_cases reaches : slot ∈ LayerBoundTemplates.reachable problem entry.2 <;> simp [reaches, ih]

def inspectOriginSnapshots (graph : Graph m) (problem : Problem n (Fin m)) (slot : Fin n)
    (role : Nat) (visible : List VisibleHead) : List ((Fin m × Fin n) × Snapshot m) :=
  (lowerOrigins problem slot).map fun (head, source) =>
    ((head, source), inspectSnapshot graph role head visible)

theorem inspect_origin_snapshots_exact (graph : Graph m) (problem : Problem n (Fin m)) (slot source : Fin n)
    (role : Nat) (visible : List VisibleHead) (head : Fin m) (result : Snapshot m) :
    ((head, source), result) ∈ inspectOriginSnapshots graph problem slot role visible ↔
      (.lower head source ∈ problem ∧ Reaches problem source slot) ∧
        inspectSnapshot graph role head visible = result := by
  simp only [inspectOriginSnapshots, List.mem_map]
  constructor
  · rintro ⟨⟨found, start⟩, member, equal⟩
    have samePair := (Prod.mk.inj equal).1
    have sameHead : found = head := (Prod.mk.inj samePair).1
    have sameSource : start = source := (Prod.mk.inj samePair).2
    subst found
    subst start
    exact ⟨(lower_origins_exact problem slot source head).mp member, (Prod.mk.inj equal).2⟩
  · rintro ⟨origin, same⟩
    exact ⟨(head, source), (lower_origins_exact problem slot source head).mpr origin, by simp [same]⟩

def inspectAllContributions (graph : Graph m) (problem : Problem n (Fin m)) (slot : Fin n)
    (role : Nat) (visible : List VisibleHead) : List (Fin m × Snapshot m) :=
  (lowerContributions problem slot).map fun head => (head, inspectSnapshot graph role head visible)

theorem inspect_all_contributions_exact (graph : Graph m) (problem : Problem n (Fin m)) (slot : Fin n)
    (role : Nat) (visible : List VisibleHead) (head : Fin m) (result : Snapshot m) :
    (head, result) ∈ inspectAllContributions graph problem slot role visible ↔
      (∃ source, .lower head source ∈ problem ∧ Reaches problem source slot) ∧
        inspectSnapshot graph role head visible = result := by
  simp only [inspectAllContributions, List.mem_map]
  constructor
  · rintro ⟨found, member, equal⟩
    have same : found = head := (Prod.mk.inj equal).1
    subst found
    exact ⟨(lower_contribution_origin problem slot head).mp member, (Prod.mk.inj equal).2⟩
  · rintro ⟨origin, same⟩
    exact ⟨head, (lower_contribution_origin problem slot head).mpr origin, by simp [same]⟩

theorem unresolved_contribution_retained (graph : Graph m) (problem : Problem n (Fin m))
    (slot : Fin n) (role : Nat) (visible : List VisibleHead) (head : Fin m)
    (origin : ∃ source, .lower head source ∈ problem ∧ Reaches problem source slot)
    (unresolved : graph head = .unresolved) :
    (head, .unknown) ∈ inspectAllContributions graph problem slot role visible := by
  apply (inspect_all_contributions_exact graph problem slot role visible head .unknown).mpr
  exact ⟨origin, (snapshot_unknown_exact graph role head visible).mpr unresolved⟩

def project (graph : Graph m) (node : Fin m) : Option (Fin m) :=
  if graph node = .unresolved then none else some node

def lowerHeads (graph : Graph m) (problem : Problem n (Fin m)) (slot : Fin n) : List (Fin m) :=
  CommonRoleDeferredBounds.lowerHeads (project graph) problem slot

theorem lower_head_origin (graph : Graph m) (problem : Problem n (Fin m)) (slot : Fin n) (head : Fin m) :
    head ∈ lowerHeads graph problem slot ↔
      ∃ source, .lower head source ∈ problem ∧ Reaches problem source slot ∧ graph head ≠ .unresolved := by
  rw [lowerHeads, CommonRoleDeferredBounds.lowerHeads_exact]
  simp only [CommonRoleDeferredBounds.HasLowerHead]
  constructor
  · rintro ⟨bound, source, seed, path, projected⟩
    unfold project at projected
    split at projected
    · cases projected
    · rename_i known
      have same := Option.some.inj projected
      subst bound
      exact ⟨source, seed, path, known⟩
  · rintro ⟨source, seed, path, known⟩
    exact ⟨head, source, seed, path, by simp [project, known]⟩

def inspectLowerHeads (graph : Graph m) (problem : Problem n (Fin m)) (slot : Fin n)
    (role : Nat) (visible : List VisibleHead) : List (Fin m × Snapshot m) :=
  (lowerHeads graph problem slot).map fun head => (head, inspectSnapshot graph role head visible)

theorem inspect_lower_heads_exact (graph : Graph m) (problem : Problem n (Fin m)) (slot : Fin n)
    (role : Nat) (visible : List VisibleHead) (head : Fin m) (result : Snapshot m) :
    (head, result) ∈ inspectLowerHeads graph problem slot role visible ↔
      (∃ source, .lower head source ∈ problem ∧ Reaches problem source slot ∧ graph head ≠ .unresolved) ∧
        inspectSnapshot graph role head visible = result := by
  simp only [inspectLowerHeads, List.mem_map]
  constructor
  · rintro ⟨found, member, equal⟩
    have headEqual : found = head := (Prod.mk.inj equal).1
    subst found
    exact ⟨(lower_head_origin graph problem slot head).mp member, (Prod.mk.inj equal).2⟩
  · rintro ⟨origin, same⟩
    exact ⟨head, (lower_head_origin graph problem slot head).mpr origin, by simp [same]⟩

theorem upper_only_has_no_lower_heads (graph : Graph m) (upper : Fin m) :
    lowerHeads graph ([.upper 0 upper] : Problem 1 (Fin m)) 0 = [] := by
  cases heads : lowerHeads graph ([.upper 0 upper] : Problem 1 (Fin m)) 0 with
  | nil => rfl
  | cons first rest =>
      have observed := CommonRoleDeferredBounds.upper_only_pending (project graph) upper
      change (match lowerHeads graph ([.upper 0 upper] : Problem 1 (Fin m)) 0 with
        | [] => CommonRoleDeferredBounds.Observation.pending
        | first :: rest => CommonRoleDeferredBounds.Observation.known first rest) = .pending at observed
      rw [heads] at observed
      cases observed

/-- A known and an unresolved lower seed are both retained by the
all-contributions entry, rather than silently selecting the known one. -/
def mixedGraph : Graph 2 := fun node => if node = 0 then .scalar 0 else .unresolved
def mixedProblem : Problem 1 (Fin 2) := [.lower 0 0, .lower 1 0]

theorem mixed_contributions_retained :
    (0, .heads []) ∈ inspectAllContributions mixedGraph mixedProblem 0 0 [] ∧
      (1, .unknown) ∈ inspectAllContributions mixedGraph mixedProblem 0 0 [] := by
  decide +kernel

end Yulang.CommonRoleGraphDemandSnapshots
