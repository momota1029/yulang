import Std

/-!
# A total finite branching inspection worklist

The input is a finite edge inventory, a computation of currently rigid
edges, and a finite list of inspection branches for each edge. The worklist
chooses an inventory edge that is currently rigid and has not been processed.
Every chosen branch adds its children and auxiliary constraints and records
the choice in a finite trace. Old constraints are retained.

The executable run takes no fuel. Internally its structural recursion has
the inventory length as capacity. Each recursive step processes one fresh
inventory edge, so every returned state has no unprocessed inventory edge.
Explicit inventory-support hypotheses give closure for all final rigid edges.
No semantic law is stored in an input graph, state, branch, or interpretation.

This is a generic finite component. Instantiation with generated type/row
constraints and preservation of their inspection grammar are separate tasks.
-/

namespace Yulang.FiniteBranchingWorklist

universe u v

variable {Edge : Type u} {Aux : Type v}

structure Branch (Edge : Type u) (Aux : Type v) where
  children : List Edge
  aux : List Aux

structure State (Edge : Type u) (Aux : Type v) where
  edges : List Edge
  processed : List Edge
  aux : List Aux
  trace : List (Edge × Branch Edge Aux)

def initial (edges : List Edge) (aux : List Aux) : State Edge Aux :=
  ⟨edges, [], aux, []⟩

def pending [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (state : State Edge Aux) : Option Edge :=
  inventory.find? (fun edge => decide (edge ∈ rigid state.edges ∧ edge ∉ state.processed))

def advance (state : State Edge Aux) (edge : Edge) (branch : Branch Edge Aux) : State Edge Aux :=
  ⟨branch.children ++ state.edges, edge :: state.processed,
    branch.aux ++ state.aux, (edge, branch) :: state.trace⟩

private def explore [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) : Nat → State Edge Aux → List (State Edge Aux)
  | 0, state => [state]
  | capacity + 1, state =>
      match pending inventory rigid state with
      | none => [state]
      | some edge => (inspect edge).flatMap
          (fun branch => explore inventory rigid inspect capacity (advance state edge branch))

/-- Total finite computation with no caller-selected cutoff. -/
def run [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (edges : List Edge) (aux : List Aux) :
    List (State Edge Aux) :=
  explore inventory rigid inspect inventory.length (initial edges aux)

/-- A syntactic support hypothesis, supplied separately to the theorems. -/
def InspectionSupported (inventory : List Edge) (inspect : Edge → List (Branch Edge Aux)) : Prop :=
  ∀ edge ∈ inventory, ∀ branch ∈ inspect edge, branch.children ⊆ inventory

/-- The rigid-edge computation may derive new edges; all its endpoints must
still belong to the fixed inventory whenever the current edges do. -/
def RigidSupported (inventory : List Edge) (rigid : List Edge → List Edge) : Prop :=
  ∀ edges, edges ⊆ inventory → rigid edges ⊆ inventory

/-- Closure includes the actual selected branch and retention of every
child and auxiliary constraint in the final state. -/
def Closed (rigid : List Edge → List Edge) (inspect : Edge → List (Branch Edge Aux))
    (state : State Edge Aux) : Prop :=
  ∀ edge ∈ rigid state.edges, ∃ branch ∈ inspect edge,
    (edge, branch) ∈ state.trace ∧ branch.children ⊆ state.edges ∧ branch.aux ⊆ state.aux

theorem pending_some [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (state : State Edge Aux) (edge : Edge) (selected : pending inventory rigid state = some edge) :
    edge ∈ inventory ∧ edge ∈ rigid state.edges ∧ edge ∉ state.processed := by
  exact ⟨List.mem_of_find?_eq_some selected,
    by simpa only [decide_eq_true_eq] using List.find?_some selected⟩

theorem pending_none [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (state : State Edge Aux) :
    pending inventory rigid state = none ↔
      ∀ edge ∈ inventory, edge ∈ rigid state.edges → edge ∈ state.processed := by
  simp only [pending, List.find?_eq_none, decide_eq_true_eq]
  constructor
  · intro absent edge listed active
    by_cases processed : edge ∈ state.processed
    · exact processed
    · exact False.elim (absent edge listed ⟨active, processed⟩)
  · intro complete edge listed both
    exact both.2 (complete edge listed both.1)

structure Invariant (inventory : List Edge) (inspect : Edge → List (Branch Edge Aux))
    (state : State Edge Aux) : Prop where
  edges_supported : state.edges ⊆ inventory
  processed_supported : state.processed ⊆ inventory
  distinct : state.processed.Nodup
  trace_keys : state.trace.map Prod.fst = state.processed
  valid_branch : ∀ edge branch, (edge, branch) ∈ state.trace → branch ∈ inspect edge
  children_present : ∀ edge branch, (edge, branch) ∈ state.trace → branch.children ⊆ state.edges
  aux_present : ∀ edge branch, (edge, branch) ∈ state.trace → branch.aux ⊆ state.aux

theorem invariant_initial (inventory : List Edge) (inspect : Edge → List (Branch Edge Aux))
    (edges : List Edge) (aux : List Aux) (supported : edges ⊆ inventory) :
    Invariant inventory inspect (initial edges aux) :=
  ⟨supported, by simp [initial], by simp [initial], rfl,
    by simp [initial], by simp [initial], by simp [initial]⟩

theorem Invariant.advance [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (state : State Edge Aux)
    (invariant : Invariant inventory inspect state) (support : InspectionSupported inventory inspect)
    (edge : Edge) (selected : pending inventory rigid state = some edge)
    (branch : Branch Edge Aux) (included : branch ∈ inspect edge) :
    Invariant inventory inspect (advance state edge branch) := by
  have chosen := pending_some inventory rigid state edge selected
  have children := support edge chosen.1 branch included
  refine ⟨?_, ?_, List.nodup_cons.mpr ⟨chosen.2.2, invariant.distinct⟩, ?_, ?_, ?_, ?_⟩
  · intro child member
    exact (List.mem_append.mp member).elim (fun member => children member)
      (fun member => invariant.edges_supported member)
  · intro candidate member
    exact (List.mem_cons.mp member).elim (fun same => same ▸ chosen.1)
      (fun member => invariant.processed_supported member)
  · exact congrArg (edge :: ·) invariant.trace_keys
  · intro candidate selectedBranch member
    rcases List.mem_cons.mp member with same | previous
    · cases same
      exact included
    · exact invariant.valid_branch candidate selectedBranch previous
  · intro candidate selectedBranch member child present
    rcases List.mem_cons.mp member with same | previous
    · cases same
      exact List.mem_append_left _ present
    · exact List.mem_append_right _ (invariant.children_present candidate selectedBranch previous present)
  · intro candidate selectedBranch member item present
    rcases List.mem_cons.mp member with same | previous
    · cases same
      exact List.mem_append_left _ present
    · exact List.mem_append_right _ (invariant.aux_present candidate selectedBranch previous present)

theorem Invariant.processed_branch (inventory : List Edge) (inspect : Edge → List (Branch Edge Aux))
    (state : State Edge Aux) (invariant : Invariant inventory inspect state)
    (edge : Edge) (processed : edge ∈ state.processed) :
    ∃ branch ∈ inspect edge, (edge, branch) ∈ state.trace ∧
      branch.children ⊆ state.edges ∧ branch.aux ⊆ state.aux := by
  rw [← invariant.trace_keys] at processed
  obtain ⟨⟨candidate, branch⟩, member, same⟩ := List.mem_map.mp processed
  change candidate = edge at same
  subst candidate
  exact ⟨branch, invariant.valid_branch edge branch member, member,
    invariant.children_present edge branch member, invariant.aux_present edge branch member⟩

theorem Invariant.closed [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (state : State Edge Aux)
    (invariant : Invariant inventory inspect state) (rigidSupport : RigidSupported inventory rigid)
    (finished : pending inventory rigid state = none) : Closed rigid inspect state := by
  intro edge active
  have listed := rigidSupport state.edges invariant.edges_supported active
  have processed := (pending_none inventory rigid state).mp finished edge listed active
  exact invariant.processed_branch inventory inspect state edge processed

private theorem explore_invariant [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (support : InspectionSupported inventory inspect)
    (capacity : Nat) (state final : State Edge Aux) (invariant : Invariant inventory inspect state)
    (returned : final ∈ explore inventory rigid inspect capacity state) : Invariant inventory inspect final := by
  induction capacity generalizing state with
  | zero =>
      have same : final = state := List.mem_singleton.mp returned
      subst final
      exact invariant
  | succ capacity ih =>
      cases found : pending inventory rigid state with
      | none =>
          have same : final = state := by simpa only [explore, found, List.mem_singleton] using returned
          subst final
          exact invariant
      | some edge =>
          simp only [explore, found] at returned
          obtain ⟨branch, included, later⟩ := List.mem_flatMap.mp returned
          exact ih (advance state edge branch)
            (invariant.advance inventory rigid inspect state support edge found branch included) later

private theorem saturated (inventory processed : List Edge) (supported : processed ⊆ inventory)
    (distinct : processed.Nodup) (full : inventory.length ≤ processed.length)
    (edge : Edge) (listed : edge ∈ inventory) : edge ∈ processed := by
  classical
  by_cases present : edge ∈ processed
  · exact present
  · have enlarged : (edge :: processed).Nodup := List.nodup_cons.mpr ⟨present, distinct⟩
    have bound := enlarged.length_le_of_subset (l₂ := inventory) (by
      intro candidate member
      exact (List.mem_cons.mp member).elim (fun same => same ▸ listed) (fun member => supported member))
    simp only [List.length_cons] at bound
    omega

private theorem explore_finished [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (support : InspectionSupported inventory inspect)
    (capacity : Nat) (state final : State Edge Aux) (invariant : Invariant inventory inspect state)
    (enough : inventory.length ≤ state.processed.length + capacity)
    (returned : final ∈ explore inventory rigid inspect capacity state) :
    pending inventory rigid final = none := by
  induction capacity generalizing state with
  | zero =>
      have same : final = state := List.mem_singleton.mp returned
      subst final
      apply (pending_none inventory rigid state).mpr
      intro edge listed _
      exact saturated inventory state.processed invariant.processed_supported invariant.distinct
        (by simpa only [Nat.add_zero] using enough) edge listed
  | succ capacity ih =>
      cases found : pending inventory rigid state with
      | none =>
          have same : final = state := by simpa only [explore, found, List.mem_singleton] using returned
          subst final
          exact found
      | some edge =>
          simp only [explore, found] at returned
          obtain ⟨branch, included, later⟩ := List.mem_flatMap.mp returned
          apply ih (advance state edge branch)
            (invariant.advance inventory rigid inspect state support edge found branch included) ?_ later
          simp only [advance, List.length_cons]
          omega

theorem run_invariant [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (edges : List Edge) (aux : List Aux)
    (initialSupport : edges ⊆ inventory) (inspectionSupport : InspectionSupported inventory inspect)
    (final : State Edge Aux) (returned : final ∈ run inventory rigid inspect edges aux) :
    Invariant inventory inspect final :=
  explore_invariant inventory rigid inspect inspectionSupport inventory.length (initial edges aux) final
    (invariant_initial inventory inspect edges aux initialSupport) returned

/-- The internal capacity cannot end with any unprocessed inventory edge. -/
theorem run_finished [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (edges : List Edge) (aux : List Aux)
    (initialSupport : edges ⊆ inventory) (inspectionSupport : InspectionSupported inventory inspect)
    (final : State Edge Aux) (returned : final ∈ run inventory rigid inspect edges aux) :
    pending inventory rigid final = none :=
  explore_finished inventory rigid inspect inspectionSupport inventory.length (initial edges aux) final
    (invariant_initial inventory inspect edges aux initialSupport) (by simp [initial]) returned

theorem run_closed [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (edges : List Edge) (aux : List Aux)
    (initialSupport : edges ⊆ inventory) (inspectionSupport : InspectionSupported inventory inspect)
    (rigidSupport : RigidSupported inventory rigid) (final : State Edge Aux)
    (returned : final ∈ run inventory rigid inspect edges aux) : Closed rigid inspect final :=
  (run_invariant inventory rigid inspect edges aux initialSupport inspectionSupport final returned).closed
    inventory rigid inspect final rigidSupport
    (run_finished inventory rigid inspect edges aux initialSupport inspectionSupport final returned)

/-- Every trace records at most one inspection of each finite inventory
edge. Repeated children and non-monotone rigid discovery do not change this. -/
theorem run_bound [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (edges : List Edge) (aux : List Aux)
    (initialSupport : edges ⊆ inventory) (inspectionSupport : InspectionSupported inventory inspect)
    (final : State Edge Aux) (returned : final ∈ run inventory rigid inspect edges aux) :
    final.processed.Nodup ∧ final.processed ⊆ inventory ∧ final.edges ⊆ inventory ∧
      final.trace.length = final.processed.length ∧ final.trace.length ≤ inventory.length := by
  have invariant := run_invariant inventory rigid inspect edges aux initialSupport inspectionSupport final returned
  have lengths : final.trace.length = final.processed.length := by
    simpa only [List.length_map] using congrArg List.length invariant.trace_keys
  exact ⟨invariant.distinct, invariant.processed_supported, invariant.edges_supported, lengths,
    lengths ▸ invariant.distinct.length_le_of_subset invariant.processed_supported⟩

private theorem explore_retains [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (capacity : Nat) (state final : State Edge Aux)
    (returned : final ∈ explore inventory rigid inspect capacity state) :
    state.edges ⊆ final.edges ∧ state.aux ⊆ final.aux := by
  induction capacity generalizing state with
  | zero =>
      have same : final = state := List.mem_singleton.mp returned
      subst final
      exact ⟨fun _ member => member, fun _ member => member⟩
  | succ capacity ih =>
      cases found : pending inventory rigid state with
      | none =>
          have same : final = state := by simpa only [explore, found, List.mem_singleton] using returned
          subst final
          exact ⟨fun _ member => member, fun _ member => member⟩
      | some edge =>
          simp only [explore, found] at returned
          obtain ⟨branch, _, later⟩ := List.mem_flatMap.mp returned
          have preserved := ih (advance state edge branch) later
          exact ⟨fun _ member => preserved.1 (List.mem_append_right _ member),
            fun _ member => preserved.2 (List.mem_append_right _ member)⟩

/-- Retention is an unconditional property of the executable computation. -/
theorem run_retains [DecidableEq Edge] (inventory : List Edge) (rigid : List Edge → List Edge)
    (inspect : Edge → List (Branch Edge Aux)) (edges : List Edge) (aux : List Aux)
    (final : State Edge Aux) (returned : final ∈ run inventory rigid inspect edges aux) :
    edges ⊆ final.edges ∧ aux ⊆ final.aux :=
  explore_retains inventory rigid inspect inventory.length (initial edges aux) final returned

/-- Independent meanings of an ordinary edge list and an auxiliary list. -/
def State.Models (edgeHolds : Edge → Prop) (auxHolds : Aux → Prop) (state : State Edge Aux) : Prop :=
  (∀ edge ∈ state.edges, edgeHolds edge) ∧ ∀ item ∈ state.aux, auxHolds item

def Branch.Models (edgeHolds : Edge → Prop) (auxHolds : Aux → Prop) (branch : Branch Edge Aux) : Prop :=
  (∀ edge ∈ branch.children, edgeHolds edge) ∧ ∀ item ∈ branch.aux, auxHolds item

theorem models_advance (edgeHolds : Edge → Prop) (auxHolds : Aux → Prop)
    (state : State Edge Aux) (edge : Edge) (branch : Branch Edge Aux) :
    (advance state edge branch).Models edgeHolds auxHolds ↔
      state.Models edgeHolds auxHolds ∧ branch.Models edgeHolds auxHolds := by
  constructor
  · rintro ⟨edges, aux⟩
    exact ⟨⟨fun _ member => edges _ (List.mem_append_right _ member),
      fun _ member => aux _ (List.mem_append_right _ member)⟩,
      ⟨fun _ member => edges _ (List.mem_append_left _ member),
        fun _ member => aux _ (List.mem_append_left _ member)⟩⟩
  · rintro ⟨original, added⟩
    exact ⟨fun _ member => (List.mem_append.mp member).elim (added.1 _) (original.1 _),
      fun _ member => (List.mem_append.mp member).elim (added.2 _) (original.2 _)⟩

private theorem explore_models_exact [DecidableEq Edge] (inventory : List Edge)
    (rigid : List Edge → List Edge) (inspect : Edge → List (Branch Edge Aux))
    (edgeHolds : Edge → Prop) (auxHolds : Aux → Prop)
    (rigidSound : ∀ edges, (∀ edge ∈ edges, edgeHolds edge) →
      ∀ edge ∈ rigid edges, edgeHolds edge)
    (inspectionExact : ∀ current, ∀ edge ∈ inventory, edge ∈ rigid current →
      (edgeHolds edge ↔ ∃ branch ∈ inspect edge, branch.Models edgeHolds auxHolds))
    (capacity : Nat) (state : State Edge Aux) :
    state.Models edgeHolds auxHolds ↔
      ∃ final ∈ explore inventory rigid inspect capacity state, final.Models edgeHolds auxHolds := by
  induction capacity generalizing state with
  | zero => simp [explore]
  | succ capacity ih =>
      cases found : pending inventory rigid state with
      | none => simp [explore, found]
      | some edge =>
          constructor
          · intro models
            have chosen := pending_some inventory rigid state edge found
            have valid := rigidSound state.edges models.1 edge chosen.2.1
            obtain ⟨branch, included, branchModels⟩ :=
              (inspectionExact state.edges edge chosen.1 chosen.2.1).mp valid
            have extended := (models_advance edgeHolds auxHolds state edge branch).mpr ⟨models, branchModels⟩
            obtain ⟨final, returned, finalModels⟩ := (ih (advance state edge branch)).mp extended
            refine ⟨final, ?_, finalModels⟩
            simp only [explore, found]
            exact List.mem_flatMap.mpr ⟨branch, included, returned⟩
          · rintro ⟨final, returned, finalModels⟩
            simp only [explore, found] at returned
            obtain ⟨branch, _, later⟩ := List.mem_flatMap.mp returned
            have extended := (ih (advance state edge branch)).mpr ⟨final, later, finalModels⟩
            exact (models_advance edgeHolds auxHolds state edge branch).mp extended |>.1

/-- The inspection law and rigid entailment are explicit theorem hypotheses,
not fields of the interpretation or of a purported solution. The statement
holds for each arbitrary independent edge/auxiliary interpretation. -/
theorem run_models_exact_selected [DecidableEq Edge] (inventory : List Edge)
    (rigid : List Edge → List Edge) (inspect : Edge → List (Branch Edge Aux))
    (edgeHolds : Edge → Prop) (auxHolds : Aux → Prop)
    (rigidSound : ∀ edges, (∀ edge ∈ edges, edgeHolds edge) →
      ∀ edge ∈ rigid edges, edgeHolds edge)
    (inspectionExact : ∀ current, ∀ edge ∈ inventory, edge ∈ rigid current →
      (edgeHolds edge ↔ ∃ branch ∈ inspect edge, branch.Models edgeHolds auxHolds))
    (edges : List Edge) (aux : List Aux) :
    ((∀ edge ∈ edges, edgeHolds edge) ∧ ∀ item ∈ aux, auxHolds item) ↔
      ∃ final ∈ run inventory rigid inspect edges aux, final.Models edgeHolds auxHolds :=
  explore_models_exact inventory rigid inspect edgeHolds auxHolds rigidSound inspectionExact
    inventory.length (initial edges aux)

/-- A convenient specialization when every inventory edge has the stated
inspection equivalence, whether or not the rigid computation selects it. -/
theorem run_models_exact [DecidableEq Edge] (inventory : List Edge)
    (rigid : List Edge → List Edge) (inspect : Edge → List (Branch Edge Aux))
    (edgeHolds : Edge → Prop) (auxHolds : Aux → Prop)
    (rigidSound : ∀ edges, (∀ edge ∈ edges, edgeHolds edge) →
      ∀ edge ∈ rigid edges, edgeHolds edge)
    (inspectionExact : ∀ edge ∈ inventory,
      edgeHolds edge ↔ ∃ branch ∈ inspect edge, branch.Models edgeHolds auxHolds)
    (edges : List Edge) (aux : List Aux) :
    ((∀ edge ∈ edges, edgeHolds edge) ∧ ∀ item ∈ aux, auxHolds item) ↔
      ∃ final ∈ run inventory rigid inspect edges aux, final.Models edgeHolds auxHolds :=
  run_models_exact_selected inventory rigid inspect edgeHolds auxHolds rigidSound
    (fun _ edge listed _ => inspectionExact edge listed) edges aux

/-- Under explicit finite-support and exact-inspection hypotheses, initial
models correspond exactly to models of returned, genuinely closed branches. -/
theorem run_closed_models_exact [DecidableEq Edge] (inventory : List Edge)
    (rigid : List Edge → List Edge) (inspect : Edge → List (Branch Edge Aux))
    (edgeHolds : Edge → Prop) (auxHolds : Aux → Prop)
    (rigidSound : ∀ edges, (∀ edge ∈ edges, edgeHolds edge) →
      ∀ edge ∈ rigid edges, edgeHolds edge)
    (inspectionExact : ∀ edge ∈ inventory,
      edgeHolds edge ↔ ∃ branch ∈ inspect edge, branch.Models edgeHolds auxHolds)
    (edges : List Edge) (aux : List Aux) (initialSupport : edges ⊆ inventory)
    (inspectionSupport : InspectionSupported inventory inspect) (rigidSupport : RigidSupported inventory rigid) :
    ((∀ edge ∈ edges, edgeHolds edge) ∧ ∀ item ∈ aux, auxHolds item) ↔
      ∃ final ∈ run inventory rigid inspect edges aux,
        Closed rigid inspect final ∧ final.Models edgeHolds auxHolds := by
  constructor
  · intro models
    obtain ⟨final, returned, valid⟩ :=
      (run_models_exact inventory rigid inspect edgeHolds auxHolds rigidSound inspectionExact edges aux).mp models
    exact ⟨final, returned,
      run_closed inventory rigid inspect edges aux initialSupport inspectionSupport rigidSupport final returned, valid⟩
  · rintro ⟨final, returned, _, valid⟩
    exact (run_models_exact inventory rigid inspect edgeHolds auxHolds rigidSound inspectionExact edges aux).mpr
      ⟨final, returned, valid⟩

end Yulang.FiniteBranchingWorklist
