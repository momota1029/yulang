import Yulang.ModuleIncremental

/-!
# Dependency-ready schedules compute the same module artifacts

Unlike a scheduler of already supplied snapshots, `step` reads previously
compiled dependency artifacts, passes them to the actual compiler, and stores
its result. A step rejects both a missing dependency and a repeated node.
`Legal` describes these conditions using only the dependency graph and the
already processed IDs; it does not assume successful compilation or a result.

The graph consists of modules or already contracted SCCs with smaller-indexed
dependencies, exactly as in `ModuleIncremental`. The source key and the ordered
dependency interfaces are the compiler's complete inputs. Output artifacts may
include errors. Source dependency extraction and a solver's realization of
this pure, dependency-local compile operation remain separate obligations.
-/

namespace Yulang.ModuleScheduling

open ModuleIncremental

universe u v
variable {Source : Type u} {Interface : Type v}

abbrev Store (Interface : Type v) := Nat → Option Interface

def canonical (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) (node : Nat) : Interface :=
  build compile source dependencies (node + 1) (Fin.last node)

theorem build_at (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) (n : Nat) (node : Fin n) :
    build compile source dependencies n node = canonical compile source dependencies node.val := by
  induction n with
  | zero => exact Fin.elim0 node
  | succ n ih =>
      refine Fin.lastCases ?_ (fun earlier => ?_) node
      · rfl
      · simpa only [build, Fin.lastCases_castSucc, Fin.val_castSucc] using ih earlier

theorem canonical_equation (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) (node : Nat) :
    canonical compile source dependencies node =
      compile (source node) ((dependencies node).map fun prior =>
        canonical compile source dependencies prior.val) := by
  have head : canonical compile source dependencies node =
      compile (source node) ((dependencies node).map (build compile source dependencies node)) := by
    simp only [canonical, build, Fin.lastCases_last]
  rw [head]
  congr 1
  apply List.map_congr_left
  intro prior _
  exact build_at compile source dependencies node prior

def collect (artifacts : Store Interface) : List Nat → Option (List Interface)
  | [] => some []
  | node :: rest => do
      let first ← artifacts node
      let tail ← collect artifacts rest
      pure (first :: tail)

theorem collect_known (artifacts : Store Interface) (value : Nat → Interface) (nodes : List Nat)
    (known : ∀ node ∈ nodes, artifacts node = some (value node)) :
    collect artifacts nodes = some (nodes.map value) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      simp only [collect, known node List.mem_cons_self,
        ih (fun prior member => known prior (List.mem_cons_of_mem _ member)), List.map_cons]
      rfl

def write (artifacts : Store Interface) (node : Nat) (value : Interface) : Store Interface :=
  fun current => if current = node then some value else artifacts current

def step (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) (node : Nat) (artifacts : Store Interface) : Option (Store Interface) :=
  match artifacts node with
  | some _ => none
  | none => match collect artifacts ((dependencies node).map Fin.val) with
    | none => none
    | some inputs => some (write artifacts node (compile (source node) inputs))

def Legal (dependencies : Dependencies) (done : List Nat) : List Nat → Prop
  | [] => True
  | node :: rest => node ∉ done ∧
      (∀ prior ∈ dependencies node, prior.val ∈ done) ∧ Legal dependencies (node :: done) rest

def Exact (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) (artifacts : Store Interface) (done : List Nat) : Prop :=
  ∀ node, artifacts node = if node ∈ done then some (canonical compile source dependencies node) else none

theorem empty_exact (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) : Exact compile source dependencies (fun _ => none) [] := by
  intro node
  simp

/-- A dependency-ready step actually obtains its inputs from the store and
calls `compile`. Its resulting artifact is the canonical dependency build. -/
theorem step_ready (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) (done : List Nat) (artifacts : Store Interface)
    (valid : Exact compile source dependencies artifacts done) (node : Nat)
    (fresh : node ∉ done) (ready : ∀ prior ∈ dependencies node, prior.val ∈ done) :
    ∃ next, step compile source dependencies node artifacts = some next ∧
      Exact compile source dependencies next (node :: done) := by
  have absent : artifacts node = none := by simp only [valid node, fresh, ↓reduceIte]
  have available : collect artifacts ((dependencies node).map Fin.val) =
      some ((dependencies node).map fun prior => canonical compile source dependencies prior.val) := by
    have collected := collect_known artifacts (canonical compile source dependencies)
      ((dependencies node).map Fin.val) (by
        intro prior member
        obtain ⟨index, present, same⟩ := List.mem_map.mp member
        subst prior
        simp only [valid index.val, ite_eq_left_iff]
        exact fun absent => False.elim (absent (ready index present)))
    simpa only [List.map_map, Function.comp_def] using collected
  refine ⟨write artifacts node (canonical compile source dependencies node), ?_, ?_⟩
  · simp only [step, absent, available, ← canonical_equation]
  · intro current
    by_cases same : current = node
    · subst current
      simp [write]
    · simp [write, same, valid current]

/-- Successful steps append an actual compile-call ID to the trace. -/
def run (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) : List Nat → Store Interface → Option (Store Interface × List Nat)
  | [], artifacts => some (artifacts, [])
  | node :: rest, artifacts =>
      match step compile source dependencies node artifacts with
      | none => none
      | some next => match run compile source dependencies rest next with
        | none => none
        | some (result, calls) => some (result, node :: calls)

/-- Graph legality, rather than successful inference or a supplied final
snapshot, implies that the schedule runs and computes the exact artifacts. -/
theorem run_legal (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) (done order : List Nat) (artifacts : Store Interface)
    (valid : Exact compile source dependencies artifacts done) (legal : Legal dependencies done order) :
    ∃ result, run compile source dependencies order artifacts = some (result, order) ∧
      Exact compile source dependencies result (order.reverse ++ done) := by
  induction order generalizing done artifacts with
  | nil => exact ⟨artifacts, rfl, valid⟩
  | cons node rest ih =>
      obtain ⟨next, stepped, nextValid⟩ := step_ready compile source dependencies done artifacts valid node legal.1 legal.2.1
      obtain ⟨result, completed, resultValid⟩ := ih (node :: done) next nextValid legal.2.2
      refine ⟨result, ?_, ?_⟩
      · simp only [run, stepped, completed]
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using resultValid

theorem legal_not_done (dependencies : Dependencies) (done order : List Nat)
    (legal : Legal dependencies done order) (node : Nat) (present : node ∈ order) : node ∉ done := by
  induction order generalizing done with
  | nil => simp at present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with same | later
      · subst node
        exact legal.1
      · have fresh := ih (first :: done) legal.2.2 later
        exact fun member => fresh (List.mem_cons_of_mem _ member)

theorem legal_nodup (dependencies : Dependencies) (done order : List Nat)
    (legal : Legal dependencies done order) : order.Nodup := by
  induction order generalizing done with
  | nil => exact List.nodup_nil
  | cons node rest ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih (node :: done) legal.2.2⟩
      intro repeated
      exact legal_not_done dependencies (node :: done) rest legal.2.2 node repeated List.mem_cons_self

theorem legal_length_le (dependencies : Dependencies) (done order : List Nat)
    (legal : Legal dependencies done order) (n : Nat) (within : ∀ node ∈ order, node < n) :
    order.length ≤ n := by
  have subset : order ⊆ List.range n := fun node member => List.mem_range.mpr (within node member)
  simpa only [List.length_range] using (legal_nodup dependencies done order legal).length_le_of_subset subset

/-- Every graph-legal schedule compiles each scheduled node once, with at
most `n` compiler calls when its IDs are drawn from the first `n` nodes. -/
theorem run_once_bound (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) (order : List Nat) (legal : Legal dependencies [] order)
    (n : Nat) (within : ∀ node ∈ order, node < n) :
    ∃ artifacts calls,
      run compile source dependencies order (fun _ => none) = some (artifacts, calls) ∧
      calls = order ∧ calls.Nodup ∧ calls.length ≤ n := by
  obtain ⟨artifacts, completed, _⟩ := run_legal compile source dependencies [] order
    (fun _ => none) (empty_exact compile source dependencies) legal
  exact ⟨artifacts, order, completed, rfl, legal_nodup dependencies [] order legal,
    legal_length_le dependencies [] order legal n within⟩

/-- A complete legal schedule gives the same finite table as the existing
ascending `ModuleIncremental.build`; unprocessed IDs remain absent. -/
theorem run_build_exact (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) (order : List Nat) (legal : Legal dependencies [] order)
    (n : Nat) (covers : ∀ node, node ∈ order ↔ node < n) :
    ∃ artifacts,
      run compile source dependencies order (fun _ => none) = some (artifacts, order) ∧
      (∀ node : Fin n, artifacts node.val = some (build compile source dependencies n node)) ∧
      (∀ node, n ≤ node → artifacts node = none) := by
  obtain ⟨artifacts, completed, valid⟩ := run_legal compile source dependencies [] order
    (fun _ => none) (empty_exact compile source dependencies) legal
  refine ⟨artifacts, completed, ?_, ?_⟩
  · intro node
    rw [valid node.val, build_at]
    simp only [List.mem_append, List.mem_reverse, List.not_mem_nil, or_false, covers node.val,
      ite_eq_left_iff]
    exact fun impossible => False.elim (impossible node.isLt)
  · intro node outside
    rw [valid node]
    simp only [List.mem_append, List.mem_reverse, List.not_mem_nil, or_false, covers node,
      show ¬node < n by omega, ↓reduceIte]

/-- Two legal schedules of the same completed nodes return the same complete
artifact table. Their call traces retain their possibly different orders. -/
theorem schedule_independent (compile : Source → List Interface → Interface) (source : Nat → Source)
    (dependencies : Dependencies) (first last : List Nat)
    (firstLegal : Legal dependencies [] first) (lastLegal : Legal dependencies [] last)
    (sameNodes : ∀ node, node ∈ first ↔ node ∈ last) :
    ∃ artifacts,
      run compile source dependencies first (fun _ => none) = some (artifacts, first) ∧
      run compile source dependencies last (fun _ => none) = some (artifacts, last) := by
  obtain ⟨firstResult, firstRun, firstExact⟩ := run_legal compile source dependencies [] first
    (fun _ => none) (empty_exact compile source dependencies) firstLegal
  obtain ⟨lastResult, lastRun, lastExact⟩ := run_legal compile source dependencies [] last
    (fun _ => none) (empty_exact compile source dependencies) lastLegal
  have equal : firstResult = lastResult := by
    funext node
    rw [firstExact node, lastExact node]
    simp only [List.mem_append, List.mem_reverse, List.not_mem_nil, or_false, sameNodes node]
  exact ⟨firstResult, firstRun, equal ▸ lastRun⟩

end Yulang.ModuleScheduling
