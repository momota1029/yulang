import Std

/-!
# Dependency-local module rebuilding

A node is a module or an already contracted import SCC. Its dependencies have
smaller indices. Compilation receives only the node's source/key and the ordered
interfaces of these dependencies. The output type is arbitrary: it may include
errors, residual qualifiers, dictionary dependencies, and nominal identities.

`dirty` computes the reverse dependency closure in one topological pass.
`rebuild` actually chooses between compiling a node and reusing its cached
artifact, recording the indices at which compilation is called. There is no
solver-success or caller-fuel premise. The proof uses exact interface equality;
it does not assume or establish a complete type normalizer.
-/

namespace Yulang.ModuleIncremental

universe u v
variable {Source : Type u} {Interface : Type v}

/-- Topological dependencies; duplicates and dependency order are retained. -/
abbrev Dependencies := (node : Nat) → List (Fin node)

def build (compile : Source → List Interface → Interface)
    (source : Nat → Source) (dependencies : Dependencies) : (n : Nat) → Fin n → Interface
  | 0 => Fin.elim0
  | n + 1 =>
      let previous := build compile source dependencies n
      Fin.lastCases (compile (source n) ((dependencies n).map previous)) previous

def dirty (changed : Nat → Bool) (dependencies : Dependencies) : (n : Nat) → Fin n → Bool
  | 0 => Fin.elim0
  | n + 1 =>
      let previous := dirty changed dependencies n
      Fin.lastCases (changed n || (dependencies n).any previous) previous

/-- Independent finite-path judgment for the modules affected by a change. -/
inductive Affected (changed : Nat → Bool) (dependencies : Dependencies) : Nat → Prop where
  | changed (node : Nat) : changed node = true → Affected changed dependencies node
  | dependency (node : Nat) (dependency : Fin node) :
      dependency ∈ dependencies node → Affected changed dependencies dependency.val →
      Affected changed dependencies node

theorem affected_iff (changed : Nat → Bool) (dependencies : Dependencies) (node : Nat) :
    Affected changed dependencies node ↔ changed node = true ∨
      ∃ dependency ∈ dependencies node, Affected changed dependencies dependency.val := by
  constructor
  · intro affected
    cases affected with
    | changed _ yes => exact Or.inl yes
    | dependency _ dependency member prior => exact Or.inr ⟨dependency, member, prior⟩
  · rintro (yes | ⟨dependency, member, prior⟩)
    · exact .changed node yes
    · exact .dependency node dependency member prior

theorem dirty_exact (changed : Nat → Bool) (dependencies : Dependencies)
    (n : Nat) (node : Fin n) :
    dirty changed dependencies n node = true ↔ Affected changed dependencies node.val := by
  induction n with
  | zero => exact Fin.elim0 node
  | succ n ih =>
      refine Fin.lastCases ?_ (fun previous => ?_) node
      · simp only [dirty, Fin.lastCases_last, Bool.or_eq_true, List.any_eq_true, Fin.val_last]
        rw [affected_iff]
        exact or_congr Iff.rfl (exists_congr fun dependency => and_congr_right fun _ => ih dependency)
      · simpa only [dirty, Fin.lastCases_castSucc, Fin.val_castSucc] using ih previous

/-- Changing sources can alter only nodes in the computed reverse closure. -/
theorem clean_build_equal (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (dependencies : Dependencies) (changed : Nat → Bool)
    (sources : ∀ node, changed node = false → before node = after node)
    (n : Nat) (node : Fin n) (clean : dirty changed dependencies n node = false) :
    build compile before dependencies n node = build compile after dependencies n node := by
  induction n with
  | zero => exact Fin.elim0 node
  | succ n ih =>
      refine Fin.lastCases ?_ (fun previous => ?_) node clean
      · intro lastClean
        simp only [dirty, Fin.lastCases_last, Bool.or_eq_false_iff, List.any_eq_false] at lastClean
        simp only [build, Fin.lastCases_last, sources n lastClean.1]
        congr 1
        apply List.map_congr_left
        intro dependency member
        exact ih dependency (by simpa using lastClean.2 dependency member)
      · intro previousClean
        simpa only [build, Fin.lastCases_castSucc] using
          ih previous (by simpa only [dirty, Fin.lastCases_castSucc] using previousClean)

/-- The second result is the actual compilation-call trace, not an estimate. -/
def rebuild (compile : Source → List Interface → Interface)
    (source : Nat → Source) (dependencies : Dependencies) (changed : Nat → Bool) :
    (n : Nat) → (Fin n → Interface) → (Fin n → Interface) × List Nat
  | 0, _ => (Fin.elim0, [])
  | n + 1, cached =>
      let previous := rebuild compile source dependencies changed n (fun i => cached i.castSucc)
      if dirty changed dependencies (n + 1) (Fin.last n) then
        (Fin.lastCases (compile (source n) ((dependencies n).map previous.1)) previous.1,
          previous.2 ++ [n])
      else (Fin.lastCases (cached (Fin.last n)) previous.1, previous.2)

/-- Reusing exactly the clean entries of a valid old build produces the same
artifact table as a full new build, even when `Interface` includes errors. -/
theorem rebuild_exact (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (dependencies : Dependencies) (changed : Nat → Bool)
    (sources : ∀ node, changed node = false → before node = after node) (n : Nat) :
    (rebuild compile after dependencies changed n (build compile before dependencies n)).1 =
      build compile after dependencies n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rebuild, build, Fin.lastCases_castSucc]
      split
      · simp only [ih]
      · rename_i clean
        have lastClean : dirty changed dependencies (n + 1) (Fin.last n) = false :=
          by simpa using clean
        have unchanged := clean_build_equal compile before after dependencies changed sources
          (n + 1) (Fin.last n) lastClean
        simp only [build, Fin.lastCases_last] at unchanged
        simp only [Fin.lastCases_last, ih, unchanged]

theorem rebuild_valid_cache (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (dependencies : Dependencies) (changed : Nat → Bool)
    (sources : ∀ node, changed node = false → before node = after node)
    (n : Nat) (cached : Fin n → Interface)
    (valid : ∀ node, cached node = build compile before dependencies n node) :
    (rebuild compile after dependencies changed n cached).1 = build compile after dependencies n := by
  have same : cached = build compile before dependencies n := funext valid
  rw [same]
  exact rebuild_exact compile before after dependencies changed sources n

theorem rebuild_trace (compile : Source → List Interface → Interface)
    (source : Nat → Source) (dependencies : Dependencies) (changed : Nat → Bool)
    (n : Nat) (cached : Fin n → Interface) :
    (rebuild compile source dependencies changed n cached).2 =
      ((List.finRange n).filter (dirty changed dependencies n)).map Fin.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rebuild]
      split <;> simp only [ih, List.finRange_succ_last, List.filter_append, List.map_append]
      all_goals simp_all [List.filter_map, dirty, Function.comp_def]

theorem rebuild_calls_le (compile : Source → List Interface → Interface)
    (source : Nat → Source) (dependencies : Dependencies) (changed : Nat → Bool)
    (n : Nat) (cached : Fin n → Interface) :
    (rebuild compile source dependencies changed n cached).2.length ≤ n := by
  rw [rebuild_trace, List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem rebuild_called_iff (compile : Source → List Interface → Interface)
    (source : Nat → Source) (dependencies : Dependencies) (changed : Nat → Bool)
    (n : Nat) (cached : Fin n → Interface) (node : Nat) :
    node ∈ (rebuild compile source dependencies changed n cached).2 ↔
      node < n ∧ Affected changed dependencies node := by
  rw [rebuild_trace]
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨index, marked, same⟩
    subst node
    exact ⟨index.isLt, (dirty_exact changed dependencies n index).mp marked⟩
  · rintro ⟨within, affected⟩
    exact ⟨⟨node, within⟩, (dirty_exact changed dependencies n ⟨node, within⟩).mpr affected, rfl⟩

/-- Import edits are allowed too. Only a clean node must retain its own key
and dependency list; affectedness follows the new graph. -/
theorem clean_build_changed_graph (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies)
    (changed : Nat → Bool)
    (keys : ∀ node, changed node = false →
      before node = after node ∧ oldDependencies node = newDependencies node)
    (n : Nat) (node : Fin n) (clean : dirty changed newDependencies n node = false) :
    build compile before oldDependencies n node = build compile after newDependencies n node := by
  induction n with
  | zero => exact Fin.elim0 node
  | succ n ih =>
      refine Fin.lastCases ?_ (fun previous => ?_) node clean
      · intro lastClean
        simp only [dirty, Fin.lastCases_last, Bool.or_eq_false_iff, List.any_eq_false] at lastClean
        obtain ⟨sourceEqual, dependenciesEqual⟩ := keys n lastClean.1
        simp only [build, Fin.lastCases_last, sourceEqual, dependenciesEqual]
        congr 1
        apply List.map_congr_left
        intro dependency member
        exact ih dependency (by simpa using lastClean.2 dependency member)
      · intro previousClean
        simpa only [build, Fin.lastCases_castSucc] using
          ih previous (by simpa only [dirty, Fin.lastCases_castSucc] using previousClean)

theorem rebuild_changed_graph_exact (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies)
    (changed : Nat → Bool)
    (keys : ∀ node, changed node = false →
      before node = after node ∧ oldDependencies node = newDependencies node) (n : Nat) :
    (rebuild compile after newDependencies changed n (build compile before oldDependencies n)).1 =
      build compile after newDependencies n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rebuild, build, Fin.lastCases_castSucc]
      split
      · simp only [ih]
      · rename_i clean
        have lastClean : dirty changed newDependencies (n + 1) (Fin.last n) = false := by
          simpa using clean
        have unchanged := clean_build_changed_graph compile before after oldDependencies
          newDependencies changed keys (n + 1) (Fin.last n) lastClean
        simp only [build, Fin.lastCases_last] at unchanged
        simp only [Fin.lastCases_last, ih, unchanged]

/-- Any subsequent deterministic display/normalization observes equal results.
This corollary does not posit that the normalizer decides type equivalence. -/
theorem rebuild_normal_forms {Normal : Type} (normalize : Interface → Normal)
    (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies)
    (changed : Nat → Bool)
    (keys : ∀ node, changed node = false →
      before node = after node ∧ oldDependencies node = newDependencies node)
    (n : Nat) (node : Fin n) :
    normalize ((rebuild compile after newDependencies changed n
      (build compile before oldDependencies n)).1 node) =
        normalize (build compile after newDependencies n node) := by
  rw [rebuild_changed_graph_exact compile before after oldDependencies newDependencies changed keys]

/-- A module key contains every input consulted by compilation. Equal source
keys and equal ordered dependency interfaces give the same cached artifact. -/
theorem module_cache_sound (compile : Source → List Interface → Interface)
    (before after : Source) (oldDependencies newDependencies : List Interface)
    (sourceEqual : before = after) (interfacesEqual : oldDependencies = newDependencies) :
    compile before oldDependencies = compile after newDependencies := by
  rw [sourceEqual, interfacesEqual]

end Yulang.ModuleIncremental
