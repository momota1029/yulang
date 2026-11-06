import Yulang.ModuleIncremental

/-!
# Reuse based on unchanged dependency interfaces

This executable refinement checks the actual old/new source keys and ordered
dependency artifacts. It can stop recompilation at an unchanged interface,
even when a dependency's source was changed. Equality is decidable equality of
the complete stored artifact, not an assumed semantic type-equivalence oracle.
As in `ModuleIncremental`, outputs may include errors and dictionary metadata.
-/

namespace Yulang.ModuleInterfaceCache

open ModuleIncremental

universe u v
variable {Source : Type u} {Interface : Type v}
  [DecidableEq Source] [DecidableEq Interface]

def rebuild (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies) :
    (n : Nat) → (Fin n → Interface) → (Fin n → Interface) × List Nat
  | 0, _ => (Fin.elim0, [])
  | n + 1, cached =>
      let previous := rebuild compile before after oldDependencies newDependencies n
        (fun i => cached i.castSucc)
      let arguments := (newDependencies n).map previous.1
      if before n = after n ∧
          (oldDependencies n).map (fun i => cached i.castSucc) = arguments then
        (Fin.lastCases (cached (Fin.last n)) previous.1, previous.2)
      else
        (Fin.lastCases (compile (after n) arguments) previous.1, previous.2 ++ [n])

/-- No caller-supplied dirty set, successful compilation or solver solution
is required. The original cache is an actual old complete build. -/
theorem rebuild_exact (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies) (n : Nat) :
    (rebuild compile before after oldDependencies newDependencies n
      (build compile before oldDependencies n)).1 = build compile after newDependencies n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rebuild, build, Fin.lastCases_castSucc]
      split
      · rename_i same
        simp only [ih] at same ⊢
        simp only [Fin.lastCases_last, same.1, same.2]
      · simp only [ih]

theorem rebuild_valid_cache (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies)
    (n : Nat) (cached : Fin n → Interface)
    (valid : ∀ node, cached node = build compile before oldDependencies n node) :
    (rebuild compile before after oldDependencies newDependencies n cached).1 =
      build compile after newDependencies n := by
  have same : cached = build compile before oldDependencies n := funext valid
  rw [same]
  exact rebuild_exact compile before after oldDependencies newDependencies n

/-- The complete inputs actually read by one pure module compilation. -/
def sameInput (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies) (node : Nat) : Bool :=
  decide (before node = after node ∧
    (oldDependencies node).map (build compile before oldDependencies node) =
      (newDependencies node).map (build compile after newDependencies node))

theorem rebuild_trace (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies) (n : Nat) :
    (rebuild compile before after oldDependencies newDependencies n
      (build compile before oldDependencies n)).2 =
        (List.range n).filter (fun node => !sameInput compile before after oldDependencies newDependencies node) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rebuild, build, Fin.lastCases_castSucc, rebuild_exact]
      split <;> simp_all [List.range_succ, List.filter_append, sameInput]
      by_cases sameSource : before n = after n <;> simp_all

theorem rebuild_called_iff (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies)
    (n node : Nat) :
    node ∈ (rebuild compile before after oldDependencies newDependencies n
      (build compile before oldDependencies n)).2 ↔
      node < n ∧ sameInput compile before after oldDependencies newDependencies node = false := by
  simp only [rebuild_trace, List.mem_filter, List.mem_range, Bool.not_eq_true']

theorem rebuild_calls_le (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies) (n : Nat) :
    (rebuild compile before after oldDependencies newDependencies n
      (build compile before oldDependencies n)).2.length ≤ n := by
  rw [rebuild_trace]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem rebuild_calls_nodup (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies) (n : Nat) :
    (rebuild compile before after oldDependencies newDependencies n
      (build compile before oldDependencies n)).2.Nodup := by
  rw [rebuild_trace]
  exact List.Pairwise.filter _ List.nodup_range

theorem clean_same_input (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies)
    (changed : Nat → Bool)
    (keys : ∀ node, changed node = false →
      before node = after node ∧ oldDependencies node = newDependencies node)
    (node : Nat) (clean : dirty changed newDependencies (node + 1) (Fin.last node) = false) :
    sameInput compile before after oldDependencies newDependencies node = true := by
  simp only [dirty, Fin.lastCases_last, Bool.or_eq_false_iff, List.any_eq_false] at clean
  obtain ⟨sourceEqual, dependenciesEqual⟩ := keys node clean.1
  simp only [sameInput, decide_eq_true_eq]
  refine ⟨sourceEqual, ?_⟩
  rw [dependenciesEqual]
  apply List.map_congr_left
  intro dependency member
  exact clean_build_changed_graph compile before after oldDependencies newDependencies changed keys
    node dependency (by simpa using clean.2 dependency member)

/-- Interface checks can shrink the affected range, and never compile a
node outside the finite reverse dependency closure computed from changes. -/
theorem called_implies_affected (compile : Source → List Interface → Interface)
    (before after : Nat → Source) (oldDependencies newDependencies : Dependencies)
    (changed : Nat → Bool)
    (keys : ∀ node, changed node = false →
      before node = after node ∧ oldDependencies node = newDependencies node)
    (n node : Nat)
    (called : node ∈ (rebuild compile before after oldDependencies newDependencies n
      (build compile before oldDependencies n)).2) : Affected changed newDependencies node := by
  have different := (rebuild_called_iff compile before after oldDependencies newDependencies n node).mp called
  apply (dirty_exact changed newDependencies (node + 1) (Fin.last node)).mp
  cases marked : dirty changed newDependencies (node + 1) (Fin.last node) with
  | true => rfl
  | false =>
      have same := clean_same_input compile before after oldDependencies newDependencies changed keys node marked
      simp only [different.2] at same
      cases same

namespace Examples

def chainDependencies : Dependencies
  | 0 => []
  | n + 1 => [Fin.last n]

/-- Changing the first module while preserving its interface recompiles that
module alone; the two dependent modules reuse their old artifacts. -/
theorem unchanged_interface_stops_recompilation :
    let compile := fun (source : Nat) (dependencies : List Nat) => (source + dependencies.sum) % 2
    let before := fun (_ : Nat) => 0
    let after := fun (node : Nat) => if node = 0 then 2 else 0
    (rebuild compile before after chainDependencies chainDependencies 3
      (build compile before chainDependencies 3)).2 = [0] := by
  decide

end Examples

end Yulang.ModuleInterfaceCache
