import Yulang.ParametricCastRules

/-!
# A finite universe derived from a cast problem

The enumerator is complete for every ground first-order tree of bounded node
count over a finite constructor alphabet. No constructor arity bound is assumed:
the node-count budget itself bounds the list of arguments. Constructor labels
come from the query's source and the finite declaration targets.

The budget is a proved bound on reachable *type size*, not a search-depth limit.
Ground declarations may increase size up to their fixed target; parametric
declarations never increase the instantiated size. All reachable instances fit
in the resulting finite list even when equal-size cast cycles exist.
-/

namespace Yulang.ParametricCasts

open Roles

mutual
  def boundedTerms (alphabet : List Nat) : Nat → List Term
    | 0 => []
    | budget + 1 => alphabet.flatMap fun name =>
        (boundedArgs alphabet budget).map (Term.app name)
  termination_by budget => 2 * budget
  decreasing_by omega

  def boundedArgs (alphabet : List Nat) : Nat → List (List Term)
    | 0 => [[]]
    | budget + 1 => [] :: (List.finRange (budget + 1)).flatMap fun index =>
        (boundedTerms alphabet (index.val + 1)).flatMap fun head =>
          (boundedArgs alphabet (budget - index.val)).map fun tail => head :: tail
  termination_by budget => 2 * budget + 1
  decreasing_by all_goals omega
end

mutual
  theorem boundedTerms_sound (alphabet : List Nat) (budget : Nat) (term : Term)
      (member : term ∈ boundedTerms alphabet budget) :
      Over alphabet term ∧ term.size ≤ budget := by
    cases budget with
    | zero => simp [boundedTerms] at member
    | succ budget =>
        rw [boundedTerms] at member
        obtain ⟨name, namePresent, member⟩ := List.mem_flatMap.mp member
        obtain ⟨args, argsPresent, rfl⟩ := List.mem_map.mp member
        have found := boundedArgs_sound alphabet budget args argsPresent
        exact ⟨⟨namePresent, found.1⟩, by simp only [Term.size]; omega⟩
  termination_by 2 * budget
  decreasing_by omega

  theorem boundedArgs_sound (alphabet : List Nat) (budget : Nat) (args : List Term)
      (member : args ∈ boundedArgs alphabet budget) :
      ArgsOver alphabet args ∧ argsSize args ≤ budget := by
    cases budget with
    | zero =>
        have empty : args = [] := List.mem_singleton.mp (by simpa only [boundedArgs] using member)
        subst args
        exact ⟨trivial, Nat.le_refl _⟩
    | succ budget =>
        rw [boundedArgs] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨trivial, Nat.zero_le _⟩
        · obtain ⟨index, _, member⟩ := List.mem_flatMap.mp member
          obtain ⟨head, headPresent, member⟩ := List.mem_flatMap.mp member
          obtain ⟨tail, tailPresent, rfl⟩ := List.mem_map.mp member
          have first := boundedTerms_sound alphabet (index.val + 1) head headPresent
          have rest := boundedArgs_sound alphabet (budget - index.val) tail tailPresent
          exact ⟨⟨first.1, rest.1⟩, by simp only [argsSize]; have := index.isLt; omega⟩
  termination_by 2 * budget + 1
  decreasing_by all_goals omega
end

mutual
  theorem boundedTerms_complete (alphabet : List Nat) (budget : Nat) (term : Term)
      (over : Over alphabet term) (small : term.size ≤ budget) :
      term ∈ boundedTerms alphabet budget := by
    cases budget with
    | zero => have := term.size_pos; omega
    | succ budget =>
        rw [boundedTerms]
        cases term with
        | var _ => exact False.elim over
        | app name args =>
            apply List.mem_flatMap.mpr
            exact ⟨name, over.1, List.mem_map.mpr ⟨args,
              boundedArgs_complete alphabet budget args over.2
                (by simp only [Term.size] at small; omega), rfl⟩⟩
  termination_by 2 * budget
  decreasing_by omega

  theorem boundedArgs_complete (alphabet : List Nat) (budget : Nat) (args : List Term)
      (over : ArgsOver alphabet args) (small : argsSize args ≤ budget) :
      args ∈ boundedArgs alphabet budget := by
    cases budget with
    | zero =>
        cases args with
        | nil => simp [boundedArgs]
        | cons head tail =>
            have := head.size_pos
            simp only [argsSize] at small
            omega
    | succ budget =>
        rw [boundedArgs]
        cases args with
        | nil => exact List.mem_cons_self
        | cons head tail =>
            have positive := head.size_pos
            have sizes : head.size + argsSize tail ≤ budget + 1 := small
            let index : Fin (budget + 1) := ⟨head.size - 1, by omega⟩
            apply List.mem_cons_of_mem
            apply List.mem_flatMap.mpr
            refine ⟨index, by simp, List.mem_flatMap.mpr ?_⟩
            refine ⟨head, boundedTerms_complete alphabet (index.val + 1) head over.1 ?_,
              List.mem_map.mpr ?_⟩
            · dsimp [index]
              omega
            · refine ⟨tail, boundedArgs_complete alphabet (budget - index.val) tail over.2 ?_, rfl⟩
              dsimp [index]
              omega
  termination_by 2 * budget + 1
  decreasing_by all_goals omega
end

theorem boundedTerms_exact (alphabet : List Nat) (budget : Nat) (term : Term) :
    term ∈ boundedTerms alphabet budget ↔ Over alphabet term ∧ term.size ≤ budget :=
  ⟨boundedTerms_sound alphabet budget term,
    fun found => boundedTerms_complete alphabet budget term found.1 found.2⟩

def sizeBound (rules : List Rule) (source : Term) : Nat :=
  max source.size (targetSize rules)

def instanceUniverse (rules : List Rule) (source : Term) : List Term :=
  distinct (boundedTerms (distinct (alphabet rules source)) (sizeBound rules source))

mutual
  theorem over_distinct (alphabet : List Nat) (term : Term) :
      Over (distinct alphabet) term ↔ Over alphabet term := by
    cases term with
    | var _ => rfl
    | app name args => simp only [Over, mem_distinct, argsOver_distinct]
  theorem argsOver_distinct (alphabet : List Nat) (args : List Term) :
      ArgsOver (distinct alphabet) args ↔ ArgsOver alphabet args := by
    cases args with
    | nil => rfl
    | cons head tail => simp only [ArgsOver, over_distinct, argsOver_distinct]
end

theorem universe_exact (rules : List Rule) (source target : Term) :
    target ∈ instanceUniverse rules source ↔
      Over (alphabet rules source) target ∧ target.size ≤ sizeBound rules source := by
  simp only [instanceUniverse, mem_distinct, boundedTerms_exact, over_distinct]

theorem universe_nodup (rules : List Rule) (source : Term) : (instanceUniverse rules source).Nodup :=
  distinct_nodup _

/-- Every finite cast path stays in a list computed from its source/declarations. -/
theorem path_mem_universe (rules : List Rule) (valid : Valid rules) {source target : Term}
    (ground : Ground source) (path : Path rules source target) : target ∈ instanceUniverse rules source :=
  (universe_exact rules source target).mpr
    ⟨path_over rules valid ground path, path_size rules valid path⟩

/-- Finiteness is derived; callers do not supply a finite instance graph. -/
theorem reachable_types_finite (rules : List Rule) (valid : Valid rules)
    (source : Term) (ground : Ground source) :
    ∃ candidates : List Term, ∀ target, Path rules source target → target ∈ candidates :=
  ⟨instanceUniverse rules source, fun _ path => path_mem_universe rules valid ground path⟩

end Yulang.ParametricCasts
