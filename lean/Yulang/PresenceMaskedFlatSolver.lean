import Yulang.PresenceMaskedBounds
import Yulang.PresenceFlatSolver

/-!
# Total flat solving with every outer mask retained

The fixed-bound grammar and the finite shared-parameter scheme are exactly
those of `PresenceFlatSolver`. Each slot now denotes a family of predicates
indexed by the outer hidden-label list. A model satisfies the independently
interpreted constraints at every mask. Free parameter families are unrestricted.

The complete solver uses the concrete `checkMaskedLe` algorithm. Its finite
scan quantifies only fixed-bound label profiles; neither parameter predicates
nor their behavior at different masks are enumerated. Successful schemes have
no residual conditions and recover every independent family solution.

This remains a flat predicate-family result. It does not assert that every
family is the masking interpretation of a regular value type, and it does not
construct recursive payloads, open tails, function types or effect rows.
-/

namespace Yulang.PresenceMaskedFlatSolver

open PresenceFiniteBounds (Bound denote checkLe)
open PresenceMaskedBounds (mask checkMaskedLe)
open PresenceDataTypes (Ty Le)
open SourceDataRuntime (Value)

variable {n : Nat}

abbrev Problem (n : Nat) := PresenceFlatSolver.Problem n
abbrev Scheme (n : Nat) := PresenceFlatSolver.Scheme n
abbrev Result (n : Nat) := PresenceFlatSolver.Result n
abbrev Family (n : Nat) := Fin n → List Nat → Ty

def Models (problem : Problem n) (value : Family n) : Prop :=
  ∀ hidden : List Nat,
    PresenceBoundCoalescing.Models (fun bound => denote (mask hidden bound)) problem
      (fun index => value index hidden)

def lower (problem : Problem n) (index : Fin n) (hidden : List Nat) : Ty :=
  PresenceBoundCoalescing.lower (fun bound => denote (mask hidden bound)) problem index

/-- The same finite output expression is interpreted under each mask. Only
fixed-bound interpretations and parameter-family projections depend on it. -/
def instantiate (scheme : Scheme n) (parameters : Family n) (target : Fin n) (hidden : List Nat) : Ty :=
  fun value =>
    (∃ bound ∈ scheme.lower target, denote (mask hidden bound) value) ∨
      ∃ part ∈ scheme.parts target,
        parameters part.1 hidden value ∧ ∀ bound ∈ part.2, denote (mask hidden bound) value

abbrev coalesce (problem : Problem n) : Scheme n := PresenceFlatSolver.coalesce problem

theorem coalesce_exact (problem : Problem n) (parameters : Family n)
    (target : Fin n) (hidden : List Nat) (value : Value) :
    instantiate (coalesce problem) parameters target hidden value ↔
      PresenceBoundCoalescing.expand (fun bound => denote (mask hidden bound)) problem
        (fun index => parameters index hidden) target value := by
  unfold instantiate coalesce PresenceFlatSolver.coalesce PresenceBoundCoalescing.expand
    PresenceBoundCoalescing.lower PresenceBoundCoalescing.upper
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨part, member, valid, upper⟩
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    exact ⟨source, (LayerBoundTemplates.mem_ancestors problem source target).mp present, valid, upper⟩
  · rintro ⟨source, path, valid, upper⟩
    exact ⟨_, List.mem_map.mpr ⟨source,
      (LayerBoundTemplates.mem_ancestors problem source target).mpr path, rfl⟩, valid, upper⟩

theorem coalesce_at_eq (problem : Problem n) (parameters : Family n) (hidden : List Nat) :
    (fun index => instantiate (coalesce problem) parameters index hidden) =
      PresenceBoundCoalescing.expand (fun bound => denote (mask hidden bound)) problem
        (fun index => parameters index hidden) := by
  funext target value
  exact propext (coalesce_exact problem parameters target hidden value)

def consistent (problem : Problem n) : Bool :=
  PresenceBoundCoalescing.consistent checkMaskedLe problem

/-- The single executable consistency scan is equivalent to checking all
hidden-label lists, not just the empty mask. -/
theorem consistent_all_masks (problem : Problem n) :
    consistent problem = true ↔
      ∀ hidden : List Nat,
        PresenceBoundCoalescing.consistent
          (fun left right => checkLe (mask hidden left) (mask hidden right)) problem = true := by
  simp only [consistent, PresenceBoundCoalescing.consistent, List.all_eq_true]
  constructor
  · intro checked hidden constraint member
    cases constraint with
    | lower | flow => rfl
    | upper source bound =>
        apply List.all_eq_true.mpr
        intro lowerBound lowerMember
        apply (PresenceFiniteBounds.checkLe_exact _ _).mpr
        exact (PresenceMaskedBounds.checkMaskedLe_exact lowerBound bound).mp
          (List.all_eq_true.mp (checked _ member) lowerBound lowerMember) hidden
    | check source target =>
        apply (PresenceFiniteBounds.checkLe_exact _ _).mpr
        exact (PresenceMaskedBounds.checkMaskedLe_exact source target).mp (checked _ member) hidden
  · intro checked constraint member
    cases constraint with
    | lower | flow => rfl
    | upper source bound =>
        apply List.all_eq_true.mpr
        intro lowerBound lowerMember
        apply (PresenceMaskedBounds.checkMaskedLe_exact _ _).mpr
        intro hidden
        exact (PresenceFiniteBounds.checkLe_exact _ _).mp
          (List.all_eq_true.mp (checked hidden _ member) lowerBound lowerMember)
    | check source target =>
        apply (PresenceMaskedBounds.checkMaskedLe_exact _ _).mpr
        intro hidden
        exact (PresenceFiniteBounds.checkLe_exact _ _).mp (checked hidden _ member)

theorem consistent_lower (problem : Problem n) :
    consistent problem = true ↔ Models problem (lower problem) := by
  rw [consistent_all_masks]
  constructor
  · intro checked hidden
    exact (PresenceBoundCoalescing.consistent_exact
      (fun left right => checkLe (mask hidden left) (mask hidden right))
      (fun bound => denote (mask hidden bound))
      (fun left right => PresenceFiniteBounds.checkLe_exact _ _) problem).mp (checked hidden)
  · intro model hidden
    exact (PresenceBoundCoalescing.consistent_exact
      (fun left right => checkLe (mask hidden left) (mask hidden right))
      (fun bound => denote (mask hidden bound))
      (fun left right => PresenceFiniteBounds.checkLe_exact _ _) problem).mpr (model hidden)

/-- A uniform lower family witnesses existence whenever the check succeeds.
No selection of infinitely many separately supplied solutions is assumed. -/
theorem consistent_exact (problem : Problem n) :
    consistent problem = true ↔ ∃ value : Family n, Models problem value := by
  rw [consistent_lower]
  constructor
  · intro model
    exact ⟨lower problem, model⟩
  · rintro ⟨value, model⟩ hidden
    exact PresenceBoundCoalescing.lower_models_of_models (model hidden)

theorem coalesce_satisfies (problem : Problem n) (checked : consistent problem = true)
    (parameters : Family n) : Models problem (instantiate (coalesce problem) parameters) := by
  intro hidden
  rw [coalesce_at_eq]
  exact PresenceBoundCoalescing.expand_satisfies ((consistent_lower problem).mp checked hidden) _

/-- Every original slot is recovered at every mask and every runtime value,
including solutions whose masks have arbitrary dependencies on each other. -/
theorem coalesce_retraction (problem : Problem n) (value : Family n) (model : Models problem value) :
    instantiate (coalesce problem) value = value := by
  funext index hidden item
  exact propext ((coalesce_exact problem value index hidden item).trans
    (PresenceBoundCoalescing.expand_retraction (model hidden) index item))

def solve (problem : Problem n) : Result n :=
  if consistent problem then .solved (coalesce problem) else .rejected

theorem solve_solved_iff (problem : Problem n) (scheme : Scheme n) :
    solve problem = .solved scheme ↔ consistent problem = true ∧ scheme = coalesce problem := by
  cases checked : consistent problem <;> simp [solve, checked, eq_comm]

theorem solve_rejected_iff (problem : Problem n) :
    solve problem = .rejected ↔ ¬ ∃ value : Family n, Models problem value := by
  have exact := consistent_exact problem
  cases checked : consistent problem <;> simp_all [solve]

theorem solved_satisfies (problem : Problem n) (scheme : Scheme n)
    (returned : solve problem = .solved scheme) (parameters : Family n) :
    Models problem (instantiate scheme parameters) := by
  obtain ⟨checked, rfl⟩ := (solve_solved_iff problem scheme).mp returned
  exact coalesce_satisfies problem checked parameters

theorem solved_retraction (problem : Problem n) (scheme : Scheme n)
    (returned : solve problem = .solved scheme) (value : Family n) (model : Models problem value) :
    instantiate scheme value = value := by
  obtain ⟨_, rfl⟩ := (solve_solved_iff problem scheme).mp returned
  exact coalesce_retraction problem value model

/-- Complete solution-space equality for arbitrary all-mask assignments;
no oracle, support test, successful solve or fuel is a theorem premise. -/
theorem solve_models_exact (problem : Problem n) (value : Family n) :
    Models problem value ↔
      ∃ scheme, solve problem = .solved scheme ∧
        ∃ parameters : Family n, instantiate scheme parameters = value := by
  constructor
  · intro model
    have checked := (consistent_exact problem).mpr ⟨value, model⟩
    exact ⟨coalesce problem, by simp [solve, checked], value, coalesce_retraction problem value model⟩
  · rintro ⟨scheme, returned, parameters, rfl⟩
    exact solved_satisfies problem scheme returned parameters

theorem solve_complete (problem : Problem n) :
    match solve problem with
    | .rejected => ¬ ∃ value : Family n, Models problem value
    | .solved scheme =>
        (∀ parameters : Family n, Models problem (instantiate scheme parameters)) ∧
        (∀ value : Family n, Models problem value → instantiate scheme value = value) := by
  cases returned : solve problem with
  | rejected => exact (solve_rejected_iff problem).mp returned
  | solved scheme =>
      exact ⟨solved_satisfies problem scheme returned, solved_retraction problem scheme returned⟩

theorem solve_instances_exact (problem : Problem n) (output : Fin n) (target : List Nat → Ty) :
    (∃ value : Family n, Models problem value ∧ ∀ hidden, Le (value output hidden) (target hidden)) ↔
      ∃ scheme, solve problem = .solved scheme ∧ ∃ parameters : Family n,
        ∀ hidden, Le (instantiate scheme parameters output hidden) (target hidden) := by
  constructor
  · rintro ⟨value, model, below⟩
    obtain ⟨scheme, returned, parameters, same⟩ := (solve_models_exact problem value).mp model
    exact ⟨scheme, returned, parameters, same ▸ below⟩
  · rintro ⟨scheme, returned, parameters, below⟩
    exact ⟨instantiate scheme parameters, solved_satisfies problem scheme returned parameters, below⟩

namespace Examples

def shadowConflict : Problem 0 := [.check PresenceMaskedBounds.Examples.contradiction .bottom]

theorem shadow_conflict_unmasked_solved :
    PresenceFlatSolver.solve shadowConflict = .solved (PresenceFlatSolver.coalesce shadowConflict) := by
  have checked : PresenceFlatSolver.consistent shadowConflict = true := by decide +kernel
  simp [PresenceFlatSolver.solve, checked]

theorem shadow_conflict_rejected : solve shadowConflict = .rejected := by
  have checked : consistent shadowConflict = false := by decide +kernel
  simp [solve, checked]

end Examples

end Yulang.PresenceMaskedFlatSolver
