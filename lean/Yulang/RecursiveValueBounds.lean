import Yulang.ValueBoundSolvers
import Yulang.SolvedRecursiveTypes

/-!
# Solving unknown value bounds over original recursive effect rows

Ground value bounds name rows from an original recursive-row problem. The
adapter resolves precisely those row occurrences, then runs the executable
unknown-value solver. Every semantic statement refers to the original
`RecursiveRows.Derives` rows. The solver does not receive a value assignment.

Unsupported row summarization, inconsistent value bounds, and a solved value
assignment are distinct results. A supported negative result excludes every
finite structural assignment over arbitrary set rows, not only the encoded
ones. The recursive rows themselves are interpreted at their fixed least
solution; this is not a joint search over arbitrary row and value assignments.
-/

namespace Yulang.RecursiveValueBounds

open StructuralBase ValueBounds

variable {m n : Nat} {Key Slot : Type}

abbrev ResolvedProblem (m n : Nat) (Key : Type) [DecidableEq Key] :=
  ValueBounds.Problem m (SemilinearRowQuotient.Row n Key)

abbrev ResolvedValue (m n : Nat) (Key : Type) [DecidableEq Key] :=
  ValueBounds.Valuation m (SemilinearRowQuotient.Row n Key)

def semanticProblem (rows : RecursiveRows.Problem n Key Slot)
    (problem : ValueBounds.Problem m Slot) :
    ValueBounds.Problem m (RecursiveRows.SetRow n Key) :=
  mapTypes (SolvedRecursiveTypes.meaning rows) problem

def resolveConstraint [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) :
    Constraint m Slot → Option (Constraint m (SemilinearRowQuotient.Row n Key))
  | .lower type target => (SolvedRecursiveTypes.resolve rows type).map (fun type => .lower type target)
  | .flow source target => some (.flow source target)
  | .upper source type => (SolvedRecursiveTypes.resolve rows type).map (fun type => .upper source type)
  | .check source target =>
      (SolvedRecursiveTypes.resolve rows source).bind fun source' =>
      (SolvedRecursiveTypes.resolve rows target).bind fun target' =>
      some (.check source' target')

def resolveProblem [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) :
    ValueBounds.Problem m Slot → Option (ResolvedProblem m n Key)
  | [] => some []
  | constraint :: rest =>
      (resolveConstraint rows constraint).bind fun constraint' =>
      (resolveProblem rows rest).bind fun rest' =>
      some (constraint' :: rest')

theorem resolveConstraint_exact [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) (constraint : Constraint m Slot)
    (resolved : Constraint m (SemilinearRowQuotient.Row n Key))
    (returned : resolveConstraint rows constraint = some resolved) :
    resolved.mapTypes SemilinearRowQuotient.decodeType =
      constraint.mapTypes (SolvedRecursiveTypes.meaning rows) := by
  cases constraint with
  | lower type target =>
      obtain ⟨type', resolvedType, rfl⟩ := Option.map_eq_some_iff.mp returned
      simp only [Constraint.mapTypes, SolvedRecursiveTypes.resolve_exact rows type type' resolvedType]
  | flow source target =>
      cases returned
      rfl
  | upper source type =>
      obtain ⟨type', resolvedType, rfl⟩ := Option.map_eq_some_iff.mp returned
      simp only [Constraint.mapTypes, SolvedRecursiveTypes.resolve_exact rows type type' resolvedType]
  | check source target =>
      simp only [resolveConstraint, Option.bind_eq_some_iff, Option.some.injEq] at returned
      obtain ⟨source', sourceResolved, target', targetResolved, rfl⟩ := returned
      simp only [Constraint.mapTypes,
        SolvedRecursiveTypes.resolve_exact rows source source' sourceResolved,
        SolvedRecursiveTypes.resolve_exact rows target target' targetResolved]

theorem resolveProblem_exact [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) (problem : ValueBounds.Problem m Slot)
    (resolved : ResolvedProblem m n Key)
    (returned : resolveProblem rows problem = some resolved) :
    mapTypes SemilinearRowQuotient.decodeType resolved = semanticProblem rows problem := by
  induction problem generalizing resolved with
  | nil => cases returned; rfl
  | cons constraint rest ih =>
      simp only [resolveProblem, Option.bind_eq_some_iff, Option.some.injEq] at returned
      obtain ⟨constraint', first, rest', later, rfl⟩ := returned
      simp only [mapTypes, semanticProblem, List.map_cons]
      rw [resolveConstraint_exact rows constraint constraint' first]
      exact congrArg (List.cons _) (ih rest' later)

def ConstraintSupported [DecidableEq Key] (rows : RecursiveRows.Problem n Key Slot) :
    Constraint m Slot → Prop
  | .lower type _ | .upper _ type => SolvedRecursiveTypes.Supported rows type
  | .flow _ _ => True
  | .check source target =>
      SolvedRecursiveTypes.Supported rows source ∧ SolvedRecursiveTypes.Supported rows target

def Supported [DecidableEq Key] (rows : RecursiveRows.Problem n Key Slot)
    (problem : ValueBounds.Problem m Slot) : Prop :=
  ∀ constraint ∈ problem, ConstraintSupported rows constraint

theorem resolveConstraint_supported_iff [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) (constraint : Constraint m Slot) :
    (∃ resolved, resolveConstraint rows constraint = some resolved) ↔ ConstraintSupported rows constraint := by
  cases constraint with
  | lower type target =>
      simp only [ConstraintSupported, ← SolvedRecursiveTypes.resolve_supported_iff]
      cases selected : SolvedRecursiveTypes.resolve rows type <;> simp [resolveConstraint, selected]
  | flow source target => simp [resolveConstraint, ConstraintSupported]
  | upper source type =>
      simp only [ConstraintSupported, ← SolvedRecursiveTypes.resolve_supported_iff]
      cases selected : SolvedRecursiveTypes.resolve rows type <;> simp [resolveConstraint, selected]
  | check source target =>
      simp only [ConstraintSupported, ← SolvedRecursiveTypes.resolve_supported_iff]
      cases first : SolvedRecursiveTypes.resolve rows source <;>
        cases second : SolvedRecursiveTypes.resolve rows target <;>
          simp [resolveConstraint, first, second]

theorem resolveProblem_supported_iff [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) (problem : ValueBounds.Problem m Slot) :
    (∃ resolved, resolveProblem rows problem = some resolved) ↔ Supported rows problem := by
  induction problem with
  | nil => simp [resolveProblem, Supported]
  | cons constraint rest ih =>
      constructor
      · rintro ⟨resolved, returned⟩
        simp only [resolveProblem, Option.bind_eq_some_iff, Option.some.injEq] at returned
        obtain ⟨constraint', first, rest', later, rfl⟩ := returned
        intro current member
        rcases List.mem_cons.mp member with rfl | member
        · exact (resolveConstraint_supported_iff rows current).mp ⟨constraint', first⟩
        · exact ih.mp ⟨rest', later⟩ current member
      · intro supported
        obtain ⟨constraint', first⟩ := (resolveConstraint_supported_iff rows constraint).mpr
          (supported constraint (by simp))
        obtain ⟨rest', later⟩ := ih.mpr (fun current member =>
          supported current (List.mem_cons_of_mem constraint member))
        exact ⟨constraint' :: rest', by simp [resolveProblem, first, later]⟩

inductive Result (m n : Nat) (Key : Type) [DecidableEq Key] where
  | unsupported
  | unsatisfiable
  | solved (value : ResolvedValue m n Key)

/-- A compact observable result for diagnostics and executable regressions;
the successful result still retains its actual synthesized assignment. -/
def Result.verdict [DecidableEq Key] : Result m n Key → Option Bool
  | .unsupported => none
  | .unsatisfiable => some false
  | .solved _ => some true

@[simp] theorem Result.verdict_none_iff [DecidableEq Key] (result : Result m n Key) :
    result.verdict = none ↔ result = .unsupported := by
  cases result <;> simp [verdict]

@[simp] theorem Result.verdict_false_iff [DecidableEq Key] (result : Result m n Key) :
    result.verdict = some false ↔ result = .unsatisfiable := by
  cases result <;> simp [verdict]

@[simp] theorem Result.verdict_true_iff [DecidableEq Key] (result : Result m n Key) :
    result.verdict = some true ↔ ∃ value, result = .solved value := by
  cases result <;> simp [verdict]

/-- Both stages are total. Unsupported is a checked capability boundary and
is deliberately not conflated with an inconsistent bound problem. -/
def solve [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) (problem : ValueBounds.Problem m Slot) : Result m n Key :=
  match resolveProblem rows problem with
  | none => .unsupported
  | some resolved =>
      match ValueBounds.solve SemilinearRowQuotient.checkType resolved with
      | none => .unsatisfiable
      | some value => .solved value

theorem solve_solved_iff [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) (problem : ValueBounds.Problem m Slot)
    (value : ResolvedValue m n Key) :
    solve rows problem = .solved value ↔
      ∃ resolved, resolveProblem rows problem = some resolved ∧
        value = least resolved ∧
          Models (RecursiveRows.algebra n Key).le (semanticProblem rows problem)
            (SemilinearRowQuotient.decodeType ∘ value) := by
  constructor
  · intro returned
    cases selected : resolveProblem rows problem with
    | none => simp [solve, selected] at returned
    | some resolved =>
        cases computed : ValueBounds.solve SemilinearRowQuotient.checkType resolved with
        | none => simp [solve, selected, computed] at returned
        | some actual =>
            have same : actual = value := by simpa [solve, selected, computed] using returned
            subst actual
            have exactResult := (ValueBoundSolvers.solve_mapped_some_iff
              SemilinearRowQuotient.decodeType SemilinearRowQuotient.checkType
              (RecursiveRows.algebra n Key).le SemilinearRowQuotient.checkType_exact resolved value).mp computed
            rw [resolveProblem_exact rows problem resolved selected] at exactResult
            exact ⟨resolved, rfl, exactResult⟩
  · rintro ⟨resolved, selected, leastValue, model⟩
    have model' : Models (RecursiveRows.algebra n Key).le
        (mapTypes SemilinearRowQuotient.decodeType resolved)
        (SemilinearRowQuotient.decodeType ∘ value) := by
      exact (resolveProblem_exact rows problem resolved selected).symm ▸ model
    have computed := (ValueBoundSolvers.solve_mapped_some_iff
      SemilinearRowQuotient.decodeType SemilinearRowQuotient.checkType
      (RecursiveRows.algebra n Key).le SemilinearRowQuotient.checkType_exact resolved value).mpr
        ⟨leastValue, model'⟩
    simp [solve, selected, computed]

theorem solve_solved_sound [DecidableEq Key] [DecidableEq Slot]
    {rows : RecursiveRows.Problem n Key Slot} {problem : ValueBounds.Problem m Slot}
    {value : ResolvedValue m n Key} (returned : solve rows problem = .solved value) :
    Models (RecursiveRows.algebra n Key).le (semanticProblem rows problem)
      (SemilinearRowQuotient.decodeType ∘ value) := by
  obtain ⟨_, _, _, model⟩ := (solve_solved_iff rows problem value).mp returned
  exact model

/-- The original least assignment is recovered exactly, before any subtype
comparison. The witness is not supplied by the caller. -/
theorem solve_solved_least_eq [DecidableEq Key] [DecidableEq Slot]
    {rows : RecursiveRows.Problem n Key Slot} {problem : ValueBounds.Problem m Slot}
    {value : ResolvedValue m n Key} (returned : solve rows problem = .solved value) :
    SemilinearRowQuotient.decodeType ∘ value = least (semanticProblem rows problem) := by
  obtain ⟨resolved, selected, rfl, _⟩ := (solve_solved_iff rows problem value).mp returned
  funext target
  rw [Function.comp_apply, least_mapTypes SemilinearRowQuotient.decodeType rfl (fun _ _ => rfl),
    resolveProblem_exact rows problem resolved selected]

/-- The comparison quantifies over arbitrary set-row assignments, whether or
not they have a semilinear representation. -/
theorem solve_solved_least [DecidableEq Key] [DecidableEq Slot]
    {rows : RecursiveRows.Problem n Key Slot} {problem : ValueBounds.Problem m Slot}
    {value : ResolvedValue m n Key} (returned : solve rows problem = .solved value)
    {other : Valuation m (RecursiveRows.SetRow n Key)}
    (model : Models (RecursiveRows.algebra n Key).le (semanticProblem rows problem) other)
    (target : Fin m) :
    Subtype (RecursiveRows.algebra n Key).le (SemilinearRowQuotient.decodeType (value target)) (other target) := by
  change Subtype _ ((SemilinearRowQuotient.decodeType ∘ value) target) _
  rw [solve_solved_least_eq returned]
  exact least_below model.lower target

theorem solve_unsupported_iff [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) (problem : ValueBounds.Problem m Slot) :
    solve rows problem = .unsupported ↔ ¬ Supported rows problem := by
  constructor
  · intro returned supported
    obtain ⟨resolved, selected⟩ := (resolveProblem_supported_iff rows problem).mpr supported
    cases computed : ValueBounds.solve SemilinearRowQuotient.checkType resolved <;>
      simp [solve, selected, computed] at returned
  · intro unsupported
    cases selected : resolveProblem rows problem with
    | none => simp [solve, selected]
    | some resolved =>
        exact False.elim (unsupported ((resolveProblem_supported_iff rows problem).mp ⟨resolved, selected⟩))

/-- A negative consistency result is exact when row summarization succeeds.
Unsupported inputs always remain a third outcome, even if some other bound
would independently be inconsistent. -/
theorem solve_unsatisfiable_iff [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) (problem : ValueBounds.Problem m Slot) :
    solve rows problem = .unsatisfiable ↔
      Supported rows problem ∧
        ¬ ∃ value : Valuation m (RecursiveRows.SetRow n Key),
          Models (RecursiveRows.algebra n Key).le (semanticProblem rows problem) value := by
  constructor
  · intro returned
    cases selected : resolveProblem rows problem with
    | none => simp [solve, selected] at returned
    | some resolved =>
        have failed : ValueBounds.solve SemilinearRowQuotient.checkType resolved = none := by
          cases computed : ValueBounds.solve SemilinearRowQuotient.checkType resolved with
          | none => rfl
          | some value => simp [solve, selected, computed] at returned
        refine ⟨(resolveProblem_supported_iff rows problem).mp ⟨resolved, selected⟩, ?_⟩
        have absent := (ValueBoundSolvers.solve_mapped_none_iff SemilinearRowQuotient.decodeType
          rfl (fun _ _ => rfl) SemilinearRowQuotient.checkType
          (RecursiveRows.algebra n Key).le SemilinearRowQuotient.checkType_exact resolved).mp failed
        rw [resolveProblem_exact rows problem resolved selected] at absent
        exact absent
  · rintro ⟨supported, absent⟩
    obtain ⟨resolved, selected⟩ := (resolveProblem_supported_iff rows problem).mpr supported
    have absent' : ¬ ∃ value : Valuation m (RecursiveRows.SetRow n Key),
        Models (RecursiveRows.algebra n Key).le
          (mapTypes SemilinearRowQuotient.decodeType resolved) value := by
      exact (resolveProblem_exact rows problem resolved selected).symm ▸ absent
    have failed := (ValueBoundSolvers.solve_mapped_none_iff SemilinearRowQuotient.decodeType
      rfl (fun _ _ => rfl) SemilinearRowQuotient.checkType
      (RecursiveRows.algebra n Key).le SemilinearRowQuotient.checkType_exact resolved).mpr absent'
    simp [solve, selected, failed]

theorem solve_exists_iff [DecidableEq Key] [DecidableEq Slot]
    (rows : RecursiveRows.Problem n Key Slot) (problem : ValueBounds.Problem m Slot) :
    (∃ value, solve rows problem = .solved value) ↔
      Supported rows problem ∧
        ∃ value : Valuation m (RecursiveRows.SetRow n Key),
          Models (RecursiveRows.algebra n Key).le (semanticProblem rows problem) value := by
  constructor
  · rintro ⟨value, returned⟩
    obtain ⟨resolved, selected, _, model⟩ := (solve_solved_iff rows problem value).mp returned
    exact ⟨(resolveProblem_supported_iff rows problem).mp ⟨resolved, selected⟩,
      ⟨_, model⟩⟩
  · rintro ⟨supported, model⟩
    cases returned : solve rows problem with
    | unsupported => exact False.elim ((solve_unsupported_iff rows problem).mp returned supported)
    | unsatisfiable => exact False.elim (((solve_unsatisfiable_iff rows problem).mp returned).2 model)
    | solved value => exact ⟨value, rfl⟩


/-! ## Original-AST execution regressions -/

namespace Examples

/-- The least row has the unbounded weights 0, 1, 2, ... . The input is an
original recursive row expression, not a supplied semilinear presentation. -/
def accumulating : RecursiveRows.Problem 1 Nat Nat :=
  [⟨7, .head 0⟩, ⟨7, .protect 0 Directed.allowNone (.var 7)⟩]

def blocked : RecursiveRows.Problem 1 Nat Nat :=
  [⟨7, .head 0⟩, ⟨7, .protect 0 Directed.allowNone (.residual [0] (.var 7))⟩]

def effectful : Ty Nat := .arrow (.base .unit) 9001 (.base .int) 7

def pureOutput : Ty Nat := .arrow (.base .unit) 9001 (.base .int) 9001

/-- Two unknown value types form a cycle; a ground function lower bound must
flow to both of them. The output upper bound then checks the inferred type. -/
def cycle : ValueBounds.Problem 2 Nat :=
  [.lower effectful 0, .flow 0 1, .flow 1 0, .upper 1 effectful]

def pureUpper : ValueBounds.Problem 2 Nat :=
  [.lower effectful 0, .flow 0 1, .flow 1 0, .upper 1 pureOutput]

set_option maxRecDepth 100000 in
theorem original_recursive_rows_and_value_cycle_solve :
    (solve accumulating cycle).verdict = some true := by decide +kernel

set_option maxRecDepth 100000 in
theorem latent_row_mismatch_is_unsatisfiable :
    (solve accumulating pureUpper).verdict = some false := by decide +kernel

set_option maxRecDepth 100000 in
theorem an_active_guard_is_unsupported :
    (solve blocked cycle).verdict = none := by decide +kernel

theorem row_free_bounds_do_not_require_unrelated_summaries :
    (solve blocked ([.lower (.base .int) 0, .upper 0 (.base .int)] :
      ValueBounds.Problem 1 Nat)).verdict = some true := by decide +kernel

theorem actual_solver_constructs_an_original_model :
    ∃ value, solve accumulating cycle = .solved value ∧
      Models (RecursiveRows.algebra 1 Nat).le (semanticProblem accumulating cycle)
        (SemilinearRowQuotient.decodeType ∘ value) := by
  obtain ⟨value, returned⟩ := (Result.verdict_true_iff _).mp
    original_recursive_rows_and_value_cycle_solve
  exact ⟨value, returned, solve_solved_sound returned⟩

theorem rejected_upper_has_no_arbitrary_semantic_value_assignment :
    ¬ ∃ value : Valuation 2 (RecursiveRows.SetRow 1 Nat),
      Models (RecursiveRows.algebra 1 Nat).le (semanticProblem accumulating pureUpper) value :=
  ((solve_unsatisfiable_iff accumulating pureUpper).mp
    ((Result.verdict_false_iff _).mp latent_row_mismatch_is_unsatisfiable)).2

end Examples

end Yulang.RecursiveValueBounds
