import Yulang.Common

/-!
# Finite occurrence heads in common row-flow families

The existing finite flow graph and pure sinks come from `RowFlowSchemes`.
This extension adds a finite list of required signed occurrences. Required
heads flow along the same graph; a required head reaching a pure sink is the
only inconsistency. The original row variables and their correlations remain
shared, and all other row parameters may be arbitrary, including infinite sets.

The scheme stores only finite occurrence lists and the existing finite row
terms. Instantiation joins the required constants with the old free-parameter
family. No model, support, closure, or success proof is stored in a scheme.

This is a reference extension for head constants, not a fast propagation
algorithm. Protection, release, residual subtraction, operation-local universal
quantification, and the Core request generator remain separate obligations.
-/

namespace Yulang.CommonRowHeadFlow

open Common (Occurrence Row)
open RowFlowSchemes (FlatProblem FlatConstraint FlatModels Reaches)

variable {n : Nat}

structure Problem (n : Nat) where
  /-- Directed inclusions and empty upper bounds, with the original slot IDs. -/
  flow : FlatProblem n
  /-- Each pair requires this occurrence in this row, independently of flow. -/
  heads : List (Fin n × Occurrence)

/-- Independent constraints on every original row assignment. -/
def Models (problem : Problem n) (rows : Fin n → Row) : Prop :=
  FlatModels Common.rowAlgebra problem.flow rows ∧
    ∀ head ∈ problem.heads, rows head.1 head.2

/-- Only finite reachability and a finite list of heads are inspected. -/
def check (problem : Problem n) : Bool :=
  problem.heads.all fun head => !RowFlowSchemes.forcedPure problem.flow head.1

theorem check_exact (problem : Problem n) :
    check problem = true ↔
      ∀ head ∈ problem.heads, RowFlowSchemes.forcedPure problem.flow head.1 = false := by
  simp only [check, List.all_eq_true, Bool.not_eq_true']

theorem models_check {problem : Problem n} {rows : Fin n → Row}
    (model : Models problem rows) : check problem = true := by
  apply (check_exact problem).mpr
  intro head member
  cases forced : RowFlowSchemes.forcedPure problem.flow head.1 with
  | false => rfl
  | true =>
      exact False.elim
        ((RowFlowSchemes.forcedPure_le_empty Common.rowAlgebra model.1 head.1 forced)
          head.2 (model.2 head member))

/-- Finite occurrence constants reaching one output slot, preserving the
input order. Duplicate occurrences are harmless set-membership duplicates. -/
def propagated (problem : Problem n) (target : Fin n) : List Occurrence :=
  (problem.heads.filter fun head =>
    decide (target ∈ RowFlowSchemes.reachable problem.flow head.1)).map Prod.snd

theorem mem_propagated (problem : Problem n) (target : Fin n) (occurrence : Occurrence) :
    occurrence ∈ propagated problem target ↔
      ∃ source, (source, occurrence) ∈ problem.heads ∧ Reaches problem.flow source target := by
  simp only [propagated, List.mem_map, List.mem_filter, decide_eq_true_eq,
    RowFlowSchemes.reachable_exact]
  constructor
  · rintro ⟨⟨source, original⟩, ⟨member, path⟩, same⟩
    cases same
    exact ⟨source, member, path⟩
  · rintro ⟨source, member, path⟩
    exact ⟨(source, occurrence), ⟨member, path⟩, rfl⟩

theorem head_propagated (problem : Problem n) (head : Fin n × Occurrence)
    (member : head ∈ problem.heads) : head.2 ∈ propagated problem head.1 :=
  (mem_propagated problem head.1 head.2).mpr ⟨head.1, member, .nil head.1⟩

theorem propagated_flow (problem : Problem n) (source target : Fin n)
    (edge : .flow source target ∈ problem.flow) (occurrence : Occurrence)
    (member : occurrence ∈ propagated problem source) : occurrence ∈ propagated problem target := by
  obtain ⟨start, original, path⟩ := (mem_propagated problem source occurrence).mp member
  exact (mem_propagated problem target occurrence).mpr
    ⟨start, original, path.append
      (.cons ((RowFlowSchemes.mem_successors problem.flow source target).mpr edge) (.nil target))⟩

theorem propagated_pure (problem : Problem n) (checked : check problem = true)
    (target : Fin n) (pure : .pure target ∈ problem.flow) (occurrence : Occurrence) :
    occurrence ∉ propagated problem target := by
  intro member
  obtain ⟨source, original, path⟩ := (mem_propagated problem target occurrence).mp member
  have forced := (RowFlowSchemes.forcedPure_exact problem.flow source).mpr ⟨target, pure, path⟩
  have live := (check_exact problem).mp checked (source, occurrence) original
  rw [forced] at live
  cases live

theorem propagated_below {problem : Problem n} {rows : Fin n → Row}
    (model : Models problem rows) (target : Fin n) :
    Common.rowLe (fun occurrence => occurrence ∈ propagated problem target) (rows target) := by
  intro occurrence member
  obtain ⟨source, original, path⟩ := (mem_propagated problem target occurrence).mp member
  exact RowFlowSchemes.reaches_le Common.rowAlgebra model.1 path occurrence
    (model.2 (source, occurrence) original)

/-- Finite syntax only. In particular parameters do not contain evidence
that their substituted rows satisfy any predicate. -/
structure Scheme (n : Nat) where
  heads : Fin n → List Occurrence
  flow : RowFlowSchemes.Scheme n

def Scheme.instantiate (scheme : Scheme n) (parameters : Fin n → Row) : Fin n → Row :=
  fun target => Common.rowJoin (fun occurrence => occurrence ∈ scheme.heads target)
    (RowFlowSchemes.instantiate Common.rowAlgebra scheme.flow parameters target)

def coalesce (problem : Problem n) : Scheme n :=
  ⟨propagated problem, RowFlowSchemes.coalesce problem.flow⟩

theorem instantiate_coalesce (problem : Problem n) (parameters : Fin n → Row) :
    (coalesce problem).instantiate parameters =
      fun target => Common.rowJoin (fun occurrence => occurrence ∈ propagated problem target)
        (RowFlowSchemes.expand Common.rowAlgebra problem.flow parameters target) := by
  funext target
  simp only [Scheme.instantiate, coalesce, RowFlowSchemes.instantiate_coalesce]

/-- Internal construction lemma. The public solver discharges this finite
check and exposes only membership in its returned family. -/
theorem coalesce_models (problem : Problem n) (checked : check problem = true)
    (parameters : Fin n → Row) : Models problem ((coalesce problem).instantiate parameters) := by
  rw [instantiate_coalesce]
  constructor
  · intro constraint member
    cases constraint with
    | flow source target =>
        intro occurrence present
        exact present.elim
          (fun head => Or.inl (propagated_flow problem source target member occurrence head))
          (fun parameter => Or.inr
            (RowFlowSchemes.expand_flow Common.rowAlgebra problem.flow parameters
              source target member occurrence parameter))
    | pure target =>
        intro occurrence present
        exact present.elim (propagated_pure problem checked target member occurrence)
          (RowFlowSchemes.expand_pure Common.rowAlgebra problem.flow parameters target member occurrence)
  · intro head member
    exact Or.inl (head_propagated problem head member)

/-- The original arbitrary row assignment itself is a parameter assignment.
Retraction is literal function equality, not merely mutual row inclusion. -/
theorem coalesce_retraction (problem : Problem n) (rows : Fin n → Row)
    (model : Models problem rows) : (coalesce problem).instantiate rows = rows := by
  rw [instantiate_coalesce]
  funext target
  apply Common.rowLe_antisymm
  · intro occurrence present
    exact present.elim (propagated_below model target occurrence)
      ((RowFlowSchemes.expand_equivalent Common.rowAlgebra model.1 target).1 occurrence)
  · intro occurrence present
    exact Or.inr ((RowFlowSchemes.expand_equivalent Common.rowAlgebra model.1 target).2 occurrence present)

/-- With no new heads, the old family is preserved at every parameter
assignment, including arbitrary nonempty and infinite rows. -/
theorem no_heads_instantiate (flow : FlatProblem n) (parameters : Fin n → Row) :
    (coalesce ⟨flow, []⟩).instantiate parameters =
      RowFlowSchemes.instantiate Common.rowAlgebra (RowFlowSchemes.coalesce flow) parameters := by
  funext target
  apply Common.rowLe_antisymm
  · intro occurrence present
    exact present.elim (fun impossible => by cases impossible) id
  · intro occurrence present
    exact Or.inr present

end Yulang.CommonRowHeadFlow
