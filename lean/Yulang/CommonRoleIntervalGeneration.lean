import Yulang.CommonRoleIntervals
import Yulang.CommonPresenceConstraintGraph

/-!
# Returning interval checks to the existing shared constraint machine

Endpoints are existing presence type terms, not a second type language.
The finite output consists of ordinary `tyLe` atoms. Compilation uses the
existing shared-pool collector and preserves the original value/row assignment
at readback. The compiled graph still contains constraints: this is generation
exactness, not a theorem that a subtype solver or role candidate succeeded.
-/

namespace Yulang.CommonRoleIntervalGeneration

open Core.PresenceGeneration (TyTerm Comp)
open CommonRoleIntervals (Interval Fits Valid coalesce evaluate)
open PresenceNormalForm (Atom All)

abbrev Argument (α : Type) := Interval (TyTerm α)

def atom : LayerBoundTemplates.Constraint 0 (TyTerm α) → Atom α
  | .check lower upper => .tyLe lower upper
  | .lower _ index | .upper index _ => nomatch index
  | .flow index _ => nomatch index

def generate (arguments : List (Argument α)) : List (Atom α) :=
  (CommonRoleIntervals.checks (n := 0) arguments).map atom

def eval (assignment : α → Comp Common.model) (term : TyTerm α) : Common.Ty :=
  term.eval Common.model assignment

def meaning (assignment : α → Comp Common.model) (arguments : List (Argument α)) :
    Interval Common.Ty := coalesce (arguments.map (evaluate (eval assignment)))

theorem atom_exact (assignment : α → Comp Common.model)
    (constraint : LayerBoundTemplates.Constraint 0 (TyTerm α)) :
    (atom constraint).Holds Common.model assignment ↔
      CommonBoundCoalescing.Holds (eval assignment) Fin.elim0 constraint := by
  cases constraint with
  | check => rfl
  | lower _ index | upper index _ | flow index _ => exact Fin.elim0 index

theorem generate_exact (assignment : α → Comp Common.model)
    (arguments : List (Argument α)) :
    All Common.model assignment (generate arguments) ↔ Valid (meaning assignment arguments) := by
  unfold meaning
  rw [← CommonRoleIntervals.checks_valid_exact (eval assignment) arguments Fin.elim0]
  simp only [All, generate, List.forall_mem_map, atom_exact,
    CommonBoundCoalescing.Models]

theorem generate_real_argument_exact (assignment : α → Comp Common.model)
    (arguments : List (Argument α)) :
    All Common.model assignment (generate arguments) ↔
      ∃ actual, ∀ argument ∈ arguments, Fits (evaluate (eval assignment) argument) actual := by
  rw [generate_exact, CommonRoleIntervals.valid_iff_nonempty]
  simp only [meaning, CommonRoleIntervals.fits_coalesce, List.forall_mem_map]

theorem generate_length (arguments : List (Argument α)) :
    (generate arguments).length = arguments.length * arguments.length := by
  simp only [generate, List.length_map, CommonRoleIntervals.checks_length]

/-- No existing ordinary/associated constraint is discarded when returning
the checks. Every statement is at the same ambient assignment. -/
theorem append_exact (assignment : α → Comp Common.model) (existing : List (Atom α))
    (arguments : List (Argument α)) :
    All Common.model assignment (existing ++ generate arguments) ↔
      All Common.model assignment existing ∧ Valid (meaning assignment arguments) := by
  rw [PresenceNormalForm.all_append, generate_exact]

/-- Actual finite compilation, including all existing endpoint constructors.
The existential graph assignment is supplied by the already proved compiler;
it is not an impl-head point capture or a stored interval center. -/
theorem compile_exact (arguments : List (Argument (Fin m)))
    (assignment : Fin m → Comp Common.model) :
    Valid (meaning assignment arguments) ↔
      ∃ values : Fin (CommonPresenceConstraintGraph.compile (generate arguments)).size → Common.Ty,
        (CommonPresenceConstraintGraph.compile (generate arguments)).Models
            (fun index => (assignment index).2) values ∧
          (CommonPresenceConstraintGraph.compile (generate arguments)).readback
            (fun index => (assignment index).2) values = assignment := by
  rw [← generate_exact]
  exact CommonPresenceConstraintGraph.compile_atoms_exact (generate arguments) assignment

theorem compile_append_exact (existing : List (Atom (Fin m)))
    (arguments : List (Argument (Fin m))) (assignment : Fin m → Comp Common.model) :
    (All Common.model assignment existing ∧ Valid (meaning assignment arguments)) ↔
      ∃ values : Fin (CommonPresenceConstraintGraph.compile (existing ++ generate arguments)).size → Common.Ty,
        (CommonPresenceConstraintGraph.compile (existing ++ generate arguments)).Models
            (fun index => (assignment index).2) values ∧
          (CommonPresenceConstraintGraph.compile (existing ++ generate arguments)).readback
            (fun index => (assignment index).2) values = assignment := by
  rw [← append_exact]
  exact CommonPresenceConstraintGraph.compile_atoms_exact (existing ++ generate arguments) assignment

/-- Reflection for every independent graph model, including regular
realizers rather than only the collector's canonical interpretation. -/
theorem compiled_reflects (existing : List (Atom (Fin m)))
    (arguments : List (Argument (Fin m))) (rows : Fin m → Common.Row)
    (values : Fin (CommonPresenceConstraintGraph.compile (existing ++ generate arguments)).size → Common.Ty)
    (model : (CommonPresenceConstraintGraph.compile (existing ++ generate arguments)).Models rows values) :
    All Common.model
        ((CommonPresenceConstraintGraph.compile (existing ++ generate arguments)).readback rows values) existing ∧
      Valid (meaning
        ((CommonPresenceConstraintGraph.compile (existing ++ generate arguments)).readback rows values)
        arguments) :=
  (append_exact _ existing arguments).mp
    (CommonPresenceConstraintGraph.compile_atoms_reflects _ rows values model)

end Yulang.CommonRoleIntervalGeneration
