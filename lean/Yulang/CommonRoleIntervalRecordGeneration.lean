import Yulang.CommonRoleIntervalRecordResidual

/-!
# Returning a determined interval record residual to the ordinary graph

The input spine is already determined. First-field-wins and the explicit
labels compute its unique residual. Both symbolic endpoints are retained and
reconciled with the requested interval by ordinary generated comparisons.
The existential in the graph theorem is the compiler's assignment, not a
search over substitutions for a role head. Open-record deferral, arbitrary
head inspection and the final role resolver remain separate obligations.
-/

namespace Yulang.CommonRoleIntervalRecordGeneration

open Core.PresenceGeneration (TyTerm Comp)
open CommonRoleCanonicalRows (Row capture)
open CommonRoleIntervalRecordResidual (Fields lowerFields upperFields)
open CommonRoleIntervals (Interval Fits Valid evaluate merge)
open CommonRoleIntervalGeneration (Argument)
open PresenceNormalForm (Atom All)

def recordTerm : Row (TyTerm α) → TyTerm α
  | [] => .emptyRecord
  | (label, payload) :: rest => .record label payload (recordTerm rest)

def bounds (labels : List Nat) (fields : Fields α) : Argument α :=
  (recordTerm (lowerFields (capture labels fields)),
    recordTerm (upperFields (capture labels fields)))

def evaluated (assignment : α → Comp Common.model) (argument : Argument α) :
    Interval Common.Ty := evaluate (CommonRoleIntervalGeneration.eval assignment) argument

def Compatible (assignment : α → Comp Common.model) (labels : List Nat)
    (fields : Fields α) (requested : Argument α) : Prop :=
  Valid (evaluated assignment (bounds labels fields)) ∧
    Valid (evaluated assignment requested) ∧
    Common.Subtype (evaluated assignment (bounds labels fields)).1
      (evaluated assignment requested).2 ∧
    Common.Subtype (evaluated assignment requested).1
      (evaluated assignment (bounds labels fields)).2

def generate (labels : List Nat) (fields : Fields α) (requested : Argument α) :
    List (Atom α) :=
  CommonRoleIntervalGeneration.generate [bounds labels fields, requested]

/-- Mathematical interval membership, not an operational choice of centre.
The residual in this statement has already been computed by subtraction. -/
theorem generated_fit_exact (assignment : α → Comp Common.model)
    (labels : List Nat) (fields : Fields α) (requested : Argument α) :
    All Common.model assignment (generate labels fields requested) ↔
      ∃ actual, Fits (evaluated assignment (bounds labels fields)) actual ∧
        Fits (evaluated assignment requested) actual := by
  unfold generate
  rw [CommonRoleIntervalGeneration.generate_real_argument_exact]
  simp [evaluated]

/-- Self consistency and BOTH cross inequalities are returned to the
constraint machine. Nothing is inferred by choosing a masked tail image. -/
theorem generate_exact (assignment : α → Comp Common.model)
    (labels : List Nat) (fields : Fields α) (requested : Argument α) :
    All Common.model assignment (generate labels fields requested) ↔
      Compatible assignment labels fields requested := by
  rw [generated_fit_exact]
  exact (exists_congr fun actual =>
    (CommonRoleIntervals.fits_merge _ _ actual).symm).trans
      ((CommonRoleIntervals.valid_iff_nonempty _).symm.trans
        (CommonRoleIntervals.valid_merge_exact _ _))

/-- Original type and row slots have literal readback, for every ambient
assignment and every existing constraint list, including arbitrary endpoints. -/
theorem compile_exact (existing : List (Atom (Fin m))) (labels : List Nat)
    (fields : Fields (Fin m)) (requested : Argument (Fin m))
    (assignment : Fin m → Comp Common.model) :
    (All Common.model assignment existing ∧ Compatible assignment labels fields requested) ↔
      ∃ values : Fin (CommonPresenceConstraintGraph.compile
          (existing ++ generate labels fields requested)).size → Common.Ty,
        (CommonPresenceConstraintGraph.compile
          (existing ++ generate labels fields requested)).Models
            (fun index => (assignment index).2) values ∧
        (CommonPresenceConstraintGraph.compile
          (existing ++ generate labels fields requested)).readback
            (fun index => (assignment index).2) values = assignment := by
  rw [← generate_exact, ← PresenceNormalForm.all_append]
  exact CommonPresenceConstraintGraph.compile_atoms_exact _ assignment

end Yulang.CommonRoleIntervalRecordGeneration
