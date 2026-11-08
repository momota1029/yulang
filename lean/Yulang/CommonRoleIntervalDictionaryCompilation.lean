import Yulang.CommonRoleIntervalDictionaries
import Yulang.CommonRoleIntervalGeneration

/-!
# Compiling every interval-dictionary obligation into the shared graph

The finite expansion component's original endpoint syntax is lowered to
existing presence terms. A caller-supplied *name map* identifies its existing
source slots; the map is not a semantic solver or a choice of interval centre.
Repeated names retain exactly the same original type/row slot.

The actual common graph compiler preserves all previous ordinary constraints
and every dictionary node's endpoint checks, with literal original readback.
The graph's subtype edges are still obligations; no parameter-side residual
predicate is used to claim that those edges have been solved.
-/

namespace Yulang.CommonRoleIntervalDictionaryCompilation

open CommonRoleCaptureNormalization (Form)
open CommonRoleIntervalExpansion (Tree)
open CommonRoleIntervalExpansionChecks (constraints Consistent)
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)

def lower (name : Nat → α) : Form → TyTerm α
  | .var index => .var (name index)
  | .int => .base .int
  | .pair first last => .pair (lower name first) (lower name last)
  | .join first last => .union (lower name first) (lower name last)
  | .tick payload => .variant 0 (lower name payload)

theorem lower_eval (name : Nat → α) (assignment : α → Comp Common.model) (form : Form) :
    (lower name form).eval Common.model assignment =
      form.eval (fun index => (assignment (name index)).1) := by
  induction form <;> simp_all [lower, Form.eval, TyTerm.eval, Common.model]

def meaning (name : Nat → α) (assignment : α → Comp Common.model) : Form → Common.Ty :=
  Form.eval (fun index => (assignment (name index)).1)

def lowerCheck (name : Nat → α) (check : LayerBoundTemplates.Constraint 0 Form) : Atom α :=
  CommonRoleIntervalGeneration.atom (check.map (lower name))

theorem lower_check_exact (name : Nat → α) (assignment : α → Comp Common.model)
    (check : LayerBoundTemplates.Constraint 0 Form) :
    (lowerCheck name check).Holds Common.model assignment ↔
      CommonBoundCoalescing.Holds (meaning name assignment) Fin.elim0 check := by
  cases check with
  | check first last =>
      simp only [lowerCheck, LayerBoundTemplates.Constraint.map,
        CommonRoleIntervalGeneration.atom, Atom.Holds, lower_eval]
      rfl
  | lower _ index | upper index _ | flow index _ => exact Fin.elim0 index

def generate (name : Nat → α) (trace : Tree) : List (Atom α) :=
  (constraints (n := 0) trace).map (lowerCheck name)

theorem generate_exact (name : Nat → α) (assignment : α → Comp Common.model) (trace : Tree) :
    All Common.model assignment (generate name trace) ↔ Consistent (meaning name assignment) trace := by
  rw [← CommonRoleIntervalExpansionChecks.constraints_exact (meaning name assignment) trace Fin.elim0]
  simp only [All, generate, List.forall_mem_map, lower_check_exact, CommonBoundCoalescing.Models]

/-- Arbitrary original shared assignments are preserved literally, including
all rows and every original value slot. The existential is the existing graph
compiler's extension, not an impl matching substitution. -/
theorem compile_trace_exact (name : Nat → Fin m) (original : List (Atom (Fin m)))
    (assignment : Fin m → Comp Common.model) (trace : Tree) :
    (All Common.model assignment original ∧ Consistent (meaning name assignment) trace) ↔
      ∃ values : Fin (CommonPresenceConstraintGraph.compile (original ++ generate name trace)).size → Common.Ty,
        (CommonPresenceConstraintGraph.compile (original ++ generate name trace)).Models
          (fun index => (assignment index).2) values ∧
        (CommonPresenceConstraintGraph.compile (original ++ generate name trace)).readback
          (fun index => (assignment index).2) values = assignment := by
  rw [← generate_exact name assignment trace, ← PresenceNormalForm.all_append]
  exact CommonPresenceConstraintGraph.compile_atoms_exact _ assignment

/-- Reflection is for every independent graph realizer, including arbitrary
regular Common types, not only the compiler's canonical extension. -/
theorem compiled_reflects (name : Nat → Fin m) (original : List (Atom (Fin m)))
    (trace : Tree) (rows : Fin m → Common.Row)
    (values : Fin (CommonPresenceConstraintGraph.compile (original ++ generate name trace)).size → Common.Ty)
    (model : (CommonPresenceConstraintGraph.compile (original ++ generate name trace)).Models rows values) :
    let assignment := (CommonPresenceConstraintGraph.compile (original ++ generate name trace)).readback rows values
    All Common.model assignment original ∧ Consistent (meaning name assignment) trace := by
  dsimp only
  rw [← generate_exact, ← PresenceNormalForm.all_append]
  exact CommonPresenceConstraintGraph.compile_atoms_reflects _ rows values model

end Yulang.CommonRoleIntervalDictionaryCompilation
