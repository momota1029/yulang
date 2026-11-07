import Yulang.CommonSymbolicRigidInspection
import Yulang.CommonPresenceClauseFamily

/-!
# Actual symbolic inspector rows in the simultaneous common solver

The emitted row constraints keep the same original row identifiers as the
constructor graph. The row part of a symbolic branch is projected exactly,
and every simple-row branch can be passed to the existing simultaneous
row/regular-equation solver. The remaining child/profile/presence checks are
not claimed to follow from this row elimination.
-/

namespace Yulang.CommonSymbolicRowConstraints

open Common (Row Ty)
open CommonSymbolicConstraints (Check Branch Alternatives)
open CommonSymbolicRigidInspection (Node)
open PresenceSourceConstraintSupport (simpleRow originalRow)
open Core.PresenceGeneration (RowTerm)

def CheckRows (property : Rows → Prop) : Check Rows NodeIndex Child → Prop
  | .rowBelow first last => property first ∧ property last
  | _ => True

def AllRows (property : Rows → Prop) (checks : Branch Rows NodeIndex Child) : Prop :=
  ∀ check ∈ checks, CheckRows property check

def NodeRows (property : Rows → Prop) : Node Rows Child → Prop
  | .arrow _ incoming _ outgoing => property incoming ∧ property outgoing
  | _ => True

theorem inspect_preserves_rows (property : Rows → Prop) (source target : Node Rows Child)
    (first : NodeRows property source) (last : NodeRows property target) :
    AllRows (NodeIndex := NodeIndex) property (CommonSymbolicRigidInspection.inspect source target) := by
  cases source <;> cases target <;>
    simp_all [NodeRows, AllRows, CheckRows, CommonSymbolicRigidInspection.inspect]

theorem allRows_append (property : Rows → Prop) (first last : Branch Rows NodeIndex Child) :
    AllRows property (first ++ last) ↔ AllRows property first ∧ AllRows property last := by
  simp only [AllRows, List.mem_append, or_imp, forall_and]

theorem discharge_preserves_rows (property : Rows → Prop) (checks : Branch Rows NodeIndex Child)
    (good : AllRows property checks) (branch : Branch Rows NodeIndex Child)
    (member : branch ∈ CommonSymbolicConstraints.discharge checks) : AllRows property branch := by
  induction checks generalizing branch with
  | nil =>
      have same := List.mem_singleton.mp member
      subst branch
      simp [AllRows]
  | cons check rest ih =>
      have tail : AllRows property rest := fun actual present => good actual (List.mem_cons_of_mem _ present)
      have copied : ∀ branch ∈ (CommonSymbolicConstraints.discharge rest).map (check :: ·),
          AllRows property branch := by
        intro branch included
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp included
        intro actual included
        exact (List.mem_cons.mp included).elim
          (fun same => same ▸ good check List.mem_cons_self) (ih tail original present actual)
      cases check with
      | childBelow | rowBelow | profileBelow => exact copied branch member
      | flag expression =>
          cases expression with
          | literal value =>
              cases value with
              | false => cases member
              | true => exact ih tail branch member
          | atom | and | or | not => exact copied branch member

variable {m slots labels : Nat}

def emittedRows : Branch (RowTerm (Fin m)) NodeIndex Child → RowFlowSchemes.Problem m
  | [] => []
  | .rowBelow first last :: rest => (originalRow first, originalRow last) :: emittedRows rest
  | _ :: rest => emittedRows rest

def withoutRows : Branch (RowTerm (Fin m)) NodeIndex Child → Branch (RowTerm (Fin m)) NodeIndex Child
  | [] => []
  | .rowBelow _ _ :: rest => withoutRows rest
  | check :: rest => check :: withoutRows rest

theorem branch_rows_exact (checks : Branch (RowTerm (Fin m)) NodeIndex Child)
    (rows : Fin m → Row) (nodes : NodeIndex → Ty) (children : Child → Ty) :
    Branch.Holds (CommonPresenceConstraintGraph.rowEval rows) nodes children checks ↔
      RowFlowSchemes.Models Common.rowAlgebra (emittedRows checks) rows ∧
        Branch.Holds (CommonPresenceConstraintGraph.rowEval rows) nodes children (withoutRows checks) := by
  induction checks with
  | nil => simp [emittedRows, withoutRows, RowFlowSchemes.Models]
  | cons check rest ih =>
      cases check <;>
        simp only [emittedRows, withoutRows, CommonSymbolicConstraints.holds_cons,
          RowFlowSchemes.Models, RowFlowSchemes.Constraint.Holds, List.mem_cons,
          forall_eq_or_imp, Check.Holds] at *
      · rw [ih]
        exact and_left_comm
      · rw [ih]
        exact and_assoc.symm
      · rw [ih]
        exact and_left_comm
      · rw [ih]
        exact and_left_comm

def declareRows (checks : Branch (RowTerm (Fin m)) NodeIndex Child)
    (good : AllRows (fun row => simpleRow row = true) checks) :
    List (CommonRowTailInference.RowConstraint m) :=
  match checks with
  | [] => []
  | .rowBelow first last :: rest =>
      ⟨originalRow first, CommonPresenceClauseFamily.declareUpper last (good _ List.mem_cons_self).2⟩ ::
        declareRows rest (fun actual member => good actual (List.mem_cons_of_mem _ member))
  | _ :: rest => declareRows rest (fun actual member => good actual (List.mem_cons_of_mem _ member))

theorem declared_rows_exact (checks : Branch (RowTerm (Fin m)) NodeIndex Child)
    (good : AllRows (fun row => simpleRow row = true) checks) :
    CommonRowTailInference.rowProblem (declareRows checks good) = emittedRows checks := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      cases check <;>
        simp only [declareRows, CommonRowTailInference.rowProblem, emittedRows, List.map_cons,
          CommonRowTailInference.RowConstraint.erase, CommonPresenceClauseFamily.declareUpper_term,
          ← ih (fun actual member => good actual (List.mem_cons_of_mem _ member))]

theorem emitted_rows_supported (checks : Branch (RowTerm (Fin m)) NodeIndex Child)
    (good : AllRows (fun row => simpleRow row = true) checks) :
    RowFlowSchemes.supported (emittedRows checks) = true := by
  rw [← declared_rows_exact checks good]
  exact CommonRowTailInference.declared_rows_supported _

/-- The row part of the actual symbolic branch and the original constructor
equations are solved together, retaining all shared row IDs. -/
def jointProblem (body : Fin slots → CommonRowTailInference.Body slots labels m)
    (extra : List (CommonRowTailInference.RowConstraint m))
    (checks : Branch (RowTerm (Fin m)) NodeIndex Child)
    (good : AllRows (fun row => simpleRow row = true) checks) :
    CommonRowTailInference.Problem slots labels m :=
  ⟨extra ++ declareRows checks good, body⟩

theorem joint_problem_exact (body : Fin slots → CommonRowTailInference.Body slots labels m)
    (extra : List (CommonRowTailInference.RowConstraint m))
    (checks : Branch (RowTerm (Fin m)) NodeIndex Child)
    (good : AllRows (fun row => simpleRow row = true) checks)
    (rows : Fin m → Row) (values : Fin slots → Ty) :
    CommonRowTailInference.Models (jointProblem body extra checks good) rows values ↔
      CommonRowTailInference.RowsHold extra rows ∧
        RowFlowSchemes.Models Common.rowAlgebra (emittedRows checks) rows ∧
          ∀ index, Common.Equivalent ((body index).eval rows values) (values index) := by
  have split : CommonRowTailInference.RowsHold (extra ++ declareRows checks good) rows ↔
      CommonRowTailInference.RowsHold extra rows ∧
        CommonRowTailInference.RowsHold (declareRows checks good) rows := by
    simp only [CommonRowTailInference.RowsHold, List.mem_append, or_imp, forall_and]
  simp only [CommonRowTailInference.Models, jointProblem, split]
  rw [CommonRowTailInference.rows_hold_iff (declareRows checks good), declared_rows_exact]
  exact and_assoc

def family (body : Fin slots → CommonRowTailInference.Body slots labels m)
    (extra : List (CommonRowTailInference.RowConstraint m))
    (checks : Branch (RowTerm (Fin m)) NodeIndex Child)
    (good : AllRows (fun row => simpleRow row = true) checks) :
    CommonRowTailInference.Scheme slots labels m :=
  CommonRowTailInference.solve (jointProblem body extra checks good)

/-- Every arbitrary pair of parameter assignments satisfies all declared
and inspector-emitted rows and all shared constructor equations. This
conclusion deliberately contains no claim about non-row branch checks. -/
theorem row_definitions_all_parameters
    (body : Fin slots → CommonRowTailInference.Body slots labels m)
    (extra : List (CommonRowTailInference.RowConstraint m))
    (checks : Branch (RowTerm (Fin m)) NodeIndex Child)
    (good : AllRows (fun row => simpleRow row = true) checks)
    (rowParameters : Fin m → Row) (valueParameters : Fin slots → Ty) :
    let scheme := family body extra checks good
    let rows := scheme.instantiateRows rowParameters
    let values := scheme.instantiateValues rowParameters valueParameters
    CommonRowTailInference.RowsHold extra rows ∧
      RowFlowSchemes.Models Common.rowAlgebra (emittedRows checks) rows ∧
        ∀ index, Common.Equivalent ((body index).eval rows values) (values index) :=
  (joint_problem_exact body extra checks good _ _).mp
    (CommonRowTailInference.solve_models _ rowParameters valueParameters)

/-- All independent row/definition models are recovered with exactly the
same rows and demand-equivalent values at every slot. Parameters carry no
residual predicate; child/profile/presence checks remain a separate task. -/
theorem row_definitions_instances_exact
    (body : Fin slots → CommonRowTailInference.Body slots labels m)
    (extra : List (CommonRowTailInference.RowConstraint m))
    (checks : Branch (RowTerm (Fin m)) NodeIndex Child)
    (good : AllRows (fun row => simpleRow row = true) checks)
    (rows : Fin m → Row) (values : Fin slots → Ty) :
    (CommonRowTailInference.RowsHold extra rows ∧
      RowFlowSchemes.Models Common.rowAlgebra (emittedRows checks) rows ∧
        ∀ index, Common.Equivalent ((body index).eval rows values) (values index)) ↔
      ∃ rowParameters : Fin m → Row, ∃ valueParameters : Fin slots → Ty,
        (family body extra checks good).instantiateRows rowParameters = rows ∧
          ∀ index, Common.Equivalent
            ((family body extra checks good).instantiateValues rowParameters valueParameters index)
            (values index) :=
  (joint_problem_exact body extra checks good rows values).symm.trans
    (CommonRowTailInference.joint_instances_exact _ rows values)

end Yulang.CommonSymbolicRowConstraints
