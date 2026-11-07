import Yulang.CommonBoundRefClosedSoundness
import Yulang.CommonBoundRefRows
import Yulang.CommonClampedRowFamily

/-!
# Solving every row condition emitted by the actual bound-reference worklist

Row constraints are recovered from finite syntax, together with the original
independent rows. The conversion can reject unsupported row syntax; generated
clauses prove that it succeeds. There is no test of a type assignment or model.
Every other auxiliary check returned by the worklist is the literal true, so
solving these rows discharges all auxiliary checks at every value assignment.
-/

namespace Yulang.CommonBoundRefSolvedRows

open PresenceOpenTailGenerationLowering (Pool)
open Core.PresenceGeneration (RowTerm)
open Common (Row Ty)
open PresenceSourceConstraintSupport (simpleRow originalRow)
open CommonPresenceConstraintGraph (rowEval)

variable {m : Nat}

abbrev RowPair (m : Nat) := RowTerm (Fin m) × RowTerm (Fin m)

def declareUpper : RowTerm (Fin m) → Option (CommonRowTailInference.Upper m)
  | .var index => some (.var index)
  | .empty => some .empty
  | .join _ _ => none

def declareRows : List (RowPair m) → Option (List (CommonRowTailInference.RowConstraint m))
  | [] => some []
  | (lower, upper) :: rest => do
      let last ← declareUpper upper
      let tail ← declareRows rest
      pure (⟨originalRow lower, last⟩ :: tail)

def Supported (pairs : List (RowPair m)) : Prop :=
  ∀ pair ∈ pairs, simpleRow pair.2 = true

theorem declareUpper_exact (row : RowTerm (Fin m)) (upper : CommonRowTailInference.Upper m)
    (returned : declareUpper row = some upper) : upper.term = originalRow row := by
  cases row <;> simp only [declareUpper] at returned
  · cases returned; rfl
  · cases returned; rfl
  · cases returned

theorem declareUpper_complete (row : RowTerm (Fin m)) (good : simpleRow row = true) :
    ∃ upper, declareUpper row = some upper := by
  cases row with
  | var index => exact ⟨.var index, rfl⟩
  | empty => exact ⟨.empty, rfl⟩
  | join => cases good

theorem declareRows_complete (pairs : List (RowPair m)) (good : Supported pairs) :
    ∃ constraints, declareRows pairs = some constraints := by
  induction pairs with
  | nil => exact ⟨[], rfl⟩
  | cons pair rest ih =>
      obtain ⟨upper, found⟩ := declareUpper_complete pair.2 (good pair List.mem_cons_self)
      obtain ⟨tail, declared⟩ := ih (fun item member => good item (List.mem_cons_of_mem _ member))
      exact ⟨⟨originalRow pair.1, upper⟩ :: tail, by simp [declareRows, found, declared]⟩

theorem declareRows_exact (pairs : List (RowPair m))
    (constraints : List (CommonRowTailInference.RowConstraint m))
    (returned : declareRows pairs = some constraints) (rows : Fin m → Row) :
    CommonRowTailInference.RowsHold constraints rows ↔
      CommonPresenceConstraintGraph.RowsHold pairs rows := by
  induction pairs generalizing constraints with
  | nil =>
      simp only [declareRows, Option.some.injEq] at returned
      subst constraints
      simp [CommonRowTailInference.RowsHold, CommonPresenceConstraintGraph.RowsHold]
  | cons pair rest ih =>
      cases found : declareUpper pair.2 with
      | none => simp [declareRows, found] at returned
      | some upper =>
          cases declared : declareRows rest with
          | none => simp [declareRows, found, declared] at returned
          | some tail =>
              simp [declareRows, found, declared] at returned
              subst constraints
              simp only [CommonRowTailInference.RowsHold, CommonPresenceConstraintGraph.RowsHold,
                List.mem_cons, forall_eq_or_imp]
              rw [declareUpper_exact pair.2 upper found]
              exact and_congr Iff.rfl (ih tail declared)

def auxiliaryRows {pool : Pool m} : List (CommonBoundRefWorklist.Aux pool) → List (RowPair m)
  | [] => []
  | .rowBelow first last :: rest => (first, last) :: auxiliaryRows rest
  | _ :: rest => auxiliaryRows rest

theorem auxiliaryRows_member {pool : Pool m} (checks : List (CommonBoundRefWorklist.Aux pool))
    (first last : RowTerm (Fin m)) :
    (first, last) ∈ auxiliaryRows checks ↔ .rowBelow first last ∈ checks := by
  induction checks with
  | nil => simp [auxiliaryRows]
  | cons check rest ih =>
      cases check <;> simp [auxiliaryRows, ih, Prod.mk.injEq]

theorem auxiliaryRows_exact {pool : Pool m} (checks : List (CommonBoundRefWorklist.Aux pool))
    (good : ∀ check ∈ checks, CommonBoundRefWorklist.RowOrTrue check)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    CommonPresenceConstraintGraph.RowsHold (auxiliaryRows checks) rows ↔
      ∀ check ∈ checks, CommonBoundRefBranches.auxHolds pool rows values check := by
  constructor
  · intro rowModel check member
    have shape := good check member
    cases check with
    | rowBelow first last =>
        exact rowModel (first, last) ((auxiliaryRows_member checks first last).mpr member)
    | flag expression =>
        cases expression with
        | literal value =>
            change value = true at shape
            subst value
            trivial
        | _ => cases shape
    | _ => cases shape
  · intro auxiliary pair member
    exact auxiliary (.rowBelow pair.1 pair.2)
      ((auxiliaryRows_member checks pair.1 pair.2).mp member)

theorem run_rows_supported (pool : Pool m) (good : CommonGeneratedPoolRows.AllSimpleRows pool)
    (edges : List (CommonBoundRefWorklist.Edge pool)) (state : CommonBoundRefWorklist.State pool)
    (returned : state ∈ CommonBoundRefWorklist.run pool edges) : Supported (auxiliaryRows state.aux) := by
  intro pair member
  have emitted := (auxiliaryRows_member state.aux pair.1 pair.2).mp member
  obtain ⟨edge, branch, inspected, included⟩ :=
    CommonBoundRefWorklist.run_aux_origin pool edges state returned _ emitted
  obtain ⟨original, inspected, included⟩ :=
    CommonBoundRefWorklist.inspect_aux_origin pool edge branch inspected _ included
  exact (CommonBoundRefRows.inspect_rows pool good edge.1.val edge.2.val original inspected
    (.rowBelow pair.1 pair.2) included).2

theorem original_rows_supported (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (good : PresenceSourceConstraintSupport.GoodAtoms atoms) :
    Supported (CommonPresenceConstraintGraph.splitAtoms atoms).rows := by
  induction atoms with
  | nil => simp [Supported, CommonPresenceConstraintGraph.splitAtoms]
  | cons atom rest ih =>
      have tail := ih (fun item member => good item (List.mem_cons_of_mem _ member))
      cases atom with
      | tyLe => exact tail
      | rowLe first last =>
          intro pair member
          rcases List.mem_cons.mp member with rfl | member
          · exact good _ List.mem_cons_self
          · exact tail pair member

theorem supported_append (first last : List (RowPair m))
    (before : Supported first) (after : Supported last) : Supported (first ++ last) := by
  intro pair member
  exact (List.mem_append.mp member).elim (before pair) (after pair)

theorem rowsHold_append (first last : List (RowPair m)) (rows : Fin m → Row) :
    CommonPresenceConstraintGraph.RowsHold (first ++ last) rows ↔
      CommonPresenceConstraintGraph.RowsHold first rows ∧
        CommonPresenceConstraintGraph.RowsHold last rows := by
  constructor
  · intro valid
    exact ⟨fun pair member => valid pair (List.mem_append_left _ member),
      fun pair member => valid pair (List.mem_append_right _ member)⟩
  · rintro ⟨before, after⟩ pair member
    exact (List.mem_append.mp member).elim (before pair) (after pair)

end Yulang.CommonBoundRefSolvedRows
