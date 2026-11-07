import Yulang.CommonSymbolicRowConstraints

/-!+# Total declarations of original and inspector-emitted row constraints

Declaration reads only finite syntax. A row comparison accepts an arbitrary
left row term and a variable or empty row on the right, preserving the
original row IDs. Check declaration accepts those comparisons and discards
literal true; every other check returns `none`.

No grammar proof, row assignment, type assignment, or semantic law is an
argument of the computation. Theorems separately establish exactness whenever
declaration succeeds and total success for the generated row/check shapes.
-/

namespace Yulang.CommonRowDeclarations

open Core.PresenceGeneration (RowTerm)
open PresenceSourceConstraintSupport (originalRow simpleRow)
open CommonRowTailInference (RowConstraint RowsHold)
open CommonPresenceConstraintGraph (rowEval)
open CommonSymbolicConstraints (Check Branch)
open CommonSymbolicRowConstraints (CheckRows AllRows)

universe u v w
variable {m : Nat} {Rows : Type u} {Node : Type v} {Child : Type w}

abbrev RowPair (m : Nat) := RowTerm (Fin m) × RowTerm (Fin m)

/-- Only the right row has a shape restriction; joins on the left are kept. -/
def declareRow : RowPair m → Option (RowConstraint m)
  | (source, .var index) => some ⟨originalRow source, .var index⟩
  | (source, .empty) => some ⟨originalRow source, .empty⟩
  | (_, .join _ _) => none

def declareRows : List (RowPair m) → Option (List (RowConstraint m))
  | [] => some []
  | first :: rest =>
      match declareRow first, declareRows rest with
      | some declared, some remaining => some (declared :: remaining)
      | _, _ => none

theorem declare_row_erase (original : RowPair m) (declared : RowConstraint m)
    (success : declareRow original = some declared) :
    declared.erase = (originalRow original.1, originalRow original.2) := by
  rcases original with ⟨source, target⟩
  cases target with
  | var | empty => cases success; rfl
  | join => cases success

theorem declare_row_exact (original : RowPair m) (declared : RowConstraint m)
    (success : declareRow original = some declared) (rows : Fin m → Common.Row) :
    RowsHold [declared] rows ↔ Common.rowLe (rowEval rows original.1) (rowEval rows original.2) := by
  rw [CommonRowTailInference.rows_hold_iff]
  simp only [CommonRowTailInference.rowProblem, List.map_singleton, declare_row_erase original declared success,
    RowFlowSchemes.Models, List.mem_singleton, forall_eq, RowFlowSchemes.Constraint.Holds, rowEval]
  rfl

theorem declare_row_some (original : RowPair m) (good : simpleRow original.2 = true) :
    ∃ declared, declareRow original = some declared := by
  rcases original with ⟨source, target⟩
  cases target with
  | var | empty => exact ⟨_, rfl⟩
  | join => cases good

theorem declare_rows_erase (original : List (RowPair m)) (declared : List (RowConstraint m))
    (success : declareRows original = some declared) :
    CommonRowTailInference.rowProblem declared =
      original.map (fun pair => (originalRow pair.1, originalRow pair.2)) := by
  induction original generalizing declared with
  | nil => cases success; rfl
  | cons first rest ih =>
      cases head : declareRow first with
      | none => simp [declareRows, head] at success
      | some firstDeclared =>
          cases tail : declareRows rest with
          | none => simp [declareRows, head, tail] at success
          | some remaining =>
              have same : firstDeclared :: remaining = declared := by
                simpa only [declareRows, head, tail, Option.some.injEq] using success
              subst declared
              simp only [CommonRowTailInference.rowProblem, List.map_cons,
                declare_row_erase first firstDeclared head]
              exact congrArg ((originalRow first.1, originalRow first.2) :: ·) (ih remaining tail)

/-- Successful declaration preserves the meaning of every original row
constraint for every independent assignment of the original row variables. -/
theorem declare_rows_exact (original : List (RowPair m)) (declared : List (RowConstraint m))
    (success : declareRows original = some declared) (rows : Fin m → Common.Row) :
    RowsHold declared rows ↔ CommonPresenceConstraintGraph.RowsHold original rows := by
  rw [CommonRowTailInference.rows_hold_iff, declare_rows_erase original declared success]
  simp only [RowFlowSchemes.Models, List.forall_mem_map, RowFlowSchemes.Constraint.Holds,
    CommonPresenceConstraintGraph.RowsHold, rowEval]
  rfl

/-- The generated right-row grammar is sufficient; no condition on the
left rows or on row parameters is needed. -/
theorem declare_rows_some (original : List (RowPair m))
    (good : ∀ pair ∈ original, simpleRow pair.2 = true) :
    ∃ declared, declareRows original = some declared := by
  induction original with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨head, declaredHead⟩ := declare_row_some first (good first List.mem_cons_self)
      obtain ⟨tail, declaredTail⟩ := ih (fun pair member => good pair (List.mem_cons_of_mem _ member))
      exact ⟨head :: tail, by simp only [declareRows, declaredHead, declaredTail]⟩

theorem split_rows_simple (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (good : PresenceSourceConstraintSupport.GoodAtoms atoms) :
    ∀ pair ∈ (CommonPresenceConstraintGraph.splitAtoms atoms).rows, simpleRow pair.2 = true := by
  induction atoms with
  | nil => intro _ impossible; cases impossible
  | cons atom rest ih =>
      have tail := ih (fun actual member => good actual (List.mem_cons_of_mem _ member))
      cases atom with
      | tyLe => exact tail
      | rowLe first last =>
          intro pair member
          rcases List.mem_cons.mp member with same | remaining
          · subst pair
            exact good _ List.mem_cons_self
          · exact tail pair remaining

/-- The actual atom collector satisfies the declaration domain whenever
the source row-shape theorem holds; no proof is passed to `declareRows`. -/
theorem declare_split_rows_some (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (good : PresenceSourceConstraintSupport.GoodAtoms atoms) :
    ∃ declared, declareRows (CommonPresenceConstraintGraph.splitAtoms atoms).rows = some declared :=
  declare_rows_some _ (split_rows_simple atoms good)

/-- The non-row check accepted by declaration is precisely literal true. -/
def RowOrTrue (item : Check Rows Node Child) : Prop :=
  match item with
  | .rowBelow _ _ => True
  | .flag (.literal value) => value = true
  | _ => False

def declareCheck : Check (RowTerm (Fin m)) Node Child → Option (List (RowConstraint m))
  | .rowBelow source target => (declareRow (source, target)).map (fun declared => [declared])
  | .flag (.literal true) => some []
  | _ => none

def declareChecks : Branch (RowTerm (Fin m)) Node Child → Option (List (RowConstraint m))
  | [] => some []
  | first :: rest =>
      match declareCheck first, declareChecks rest with
      | some declared, some remaining => some (declared ++ remaining)
      | _, _ => none

theorem rows_hold_append (first last : List (RowConstraint m)) (rows : Fin m → Common.Row) :
    RowsHold (first ++ last) rows ↔ RowsHold first rows ∧ RowsHold last rows := by
  simp only [RowsHold, List.mem_append, or_imp, forall_and]

theorem declare_check_exact (original : Check (RowTerm (Fin m)) Node Child)
    (declared : List (RowConstraint m)) (success : declareCheck original = some declared)
    (rows : Fin m → Common.Row) (nodes : Node → Common.Ty) (children : Child → Common.Ty) :
    RowsHold declared rows ↔ original.Holds (rowEval rows) nodes children := by
  cases original with
  | rowBelow source target =>
      cases found : declareRow (source, target) with
      | none => simp [declareCheck, found] at success
      | some row =>
          have same : [row] = declared := by
            simpa only [declareCheck, found, Option.map_some, Option.some.injEq] using success
          subst declared
          exact declare_row_exact (source, target) row found rows
  | flag expression =>
      cases expression with
      | literal value =>
          cases value with
          | false => cases success
          | true =>
              cases success
              simp [RowsHold, Check.Holds, CommonSymbolicRecordProfiles.BoolExpr.eval]
      | _ => cases success
  | _ => cases success

/-- Successful check declaration preserves the whole branch meaning for
every independent row, node and child assignment. No checks are left over. -/
theorem declare_checks_exact (original : Branch (RowTerm (Fin m)) Node Child)
    (declared : List (RowConstraint m)) (success : declareChecks original = some declared)
    (rows : Fin m → Common.Row) (nodes : Node → Common.Ty) (children : Child → Common.Ty) :
    RowsHold declared rows ↔ Branch.Holds (rowEval rows) nodes children original := by
  induction original generalizing declared with
  | nil => cases success; simp [RowsHold]
  | cons first rest ih =>
      cases head : declareCheck first with
      | none => simp [declareChecks, head] at success
      | some firstDeclared =>
          cases tail : declareChecks rest with
          | none => simp [declareChecks, head, tail] at success
          | some remaining =>
              have same : firstDeclared ++ remaining = declared := by
                simpa only [declareChecks, head, tail, Option.some.injEq] using success
              subst declared
              rw [rows_hold_append, CommonSymbolicConstraints.holds_cons]
              exact and_congr (declare_check_exact first firstDeclared head rows nodes children)
                (ih remaining tail)

theorem declare_check_some (original : Check (RowTerm (Fin m)) Node Child)
    (simple : CheckRows (fun row => simpleRow row = true) original) (shape : RowOrTrue original) :
    ∃ declared, declareCheck original = some declared := by
  cases original with
  | rowBelow source target =>
      obtain ⟨row, found⟩ := declare_row_some (source, target) simple.2
      exact ⟨[row], by simp only [declareCheck, found, Option.map_some]⟩
  | flag expression =>
      cases expression with
      | literal value =>
          have same : value = true := shape
          subst value
          exact ⟨[], rfl⟩
      | _ => cases shape
  | _ => cases shape

/-- Every branch with simple rows and only row/true checks is accepted by
the total declaration function. These hypotheses are used only in the proof. -/
theorem declare_checks_some (original : Branch (RowTerm (Fin m)) Node Child)
    (simple : AllRows (fun row => simpleRow row = true) original)
    (shape : ∀ check ∈ original, RowOrTrue check) :
    ∃ declared, declareChecks original = some declared := by
  induction original with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨head, declaredHead⟩ := declare_check_some first
        (simple first List.mem_cons_self) (shape first List.mem_cons_self)
      obtain ⟨tail, declaredTail⟩ := ih
        (fun check member => simple check (List.mem_cons_of_mem _ member))
        (fun check member => shape check (List.mem_cons_of_mem _ member))
      exact ⟨head ++ tail, by simp only [declareChecks, declaredHead, declaredTail]⟩

end Yulang.CommonRowDeclarations
