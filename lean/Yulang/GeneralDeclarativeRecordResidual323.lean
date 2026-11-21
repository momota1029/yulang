import Yulang.GeneralDeclarativeRecordWalk323
import Yulang.GeneralNominalCommonBridge
import Yulang.GeneralDeclarativeNewNames321
import Yulang.CommonRoleCanonicalRows

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordResidual323
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (Entails appendFacts model_append literal)
open GeneralDeclarativeRecordWalk323 (recordExpr eval_record valuesOf)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeNewNames321 (supply after old_plus_extra)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans record_congr)
open CommonRoleCanonicalRows (Row selected residual mem_residual)
open GeneralNominalCommonBridge (Assignment)

def withTail : Row Expr → Expr → Expr
  | [],tail => tail
  | (label,payload)::rest,tail => .record label payload (withTail rest tail)

theorem prefix_append (xs ys : Row Expr) :
    withTail xs (recordExpr ys) = recordExpr (xs ++ ys) := by
  induction xs with
  | nil => rfl
  | cons entry more ih =>
    rcases entry with ⟨label,field⟩
    simp [withTail,recordExpr,ih]

theorem prefix_congr (m : Assignment) (xs : Row Expr) (split : eqAt m a b) :
    eqAt m (withTail xs a) (withTail xs b) := by
  induction xs with
  | nil => exact split
  | cons row rest ih =>
    obtain ⟨label,payload⟩ := row
    exact record_congr _ (eqv_refl _) ih

theorem withTail_append (xs ys : Row Expr) (terminal : Expr) :
    withTail xs (withTail ys terminal) = withTail (xs ++ ys) terminal := by
  induction xs with
  | nil => rfl
  | cons entry more ih =>
    rcases entry with ⟨label,field⟩
    simp [withTail,ih]

theorem permute_fields (m : Assignment) (terminal : Expr)
    {xs ys : Row Expr} (permutation : xs.Perm ys) (unique : (xs.map Prod.fst).Nodup) :
    eqAt m (withTail xs terminal) (withTail ys terminal) := by
  induction permutation with
  | nil => exact eqv_refl _
  | cons h p ih =>
    exact record_congr h.1 (eqv_refl _) (ih (List.nodup_cons.mp unique).2)
  | swap a b rest =>
    have ne : a.1 ≠ b.1 := by
      intro eq
      exact (List.nodup_cons.mp unique).1 (List.mem_cons.mpr (.inl eq.symm))
    exact GeneralNominalCommonBridge.swap _ _ (Ne.symm ne) _ _ _
  | trans first second ih jh =>
    exact eqv_trans (ih unique) (jh ((first.map Prod.fst).nodup_iff.mp unique))

theorem partition_permutation (names : List Nat) (fields : Row Expr) :
    (selected names fields ++ residual names fields).Perm fields :=
  List.filter_append_perm (fun (e : Nat × Expr) => names.contains e.1) fields

/-- Subtract only the written names from the known canonical spine.
The chosen terminal is preserved, so a closed exact tail is not
identified with a width-ended record or a producer mask. -/
theorem reconstruct_with_terminal (m : Assignment) (fields : Row Expr)
    (written : List Nat) (terminal : Expr) (unique : (fields.map Prod.fst).Nodup) :
    eqAt m (withTail fields terminal)
      (withTail (selected written fields) (withTail (residual written fields) terminal)) := by
  rw [withTail_append]
  exact permute_fields m terminal (partition_permutation written fields).symm unique

theorem empty_terminal (fields : Row Expr) :
    withTail fields (.primitive .emptyRecord []) = recordExpr fields := by
  induction fields with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨label,item⟩ := entry
    simp [withTail,recordExpr,ih]

/-- The width-ended case uses the same subtraction as every other
known terminal, without making an empty-tail assumption for callers. -/
theorem reconstruct (m : Assignment) (fields : Row Expr) (written : List Nat)
    (unique : (fields.map Prod.fst).Nodup) :
    eqAt m (recordExpr fields) (withTail (selected written fields) (recordExpr (residual written fields))) := by
  simpa only [empty_terminal] using reconstruct_with_terminal m fields written (.primitive .emptyRecord []) unique

theorem reconstruct_at_actual {s : State} (fields : Row Expr) (written : List Nat)
    (unique : (fields.map Prod.fst).Nodup)
    (full : Entails s ⟨root,recordExpr fields⟩)
    (hasRemainder : Entails s ⟨tailName,recordExpr (residual written fields)⟩) :
    Entails s ⟨root,withTail (selected written fields) (.variable tailName)⟩ :=
  fun m valid => eqv_trans (full m valid) (eqv_trans (reconstruct m fields written unique)
    (prefix_congr m _ (eqv_symm (hasRemainder m valid))))

/-- Source computation chooses a fresh logical name only for the actual
remainder. Older ordinary models and requested output names are untouched. -/
theorem fresh_remainder {s : State} (fields : Row Expr) (written : List Nat) (keepNames : List Nat)
    (unique : (fields.map Prod.fst).Nodup)
    (full : Entails s ⟨root,recordExpr fields⟩) :
    ∃ row : Equation,
      row.right = recordExpr (residual written fields) ∧
      (∀ m, Models s m → ∃ m', Models (appendFacts s [row]) m' ∧
        ∀ n ∈ stateNames s ++ (keepNames ++ root :: names (recordExpr fields)), m' n = m n) ∧
      Entails (appendFacts s [row]) ⟨root,withTail (selected written fields) (.variable row.left)⟩ := by
  let rhs := recordExpr (residual written fields)
  let allKept := keepNames ++ root :: names (recordExpr fields)
  let row : Equation := ⟨after ((stateNames s ++ allKept) ++ [rhs].flatMap names),rhs⟩
  have supplyExact : supply s allKept [rhs] = [row] := rfl
  refine ⟨row,rfl,?_,?_⟩
  · intro m valid
    have extension := old_plus_extra s allKept [rhs] m valid
    rw [supplyExact] at extension
    exact ⟨_,extension⟩
  · apply reconstruct_at_actual fields written unique
    · exact fun m good => full m ((model_append m).mp good).1
    · exact literal (List.mem_append_right _ List.mem_cons_self)

end Yulang.GeneralDeclarativeRecordResidual323
