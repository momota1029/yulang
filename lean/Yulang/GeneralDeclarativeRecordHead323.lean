import Yulang.GeneralDeclarativeRecordResidual323
import Yulang.GeneralDeclarativeCompileLists321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordHead323
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeRecordWalk323 (recordExpr substFields)
open GeneralDeclarativeRecordResidual323 (withTail prefix_congr reconstruct_with_terminal permute_fields)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized translate_value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm record_congr)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalMaterialization (Mode)
open CommonRoleCanonicalRows (Row selected residual)
open CommonRoleOutermostResolver (All₂)

theorem logical_spine (cap : Nat → Capture) (mode : Mode) (fields : Row Expr) (tail : Expr) :
    logical cap mode (withTail fields tail) = withTail (substFields cap mode fields) (logical cap mode tail) := by
  induction fields with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨label,expr⟩ := entry
    simp [withTail,logical,substFields,ih]

def FieldValue (m : Assignment) (x y : Nat × Expr) : Prop :=
  x.1 = y.1 ∧ eqAt m x.2 y.2

theorem field_congr (m : Assignment) (known : All₂ (FieldValue m) xs ys)
    (tail : eqAt m forever actual) :
    eqAt m (withTail xs forever) (withTail ys actual) := by
  induction known with
  | nil => exact tail
  | @cons one two xs ys here _ ih =>
    obtain ⟨l,x⟩ := one
    obtain ⟨k,y⟩ := two
    have same : l = k := here.1
    subst k
    exact record_congr _ here.2 ih

theorem selected_nodup (actual : Row Expr) (written : List Nat)
    (noDuplicate : (actual.map Prod.fst).Nodup) :
    ((selected written actual).map Prod.fst).Nodup := by
  have sub : (selected written actual).Sublist actual := List.filter_sublist
  exact noDuplicate.sublist (sub.map Prod.fst)

/-- Comparing the actual fields by their source labels need not constrain
the order they were written. First-field normalization is required
before the partition/permutation, not imposed as a new source restriction. -/
theorem permuted_head {s : State} {p : Pattern} (actual written : Row Expr)
    (terminal : Expr) (unique : (actual.map Prod.fst).Nodup)
    (root : Entails s ⟨arg.center,withTail actual terminal⟩)
    (residualRead : Entails s ⟨(capture binder).center,
      withTail (residual (written.map Prod.fst) actual) terminal⟩)
    (permutation : (selected (written.map Prod.fst) actual).Perm inSourceOrder)
    (fields : ∀ m, Models s m → All₂ (FieldValue m) inSourceOrder (substFields capture .actual written))
    (newCode : translate c interp (normalize p) = some (withTail written (.variable binder)))
    (rawCode : translate c interp p = some raw) :
    Result s (headFact c interp capture arg p) := by
  refine ⟨[⟨arg.center,logical capture .actual raw⟩],by simp [headFact,rawCode],?_⟩
  intro row member m valid
  cases List.mem_singleton.mp member
  have exactSpine : eqAt m (withTail actual terminal) (logical capture .actual (withTail written (.variable binder))) := by
    rw [logical_spine]
    exact eqv_trans (reconstruct_with_terminal m actual _ terminal unique)
      (eqv_trans (permute_fields m _ permutation (selected_nodup actual _ unique))
        (field_congr m (fields m valid) (eqv_symm (residualRead m valid))))
  have normalized := translate_value (normalize p) (variables := variables capture m) newCode
  have spelling := compiled_normalized (variables := variables capture m) rawCode
  rw [← normalized] at spelling
  simp only [Holds,logical_value]
  simp only [eqAt,logical_value] at exactSpine
  exact eqv_trans (root m valid) (eqv_trans exactSpine (eqv_symm spelling))

/-- Source record-tail binding at a known canonical actual spine. The
readback supplies the *computed* residual, not an arbitrary tail that
makes a record type equivalent. Root, field and tail names remain fixed. -/
theorem head {s : State} {p : Pattern} (actual : Row Expr)
    (written : Row Expr) (terminal : Expr) (unique : (actual.map Prod.fst).Nodup)
    (root : Entails s ⟨arg.center,withTail actual terminal⟩)
    (knownTail : Entails s ⟨(capture binder).center,
      withTail (residual (written.map Prod.fst) actual) terminal⟩)
    (fields : ∀ m, Models s m → All₂ (FieldValue m)
      (selected (written.map Prod.fst) actual) (substFields capture .actual written))
    (newCode : translate c interp (normalize p) = some (withTail written (.variable binder)))
    (rawCode : translate c interp p = some raw) :
    Result s (headFact c interp capture arg p) :=
  permuted_head actual written terminal unique root knownTail (.refl _) fields newCode rawCode

end Yulang.GeneralDeclarativeRecordHead323
