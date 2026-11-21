import Yulang.GeneralDeclarativeExactWalk323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordWalk323
open GeneralDeclarativeExactWalk323 (Exact)
open GeneralDeclarativeHead320 (environment)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)
open GeneralDeclarativeRepeatedActual323 (eqAt BindsAt split_binds)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl record_congr)
open GeneralNominalStructuralReadback (recordValues record_payload)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeWhere319 (Capture)
open CommonNominalFullCarrier (Ty Equivalent)

def recordExpr : List (Nat × Expr) → Expr
  | [] => .primitive .emptyRecord []
  | (label,payload)::rest => .record label payload (recordExpr rest)

def valuesOf (m : Assignment) (fields : List (Nat × Expr)) : List (Nat × Ty) :=
  fields.map fun p => (p.1,value (environment m) .actual p.2)

def substFields (cap : Nat → Capture) (mode : Mode) (fields : List (Nat × Expr)) : List (Nat × Expr) :=
  fields.map fun p => (p.1,logical cap mode p.2)

theorem eval_record (m : Assignment) (fields : List (Nat × Expr)) :
    value (environment m) .actual (recordExpr fields) = recordValues (valuesOf m fields) := by
  induction fields with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨label,payload⟩ := p
    simp only [recordExpr,value,ih]
    rfl

theorem logical_record (cap : Nat → Capture) (mode : Mode) (fields : List (Nat × Expr)) :
    logical cap mode (recordExpr fields) = recordExpr (substFields cap mode fields) := by
  induction fields with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨label,payload⟩ := p
    simp only [recordExpr,logical,ih]
    rfl

inductive Fields (mode : Mode) : List (Nat × Expr) → List (Nat × Expr) → List Occurrence → Prop where
  | nil : Fields mode [] [] []
  | cons : Exact mode t c first → Fields mode rest tail next →
      Fields mode ((label,t)::rest) ((label,c)::tail) (first ++ next)

theorem fields_walk (views : Fields mode xs ys seen) :
    Walk mode (recordExpr xs) (recordExpr ys) seen := by
  induction views with
  | nil => exact .primitive .nil
  | cons first _ ih => exact .record first.walked ih

theorem same_labels (views : Fields mode xs ys seen) : xs.map Prod.fst = ys.map Prod.fst := by
  induction views with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem fields_have_exact_payloads (m : Assignment) (cap : Nat → Capture)
    (views : Fields mode xs ys seen) (unique : (xs.map Prod.fst).Nodup)
    (whole : eqAt m (recordExpr xs) (logical cap mode (recordExpr ys))) :
    ∀ label first last, (label,first) ∈ xs → (label,last) ∈ ys →
      eqAt m first (logical cap mode last) := by
  rw [eqAt,logical_record,eval_record,eval_record] at whole
  have distinct1 : ((valuesOf m xs).map Prod.fst).Nodup := by
    simpa only [valuesOf,List.map_map,Function.comp_def] using unique
  have distinct2 : ((valuesOf m (substFields cap mode ys)).map Prod.fst).Nodup := by
    simpa only [valuesOf,substFields,List.map_map,Function.comp_def,← same_labels views] using unique
  intro l a b hasA hasB
  exact record_payload _ _ distinct1 distinct2 (List.mem_map.mpr ⟨(l,a),hasA,rfl⟩)
    (List.mem_map.mpr ⟨(l,logical cap mode b),List.mem_map.mpr ⟨(l,b),hasB,rfl⟩,rfl⟩) whole

theorem from_payloads (m : Assignment) (cap : Nat → Capture)
    (views : Fields mode xs ys seen)
    (atLabel : ∀ l a b, (l,a) ∈ xs → (l,b) ∈ ys → eqAt m a (logical cap mode b)) :
    BindsAt m cap seen := by
  induction views with
  | nil =>
    intro _ bad
    cases bad
  | cons first tail ih =>
    apply (split_binds ..).mpr
    exact ⟨(first.semantic m cap).mp (atLabel _ _ _ List.mem_cons_self List.mem_cons_self),
      ih (fun l a b ha hb => atLabel l a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb))⟩

theorem builds_record (m : Assignment) (cap : Nat → Capture)
    (views : Fields mode xs ys seen) (each : BindsAt m cap seen) :
    eqAt m (recordExpr xs) (logical cap mode (recordExpr ys)) := by
  induction views with
  | nil => exact eqv_refl _
  | cons first _ ih =>
    have parts := (split_binds ..).mp each
    exact record_congr _ ((first.semantic m cap).mpr parts.1) (ih parts.2)

/-- Matching a normalized closed record is exact on the visible labels.
An arbitrary open tail or shadowed occurrence is not inverted. -/
theorem closed_record (views : Fields mode xs ys seen) (visible : (xs.map Prod.fst).Nodup) :
    Exact mode (recordExpr xs) (recordExpr ys) seen :=
  ⟨fields_walk views,fun m cap =>
    ⟨fun same => from_payloads m cap views (fields_have_exact_payloads m cap views visible same),
      builds_record m cap views⟩⟩

end Yulang.GeneralDeclarativeRecordWalk323
