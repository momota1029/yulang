import Yulang.GeneralRebaseTreeSchema272

namespace Yulang.GeneralRebaseTreeSchemaProgress272
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedPlans231 (emittedSchema)
open GeneralNominalCenteredHeadMatSchemas (Equation Schema)
open GeneralRebaseTreeInterpreter272 (Source)
open GeneralRebaseTreeSchema272 (entry compute environment enrich enrich_preserves_source runPlans)
open GeneralRebaseFiniteTree272 (Tree)

def targets (plans : List (Plan roles)) : List Nat :=
 plans.flatMap (fun plan => (emittedSchema plan).equations.map Equation.target)

theorem compute_target (env : GeneralRebaseTreeExprCompile272.Env) (schema : Schema) (id : Nat) (tree : Tree)
 (hit : compute env schema id = some tree) : id ∈ schema.equations.map Equation.target := by
 obtain ⟨xs,eq,ys,inside,h,_⟩ := List.findSome?_eq_some_iff.mp hit
 have listed : eq ∈ schema.equations := by rw [inside]; exact List.mem_append_right _ List.mem_cons_self
 unfold entry at h
 split at h
 · exact List.mem_map.mpr ⟨eq,listed,by assumption⟩
 · contradiction

theorem next_known (plans : List (Plan roles)) (start : Source) (id : Nat) (tree : Tree)
 (before : start id = some tree) : runPlans start plans id = some tree := by
 induction plans generalizing start with
 | nil => exact before
 | cons p ps ih => exact ih (enrich start p) (enrich_preserves_source start p id tree before)

theorem new_target (plans : List (Plan roles)) (start : Source) (id : Nat) (tree : Tree)
 (before : start id = none) (later : runPlans start plans id = some tree) :
 id ∈ targets plans := by
 induction plans generalizing start with
 | nil =>
   change start id = some tree at later
   rw [before] at later
   cases later
 | cons p ps ih =>
   cases direct : enrich start p id with
   | none =>
     exact List.mem_append_right _ (ih (enrich start p) direct later)
   | some known =>
     apply List.mem_append_left
     have hit : compute (environment p start) (emittedSchema p) id = some known := by
       simpa [enrich,before,Option.or] using direct
     exact compute_target _ _ id known hit

def missing (plans : List (Plan roles)) (src : Source) : List Nat :=
 (targets plans).filter (fun id => (src id).isNone)

theorem missing_filters (plans : List (Plan roles)) (src : Source) :
 missing plans (runPlans src plans) = (missing plans src).filter (fun id => (runPlans src plans id).isNone) := by
 unfold missing
 rw [List.filter_filter]
 apply List.filter_congr
 intro id _
 cases before : src id with
 | none => simp
 | some tree =>
   have now := next_known plans src id tree before
   simp [now]

theorem fixed_of_missing (plans : List (Plan roles)) (src : Source)
 (stable : missing plans (runPlans src plans) = missing plans src) :
 runPlans src plans = src := by
 funext id
 cases before : src id with
 | some tree => exact next_known plans src id tree before
 | none =>
   cases arrived : runPlans src plans id with
   | none => rfl
   | some tree =>
     have wasMissing : id ∈ missing plans src :=
       List.mem_filter.mpr ⟨new_target plans src id tree before arrived,Option.isNone_iff_eq_none.mpr before⟩
     rw [← stable] at wasMissing
     have nowNone := Option.isNone_iff_eq_none.mp (List.mem_filter.mp wasMissing).2
     rw [arrived] at nowNone
     cases nowNone

theorem strict (plans : List (Plan roles)) (src : Source) (new : runPlans src plans ≠ src) :
 (missing plans (runPlans src plans)).length < (missing plans src).length := by
 have subset : (missing plans (runPlans src plans)).Sublist (missing plans src) := by
   rw [missing_filters]
   exact List.filter_sublist ..
 have numbers := subset.length_le
 have distinct : (missing plans (runPlans src plans)).length ≠ (missing plans src).length :=
   fun same => new (fixed_of_missing plans src (subset.eq_of_length same))
 omega

end Yulang.GeneralRebaseTreeSchemaProgress272
