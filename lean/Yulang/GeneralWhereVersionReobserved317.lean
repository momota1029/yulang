import Yulang.GeneralWhereVersionRootSelect317
import Yulang.GeneralWhereVersionPreserve317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 45000000
namespace Yulang.GeneralWhereVersionReobserved317
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry declaration leaf otherChild)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundChildSite316 (signature child)
open GeneralWhereVersionRootReport317 (plan same)
open GeneralWhereVersionCase317 (occ lowerRow upperRow ordered_children)
open GeneralWhereVersionCommit317 (core framedState)
open GeneralWhereVersionInstall317 (fixed Models)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralWhereVersionCompiler317 (schema children)
open GeneralWhereVersionSemantics317 (full)
open GeneralNominalVersionedPlans231 (variables childSchema)
open GeneralDeferredLadderTransport302 (binder_eq capture_eq)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalCommonBridge (Assignment)

/-- The corrected compiler output and ordered generated occurrence are
unchanged when the actual repaired state is read again. -/
theorem rows_and_occurrence :
    (schema plan).equations =
      [⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩,lowerRow,upperRow] ∧
    children plan = [occ] := by
  have sc := GeneralWhereVersionRecompile317.actual_after_observation
  exact ⟨(congrArg GeneralNominalCenteredHeadMatSchemas.Schema.equations sc.2).trans
    GeneralWhereVersionCase317.rows,sc.1⟩

theorem variables_eq {a b : GeneralNominalCenters.Plan rs} (view : Same a b) (m : Assignment) :
    variables a m = variables b m := by
  funext mode name
  simp only [variables,view.declaration,binder_eq view,capture_eq view]

theorem rows_live (m : Assignment) (valid : Models fixed m) :
    (schema plan).unknown = false ∧ (schema plan).Holds (variables plan m) m := by
  have p := (GeneralWhereVersionJournal317.fixed_iff m).mp valid
  have sem := full m p
  rw [GeneralWhereVersionRecompile317.actual_after_observation.2,
    ← variables_eq same]
  exact ⟨sem.materialized,sem.rows⟩

theorem child_same_model (m : Assignment) (valid : Models fixed m) :
    (childSchema plan otherChild signature).Holds (variables plan m) m := by
  have p := (GeneralWhereVersionJournal317.fixed_iff m).mp valid
  rw [GeneralNominalVersionedPlans231.childSchema_eq,
    ← GeneralNominalCenteredHeadMatPlanData.child_schema same,
    ← GeneralNominalVersionedPlans231.childSchema_eq,
    ← variables_eq same]
  exact GeneralWhereVersionSemantics317.same_model_child m p

theorem rechecked (m : Assignment) (valid : Models fixed m) :
    GeneralNominalVersionedDiagnostic232.Local registry framedState root (.selected declaration.id [child]) ∧
    children plan = [occ] ∧
    (schema plan).unknown = false ∧ (schema plan).Holds (variables plan m) m ∧
    (childSchema plan otherChild signature).Holds (variables plan m) m ∧
    GeneralNominalVersionedDiagnostic232.Local registry framedState occ (.selected leaf.id []) ∧
    GeneralWhereVersionRegression317.Evidence m root GeneralLiveCompoundFullResult316.dictionary := by
  have rootLeaf := GeneralWhereVersionRootSelect317.root_and_leaf_on_reobservation
  have row := rows_live m valid
  exact ⟨rootLeaf.1,rootLeaf.2.1,row.1,row.2,child_same_model m valid,rootLeaf.2.2,
    GeneralWhereVersionRegression317.acceptance_sound m valid GeneralWhereVersionRegression317.accepted_root⟩

end Yulang.GeneralWhereVersionReobserved317
