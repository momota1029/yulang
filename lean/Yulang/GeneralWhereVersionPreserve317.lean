import Yulang.GeneralWhereVersionBatchAgree317
import Yulang.GeneralWhereVersionRegression317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 45000000
namespace Yulang.GeneralWhereVersionPreserve317
open GeneralWhereVersionCompiler317 (schema)
open GeneralWhereVersionCase317 (lower upper lowerRow upperRow expr)
open GeneralLiveCompoundPostFrames316 (rootPlan root_frame_plan)
open GeneralLiveCompoundPostRootHead316 (frame head)
open GeneralLiveCompoundPostRootSelect316 (selected classes)
open GeneralLiveCompoundLeafInstall316 (after after_model reachable)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundChildSite316 (child)
open GeneralLiveCompoundRegistry316 (boundary_checked sourceRegistry declaration otherChild)
open GeneralLiveCompoundProposedRepair316 (cursor)
open GeneralNominalVersionedJournal232 (Models Effect)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds variables)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedChildEndpointCut315 (BaseReady)
open GeneralVersionedEndpointBatch315 (Proposal)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open CommonNominalFullCarrier

open GeneralWhereVersionWitness317 (ParentHolds lowerProposal upperProposal actual_row)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralWhereVersionInstall317 (fixed before models)
open GeneralWhereVersionJournal317 (fixed_iff)

theorem model_from_each_agrees (prior : Assignment) (valid : Models after prior) :
    ∃ m, ParentHolds m ∧ GeneralNominalCenteredFrame179.Agree (sources after) prior m := by
  obtain ⟨e,g,s,o,k,c⟩ := GeneralNominalVersionedMixedSelectedEffect235.source_effect boundary_checked reachable selected
  have f := e.frame
  rw [g,s,o] at f
  have eq := root_frame_plan f
  have base := GeneralVersionedCompleteInModel315.shared boundary_checked reachable selected frame
    cursor rfl prior valid
  obtain ⟨full,head',schema',classes'⟩ := base
  let ready := GeneralVersionedCompleteInModel315.fill after rootPlan GeneralLiveCompoundRoot316.plan prior
  have begins : BaseReady after e ready := by
    refine ⟨full,?_,?_,?_⟩
    · rw [eq]; exact head'
    · rw [eq]; exact schema'
    · change GeneralNominalVersionedEffects231.ClassEffects after.core e.plan.packet.site.occurrence e.plan ready
      rw [o,eq]; exact classes'
  let a : Proposal e.plan := eq.symm ▸ lowerProposal
  let b : Proposal e.plan := eq.symm ▸ upperProposal
  obtain ⟨m,extended,stays,vals⟩ := GeneralWhereVersionBatchAgree317.batch_agrees reachable g s begins [a,b]
  have headOk := extended.2.1
  have schemaOk := extended.2.2.1
  have heldClasses := extended.2.2.2
  rw [eq] at headOk schemaOk
  change GeneralNominalVersionedEffects231.ClassEffects after.core e.plan.packet.site.occurrence e.plan m at heldClasses
  rw [o,eq] at heldClasses
  refine ⟨m,⟨extended.1,headOk,schemaOk,heldClasses,?_⟩,?_⟩
  case refine_2 =>
    intro name seen
    exact (GeneralVersionedCompleteInModel315.preserved after rootPlan GeneralLiveCompoundRoot316.plan prior _ (List.mem_append_left _ seen)).trans
      (stays name seen)
  have low := vals a List.mem_cons_self
  have upp := vals b (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have low' : lowerRow.Holds (variables rootPlan m) m := by
    dsimp only [a] at low
    generalize eq : e.plan = rootPlan at *
    cases eq
    exact low
  have upp' : upperRow.Holds (variables rootPlan m) m := by
    dsimp only [b] at upp
    generalize eq : e.plan = rootPlan at *
    cases eq
    exact upp
  intro row present
  rw [GeneralWhereVersionCase317.rows] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · exact actual_row m extended.1
  · exact low'
  · exact upp'

theorem exact_legacy_projection (prior : Assignment) (valid : GeneralWhereVersionInstall317.Models before prior) :
    ∃ m, GeneralWhereVersionInstall317.Models fixed m ∧
      GeneralNominalCenteredFrame179.Agree (sources after) prior m := by
  obtain ⟨m,held,agreement⟩ := model_from_each_agrees prior valid.1
  exact ⟨m,models m held,agreement⟩

theorem no_legacy_model_lost_or_created (prior : Assignment) :
    GeneralWhereVersionInstall317.Models before prior ↔
      ∃ m, GeneralWhereVersionInstall317.Models fixed m ∧
        GeneralNominalCenteredFrame179.Agree (sources after) prior m := by
  constructor
  · exact exact_legacy_projection prior
  · rintro ⟨m,valid,agree⟩
    have old := ((fixed_iff m).mp valid).1
    refine ⟨(GeneralNominalVersionedJournalFrame236.models_iff after agree).mpr old,?_⟩
    intro _ absent
    cases absent

end Yulang.GeneralWhereVersionPreserve317
