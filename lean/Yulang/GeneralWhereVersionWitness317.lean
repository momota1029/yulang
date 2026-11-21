import Yulang.GeneralWhereVersionBase317
import Yulang.GeneralVersionedCompleteInModel315

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 30000000
namespace Yulang.GeneralWhereVersionWitness317
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

noncomputable def lowerProposal : Proposal rootPlan :=
  ⟨.lower,otherChild,0,lowerRow,List.mem_singleton_self _,⟨.variant 0 (.var 0),rfl,rfl⟩,rfl⟩

noncomputable def upperProposal : Proposal rootPlan :=
  ⟨.upper,otherChild,0,upperRow,List.mem_singleton_self _,⟨.variant 0 (.var 0),rfl,rfl⟩,rfl⟩

def ParentHolds (m : Assignment) : Prop :=
  Models after m ∧ HeadModels rootPlan.packet m ∧ SchemaHolds rootPlan rootPlan.headSchema m ∧
    GeneralNominalVersionedEffects231.ClassEffects after.core GeneralDictionaryJournalRefinement228Source.root rootPlan m ∧
    (schema rootPlan).Holds (variables rootPlan m) m

theorem both_values (m : Assignment) (valid : Models after m) (h : HeadModels rootPlan.packet m)
    (lo : lowerRow.Holds (variables rootPlan m) m) (hi : upperRow.Holds (variables rootPlan m) m) :
    Equivalent (m lower).1 (variant 0 (m 2).1) ∧ Equivalent (m upper).1 (variant 0 (m 2).1) := by
  have old := GeneralLiveCompoundCulprit316.old_head m h
  have l := GeneralVersionedEndpointBadRow315.new_operand m old
  have u := (GeneralVersionedEndpointBadRow315.raw_upper_projections m
    (GeneralLiveCompoundPostFeedback316.old_valid m valid) old).2
  rw [GeneralLiveCompoundCulprit316.variables_pair] at lo hi
  exact ⟨equivalent_trans lo ⟨(common_variant_iff ..).mpr l.1,(common_variant_iff ..).mpr l.2⟩,
    equivalent_trans hi ⟨(common_variant_iff ..).mpr u.1,(common_variant_iff ..).mpr u.2⟩⟩

theorem actual_row (m : Assignment) (valid : Models after m) :
    (⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩ : Equation).Holds (variables rootPlan m) m := by
  change Equivalent (m 4).1 GeneralDictionaryOptionalOutput229.value
  have old := GeneralLiveCompoundPostFeedback316.old_valid m valid
  exact GeneralDictionaryCompoundObstruction238.associated_value m
    (GeneralMixedCompoundUpperSupport307.child_history m old)

theorem model_from_each (prior : Assignment) (valid : Models after prior) :
    ∃ m, ParentHolds m := by
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
  obtain ⟨m,extended,vals⟩ := GeneralVersionedEndpointBatch315.batch reachable g s begins [a,b]
  have headOk := extended.2.1
  have schemaOk := extended.2.2.1
  have heldClasses := extended.2.2.2
  rw [eq] at headOk schemaOk
  change GeneralNominalVersionedEffects231.ClassEffects after.core e.plan.packet.site.occurrence e.plan m at heldClasses
  rw [o,eq] at heldClasses
  refine ⟨m,extended.1,headOk,schemaOk,heldClasses,?_⟩
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

theorem inhabited : ∃ m, ParentHolds m := model_from_each w after_model

end Yulang.GeneralWhereVersionWitness317
