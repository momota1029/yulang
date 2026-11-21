import Yulang.GeneralWhereVersionCommit317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 44000000
/-! Semantic kernel of the prototype. No bounds, output provenance, or
head equations are dropped. Only the where rows and the descriptor
intervals are supplied by the versioned canonical emission. -/
namespace Yulang.GeneralWhereVersionSemantics317
open GeneralWhereVersionCompiler317 (child schema children)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds variables childSchema)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters GeneralDeclarations
open GeneralWhereVersionCase317 (site centers_preserved)
open GeneralWhereVersionCommit317 (core corrected_site)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralLiveCompoundPostRootHead316 (frame)
open GeneralLiveCompoundLeafInstall316 (after reachable)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (otherChild boundary_checked)
open GeneralLiveCompoundChildSite316 (signature)
open GeneralDictionaryJournalRefinement228Source (roles root)
open CommonNominalFullCarrier
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

structure Holds {rs : Roles.RoleDecls} (p : Plan rs) (m : Assignment) : Prop where
  head : HeadModels p.packet m
  input : p.input.Holds m
  captures : ∀ name, name ∈ p.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed p.packet name →
    GeneralNominalCaptureMerges.Fits m ((GeneralNominalVersionedFrame231.capture p.packet).inputs name)
      (m (GeneralNominalVersionedFrame231.binder p name)).1
  headSchema : SchemaHolds p p.headSchema m
  materialized : (schema p).unknown = false
  rows : (schema p).Holds (variables p m) m
  childSemantics : ∀ clause ∈ p.packet.declaration.requirements, ∀ sig : clause.Signature rs,
    (child p clause sig).Holds m ∧ (childSchema p clause sig).Holds (variables p m) m

theorem actual_binders (m : Assignment) (valid : ParentHolds m) :
    Equivalent (variables rootPlan m .actual 0) (m 2).1 := by
  have value := GeneralNominalVersionedCurrentHead237.capture_fits rootPlan frame valid.1 valid.2.1
    valid.2.2.1 0 (.inl (by decide +kernel))
  have head := GeneralLiveCompoundCulprit316.old_head m valid.2.1
  have reads := GeneralVersionedEndpointBadRow315.raw_upper_projections m
    (GeneralLiveCompoundPostFeedback316.old_valid m valid.1) head
  have low := GeneralVersionedEndpointBadRow315.new_operand m head
  have slotLo : Equivalent (variables rootPlan m .lower 0) (m 2).1 := by
    rw [GeneralLiveCompoundCulprit316.variables_pair]; exact low
  have slotHi : Equivalent (variables rootPlan m .upper 0) (m 2).1 := by
    rw [GeneralLiveCompoundCulprit316.variables_pair]; exact reads.2
  have notOutput : ¬ (0:Nat) ∈ rootPlan.packet.declaration.outputNames := by decide +kernel
  unfold variables at slotLo slotHi
  simp only [notOutput,ite_false] at slotLo slotHi
  change Equivalent (m (GeneralNominalVersionedFrame231.binder rootPlan 0)).1 (m 2).1
  exact ⟨subtype_trans value.2 slotHi.1,subtype_trans slotLo.2 value.1⟩

theorem actual_child_schema : childSchema rootPlan otherChild signature =
    ⟨[⟨GeneralMixedCompoundChildEquality307.mid,.actual,GeneralWhereVersionCase317.expr⟩],false⟩ := by
  change childSchema (GeneralNominalVersionedTransport231.extendedPlan _ _ _ GeneralLiveCompoundCurrentRoot316.plan)
    otherChild signature = _
  rw [GeneralNominalVersionedTransport231.childSchema_eq,GeneralNominalVersionedPlans231.childSchema_eq]
  rfl

theorem same_model_child (m : Assignment) (valid : ParentHolds m) :
    (childSchema rootPlan otherChild signature).Holds (variables rootPlan m) m := by
  rw [actual_child_schema]
  intro row seen
  cases List.mem_singleton.mp seen
  change Equivalent (m GeneralMixedCompoundChildEquality307.mid).1 (variant 0 (variables rootPlan m .actual 0))
  have history := GeneralLiveCompoundPostFeedback316.old_valid m valid.1
  have center := GeneralMixedCompoundChildEquality307.historical_child_center m
    (GeneralMixedCompoundUpperSupport307.child_history m history)
  have actual := actual_binders m valid
  exact equivalent_trans center ⟨(common_variant_iff ..).mpr actual.2,(common_variant_iff ..).mpr actual.1⟩

theorem materialized : (schema rootPlan).unknown = false := by
  unfold schema
  rw [GeneralWhereVersionCase317.emission_exact]
  rfl

theorem full (m : Assignment) (valid : ParentHolds m) : Holds rootPlan m := by
  refine ⟨valid.2.1,valid.1.1.2.2.2.1 _ frame.center_recorded,?_,valid.2.2.1,materialized,valid.2.2.2.2,?_⟩
  · exact GeneralNominalVersionedCurrentHead237.capture_fits rootPlan frame valid.1 valid.2.1 valid.2.2.1
  · intro clause member sig
    have eq : clause = otherChild := List.mem_singleton.mp member
    subst clause
    exact ⟨corrected_site m valid,same_model_child m valid⟩

theorem outputs (m : Assignment) (valid : ParentHolds m) :
    ∀ out ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness rootPlan m out := by
  intro out request
  apply GeneralDictionaryDefaultEvidence204Laws.output_of_class_effects
    (GeneralNominalVersionedMixedReady235.ready boundary_checked reachable frame)
    ((GeneralNominalVersionedEffects231.class_effects_iff ..).mp valid.2.2.2.1)
  exact GeneralNominalCenteredHeadOutputs.request_retained rootPlan.packet.site frame.raw_recorded
    (GeneralNominalSaturationState.Alias.refl _) request

end Yulang.GeneralWhereVersionSemantics317
