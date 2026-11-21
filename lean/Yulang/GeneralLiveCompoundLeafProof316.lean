import Yulang.GeneralLiveCompoundLeafHead316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 22000000
namespace Yulang.GeneralLiveCompoundLeafProof316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot lower_width width_two)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry leaf leaf_checked source checked)
open GeneralLiveCompoundUpperRefresh316 (upperState old_models)
open GeneralLiveCompoundUpperSnapshot316 (snap context)
open GeneralLiveCompoundChildSite316
open GeneralLiveCompoundLeafHead316 (packet plan bindings head)
open GeneralSourceDictionaries GeneralNominalCenters GeneralDeclarations
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedCandidates231
open GeneralNominalRecursiveInspection (Origin Observes Test)
open GeneralNominalVersionedJournal232 (Models)
open CommonNominalFullCarrier

noncomputable abbrev w := GeneralDictionaryCompoundPointModel238.extended

theorem valid : Models upperState w :=
  (old_models w).mpr GeneralVersionedEndpointObstructionHead315.valid

theorem binder_exact : GeneralNominalVersionedFrame231.binder plan 0 =
    GeneralNominalCenters.fresh snapshot.seed child.identity leaf.id 8 0 0 := by
  unfold GeneralNominalVersionedFrame231.binder
  change (if (0:Nat) ∈ leaf.outputNames then _ else if
    ((GeneralNominalVersionedFrame231.capture packet).inputs 0).1 =
    ((GeneralNominalVersionedFrame231.capture packet).inputs 0).2 then _ else _) = _
  have input : (GeneralNominalVersionedFrame231.capture packet).inputs 0 = (4,2) := by
    change (GeneralNominalVersionedAllocation231.capture snap registry child.identity leaf.id packet.bindings).inputs 0 = _
    rw [bindings]; rfl
  simp [input,show (0:Nat) ∉ leaf.outputNames from by decide]
  rfl

abbrev binderId := GeneralNominalCenters.fresh snapshot.seed child.identity leaf.id 8 0 0

theorem binder_value : (w binderId).1 = .emptyRecord := by
  have two (i : Fin 2) : i = 0 ∨ i = 1 := by omega
  have three (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  change (GeneralDictionaryCompoundPointModel238.extended binderId).1 = _
  rw [GeneralDictionaryCompoundPointModel238.extended,
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (by intro i h; rcases two i with rfl|rfl <;> exact (by decide +kernel : _ ≠ _) h),
    GeneralDictionaryCompoundVersionedModel238.extended,
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (by intro i h; rcases two i with rfl|rfl <;> exact (by decide +kernel : _ ≠ _) h)]
  change (GeneralDictionaryCompoundModel238.extended binderId).1 = _
  rw [GeneralDictionaryCompoundModel238.extended,
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (by intro i h; rcases three i with rfl|rfl|rfl <;> exact (by decide +kernel : _ ≠ _) h)]
  change (GeneralDictionaryCompoundPacket238.model binderId).1 = _
  unfold GeneralDictionaryCompoundPacket238.model
  simp [show ¬ binderId ≤ 4 from by decide +kernel,
    show binderId ≠ GeneralDictionaryCompoundPacket238.lo from by decide +kernel]

theorem selected_bounds : (GeneralNominalVersionedFrame231.capture packet).inputs 0 = (4,2) := by
  change (GeneralNominalVersionedAllocation231.capture snap registry child.identity leaf.id packet.bindings).inputs 0 = _
  rw [bindings]; rfl

theorem head_schema : plan.headSchema =
    ⟨[⟨0,projection,.actual⟩],[(ref,.structural (.variant 0))],false⟩ := by
  unfold Plan.headSchema
  change GeneralNominalMaterialization.schemas (GeneralNominalInspection.queries snap context.interpretation leaf)
    (fun index => .source ((List.ofFn childSite.center)[index]?.getD 0)) .actual 0 = _
  rw [leaf_query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,ref,projection,center_id]

theorem center_value : Equivalent (w GeneralMixedCompoundChildEquality307.mid).1 (variant 0 .emptyRecord) := by
  have old := GeneralVersionedEndpointObstructionHead315.valid
  have a := GeneralMixedCompoundChildEquality307.historical_child_center w
    (old.2.1 GeneralDictionaryCompoundObstruction238.oldPlan GeneralDictionaryCompoundPoint238.original_plan_retained)
  have b := width_two w old.1.2.1
  exact GeneralDictionaryDefaultExpression209.equivalent_trans a
    ⟨(common_variant_iff ..).mpr b.1,(common_variant_iff ..).mpr b.2⟩

theorem schema : SchemaHolds plan plan.headSchema w := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source _⟩,?_⟩
    intro value seen
    cases seen
    exact ⟨[.emptyRecord],rfl,center_value⟩
  · intro entry member
    cases List.mem_singleton.mp member
    change GeneralNominalOriginTerms.Same w projection (.source (GeneralNominalVersionedFrame231.binder plan 0))
    rw [binder_exact]
    have projected : Observes w projection .emptyRecord :=
      .structural (.source _) (values := [.emptyRecord]) rfl center_value rfl
    refine ⟨⟨_,projected⟩,⟨_,.source _⟩,?_⟩
    intro a b ha hb
    cases hb
    rw [binder_value]
    cases ha with
    | structural parent length equal found =>
      cases parent
      have full := GeneralDictionaryDefaultExpression209.equivalent_trans ⟨equal.2,equal.1⟩ center_value
      exact GeneralNominalStructuralReadback.shape_payload (.variant 0) (by trivial) _ [.emptyRecord]
        length rfl found rfl full

end Yulang.GeneralLiveCompoundLeafProof316
