import Yulang.GeneralRebaseRowGeneratedChild287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 15000000
namespace Yulang.GeneralRebaseRowWholeChild287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child center)
open GeneralRebaseRowParentFrame287 (after after_model)
open GeneralRebaseRowGeneratedChild287
open GeneralNominalCenters (Plan Site)
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedPlans231 (Ordinary Holds Outputs emittedSchema SchemaHolds)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry true,current true,(center true).observed,opaqueChild,opaque_checked,
    [((0 : Fin 3),(0 : Fin 3))]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,center true,rfl⟩

theorem query : GeneralNominalInspection.queries (current true).state (current true).interpretation opaqueChild =
    [.variables [0]] := by
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate]

theorem report_exact : GeneralNominalPacketSupport.report packet =
    { captures := [⟨0,((0 : Fin 3),(0 : Fin 3)),none⟩],
      checked := [((0 : Fin 3),(0 : Fin 3)),((0 : Fin 3),(0 : Fin 3))] } := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [show GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = _ from query]
  simp [inspectMany,inspect,Report.append]

theorem bindings_exact : packet.bindings = [(0,(0,0))] := by
  change bindings (current true).state (GeneralNominalPacketSupport.report packet) = _
  rw [report_exact]
  rfl

theorem capture : (GeneralNominalVersionedFrame231.capture packet).inputs 0 = (0,0) := by
  change (GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs 0 = _
  rw [bindings_exact]
  rfl

theorem binder : GeneralNominalVersionedFrame231.binder plan 0 = 0 := by
  unfold GeneralNominalVersionedFrame231.binder
  change (if 0 ∈ opaqueChild.outputNames then _ else _) = _
  simp only [show ¬ 0 ∈ opaqueChild.outputNames from by decide +kernel]
  rw [capture]
  rfl

theorem no_children : GeneralNominalVersionedFrame231.children packet = [] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show opaqueChild.requirements = [] from rfl)]
  rfl

theorem emitted_empty : emittedSchema plan = ⟨[],false⟩ := by
  unfold emittedSchema GeneralNominalVersionedPlans231.emittedRequests
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show opaqueChild.requirements = [] from rfl)]
  rfl

theorem head_schema : plan.headSchema = ⟨[⟨0,.source 0,.actual⟩],[],false⟩ := by
  unfold Plan.headSchema
  rw [show GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = _ from query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,center,child,childAt,roles,
    GeneralDeclarationExamples.bareRole,List.ofFn_succ]

theorem ordinary (m : Assignment) : Ordinary packet m := by
  refine ⟨?_,?_,?_⟩
  · rw [bindings_exact]
    intro a one b two _
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact subtype_refl _
  · unfold GeneralNominalVersionedAllocation231.merges
    rw [bindings_exact]
    intro a member; cases member
  · rw [report_exact]
    intro a seen
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with rfl|rfl <;> exact subtype_refl _

theorem holds (m : Assignment) (valid : Models (after true) m) : Holds plan m := by
  refine ⟨valid.1.1,⟨ordinary m,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [report_exact]
    simp [ProjectionModels]
  · intro i
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro name used
    have eq : name = 0 := by
      rcases used with inHead|⟨_,member,_⟩
      · simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
          GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
          GeneralDeclarationPatterns.Pattern.variables] using inHead
      · cases member
    subst name
    change GeneralNominalCaptureMerges.Fits m ((GeneralNominalVersionedFrame231.capture packet).inputs 0)
      (m (GeneralNominalVersionedFrame231.binder plan 0)).1
    rw [binder,capture]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    refine ⟨(by intro _ impossible; cases impossible),?_⟩
    intro entry member
    cases List.mem_singleton.mp member
    simp only [ite_true,binder]
    exact GeneralNominalOriginTerms.source_self m 0
  · rw [emitted_empty]
    intro _ h; cases h
  · intro _ h; cases h
  · unfold Outputs
    rw [emitted_empty]
    intro _ h; cases h

theorem fresh :
    GeneralNominalVersionedAllocation231.Fresh (current true).state (registry true)
      (child true).identity packet.bindings := by
  intro key member
  have each : (GeneralNominalVersionedAllocation231.keys (registry true) (child true).identity packet.bindings).all
      (fun k => decide (GeneralNominalIdentities.source (current true).state.seed k ∈
        GeneralNominalState.sources (current true).state → k ∈ (current true).state.allocated)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp each key member)

theorem prepared : Prepared (registry true) (current true) (child true) opaqueChild := by
  refine ⟨⟨rfl,by intro _ _ impossible; cases impossible⟩,?_,_,current_args true, fresh,?_,model Common.rowEmpty,?_⟩
  · refine ⟨?_,by intro _ member; cases member⟩
    intro i
    change 0 ∈ GeneralNominalState.sources (current true).state ∧ 0 ∈ GeneralNominalState.sources (current true).state
    exact ⟨by decide +kernel,by decide +kernel⟩
  · rw [show GeneralNominalRecursiveCandidates.report _ _ _ = GeneralNominalPacketSupport.report packet from rfl,report_exact]
    exact ⟨rfl,rfl,rfl⟩
  · change GeneralNominalVersionedCandidates231.HeadModels packet.registry packet.context packet.site.occurrence packet.declaration packet.bounds (model Common.rowEmpty)
    exact (GeneralNominalVersionedCandidates231.headModels_packet_iff packet (model Common.rowEmpty)).mpr
      (GeneralNominalVersionedPlans231.head_models (plan := plan) (holds _ (after_model true Common.rowEmpty)))

theorem child_frame : Frame (registry true) (after true).core (child true) 1 plan :=
  ⟨rfl,rfl,rfl,rfl,raw_child true,center_child true,List.mem_cons_of_mem _ List.mem_cons_self,
    rfl,current_args true,prepared⟩

theorem requests_empty : GeneralNominalCenteredHeadOutputs.requests (after true).core (child true) = [] := by
  rw [← GeneralRebaseExecutableRequests262.requests_eq]
  decide +kernel

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready (after true).core (child true) plan := by
  intro out member
  rw [requests_empty] at member
  cases member

theorem class_effects (m : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects (after true).core (child true) plan m := by
  constructor <;> intro out present <;> rw [requests_empty] at present <;> cases present

theorem evidence (m : Assignment) (valid : Models (after true) m) :
    Evidence (registry true) (after true).core m (child true) (.node 1 []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf
    ⟨plan,GeneralNominalVersionedEvidence231.certificate_of_semantics child_frame no_children.symm
      (holds m valid) ready (class_effects m)⟩

theorem already_committed : GeneralNominalVersionedMixedKernel234.Committed (after true) plan := by
  refine ⟨fun m h => ⟨holds m h,class_effects m⟩,?_⟩
  intro o h
  rw [no_children] at h
  cases h

end Yulang.GeneralRebaseRowWholeChild287
