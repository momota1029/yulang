import Yulang.GeneralWhereVersionRecompile317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 49000000
namespace Yulang.GeneralWhereVersionRootHead317
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry declaration declaration_checked leaf checked)
open GeneralWhereVersionSnapshot317 (snap context zero)
open GeneralWhereVersionBase317 (source source_old)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralWhereVersionCommit317 (core framedState new_snapshot)
open GeneralWhereVersionRootReport317 (packet plan location query exact_report same)
open GeneralWhereVersionLeafRegistry317 (descriptors sites)
open GeneralWhereVersionLeafFresh317 (finite_sources)
open GeneralWhereVersionCase317 (lower upper expr)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundPost316 (raw)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Prepared Survivor Unique inputs)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)
open GeneralNominalCommonBridge (Assignment)

theorem binding : packet.bindings = [(0,2,2),(0,2,2)] := by
  rw [← GeneralNominalCenteredHeadMatPlanData.bindings same]
  exact (GeneralNominalVersionedTransport231.packet_bindings _ _ _ GeneralLiveCompoundCurrentRoot316.packet).trans
    GeneralLiveCompoundCurrentRoot316.bindings_exact

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snap registry root.identity packet.bindings := by
  intro k member collision
  have tag : k.2.2.1 ≤ 6 := by
    apply GeneralVersionedInstallDomain313.reserve_purpose packet
    exact List.mem_map.mpr ⟨k,member,rfl⟩
  rcases finite_sources collision with past|new|new
  · apply GeneralLiveCompoundPostRootHead316.fresh k _ past
    rw [GeneralNominalCenteredHeadMatPlanData.bindings same]
    exact member
  · exact False.elim (GeneralVersionedHighOrigins315.distinct
      (b := GeneralVersionedEndpointAddress315.key rootPlan .lower otherChild.id 0 expr)
      (by change k.2.2.1 ≠ 10; omega) snap.seed new)
  · exact False.elim (GeneralVersionedHighOrigins315.distinct
      (b := GeneralVersionedEndpointAddress315.key rootPlan .upper otherChild.id 0 expr)
      (by change k.2.2.1 ≠ 11; omega) snap.seed new)

theorem model_head (m : Assignment) (valid : ParentHolds m) : HeadModels packet m := by
  have old := valid.2.1
  exact ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr
    ⟨new_snapshot m valid,(GeneralDeferredLadderTransport302.ordinary_iff same m).mp
      ((GeneralNominalVersionedPlans231.private_models_iff ..).mp old.1).2⟩,
    (GeneralNominalCenteredHeadMatPlanData.projections same m).mp old.2⟩

theorem schema_hold (m : Assignment) (valid : ParentHolds m) : SchemaHolds plan plan.headSchema m := by
  have old := valid.2.2.1
  rw [GeneralNominalCenteredHeadMatPlanData.head_schema same] at old
  unfold SchemaHolds at old ⊢
  simp only [GeneralDeferredLadderTransport302.binder_eq same,
    GeneralDeferredLadderTransport302.capture_eq same,same.declaration] at old
  exact old

theorem prepared (m : Assignment) (valid : ParentHolds m) : Prepared registry context root declaration := by
  refine ⟨GeneralLiveCompoundRegistry316.source.metadata,⟨?_,by intro output bad; cases bad⟩,
    [(zero,zero)],location,fresh,?_,m,
    (GeneralNominalVersionedCandidates231.headModels_packet_iff packet m).mpr (model_head m valid)⟩
  · intro idx
    have eq : source zero = 0 := by rw [source_old]; rfl
    change (0 : Nat) ∈ GeneralNominalState.sources snap ∧ 0 ∈ GeneralNominalState.sources snap
    exact ⟨eq ▸ GeneralNominalAllocationSupport.slot_source snap zero,
      eq ▸ GeneralNominalAllocationSupport.slot_source snap zero⟩
  · rw [exact_report]
    exact ⟨rfl,rfl,rfl⟩

theorem frame (m : Assignment) (valid : ParentHolds m) :
    Frame registry core root declaration.id plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,List.mem_cons_self,rfl,location,prepared m valid⟩
  · rw [descriptors]; exact List.mem_cons_self
  · rw [sites]; exact List.mem_cons_self

theorem known : ¬ GeneralNominalState.RootPending snap (inputs root).demand := by
  rintro ⟨i,no⟩
  exact no ⟨zero,(by change source zero = 0; rw [source_old]; rfl),Or.inr ⟨_,rfl⟩⟩

theorem legacy_children :
    GeneralNominalVersionedFrame231.children packet = [GeneralLiveCompoundChildSite316.child] :=
  (GeneralDeferredLadderTransport302.children_eq same).symm.trans GeneralLiveCompoundPostRootHead316.root_children

theorem survivor (m : Assignment) (valid : ParentHolds m) :
    Survivor registry context root declaration.id [GeneralLiveCompoundChildSite316.child] :=
  ⟨known,declaration,List.mem_cons_self,declaration_checked,rfl,rfl,[(zero,zero)],location,prepared m valid,legacy_children.symm⟩

theorem unique (m : Assignment) (valid : ParentHolds m) :
    Unique registry context root declaration.id [GeneralLiveCompoundChildSite316.child] := by
  refine ⟨survivor m valid,?_⟩
  intro k kids candidate
  have copy := candidate
  obtain ⟨_,d,seen,_,eq,role,_,_,_,_⟩ := copy
  rcases List.mem_cons.mp seen with first|last
  · subst d; subst k
    exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked candidate (survivor m valid)⟩
  · cases List.mem_singleton.mp last; cases role

end Yulang.GeneralWhereVersionRootHead317
