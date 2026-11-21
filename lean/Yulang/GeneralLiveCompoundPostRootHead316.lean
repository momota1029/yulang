import Yulang.GeneralLiveCompoundPostFrames316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 40000000
namespace Yulang.GeneralLiveCompoundPostRootHead316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry declaration declaration_checked leaf source)
open GeneralLiveCompoundChildSite316 (child childSite signature)
open GeneralLiveCompoundPost316 (raw cur raw_sites_after centers_after)
open GeneralLiveCompoundPostFrames316 (rootPlan leafPlan)
open GeneralLiveCompoundLeafInstall316 (after after_model)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundCurrentRoot316 (plan packet located report_exact bindings_exact)
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedCandidates231 (Prepared Survivor Unique inputs)
open GeneralNominalVersionedInstallation231 (reserved atoms allocated)
open GeneralNominalVersionedTransport231 (extendedPacket extendedPlan)
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)

noncomputable abbrev adds := GeneralLiveCompoundLeafHead316.packet
open GeneralLiveCompoundUpperSnapshot316 (snap context)
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalReportErasure (erase Data)
abbrev slot0 : Fin 8 := 0
noncomputable abbrev oldPlan := GeneralMixedCompoundUpperRoot307.plan

theorem report_codes :
    erase snap (report context declaration [(slot0,slot0)]) =
    erase GeneralMixedCompoundUpperSnapshot307.snap
      (report GeneralMixedCompoundUpperSnapshot307.context GeneralDictionaryCompoundSource238.declaration [(slot0,slot0)]) := by
  rw [report_exact,GeneralMixedCompoundUpperRoot307.report_exact]
  rfl

theorem ordinary_pre : Ordinary packet w := by
  have old := ((GeneralNominalVersionedPlans231.private_models_iff ..).mp
    GeneralVersionedEndpointObstructionHead315.head.1).2
  unfold Ordinary at old ⊢
  rw [bindings_exact]
  rw [GeneralMixedCompoundUpperRoot307.bindings_exact] at old
  refine ⟨old.1,old.2.1,?_⟩
  change PresenceNormalForm.All _ w (GeneralNominalRecursiveInspection.selfChecks snap
    (report context declaration [(slot0,slot0)]))
  rw [← GeneralNominalReportErasure.checks_exact,report_codes,GeneralNominalReportErasure.checks_exact]
  exact old.2.2

theorem projection_pre : GeneralNominalRecursiveInspection.ProjectionModels packet.context.state
    (GeneralNominalPacketSupport.report packet) w := by
  have old := GeneralVersionedEndpointObstructionHead315.head.2
  change GeneralNominalRecursiveInspection.ProjectionModels snap (report context declaration [(slot0,slot0)]) w
  rw [← GeneralNominalReportErasure.projections_exact,report_codes,GeneralNominalReportErasure.projections_exact]
  exact old

theorem head : HeadModels rootPlan.packet w := by
  refine ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr ⟨after_model.1.1,?_⟩,?_⟩
  · exact (GeneralNominalVersionedTransport231.ordinary_iff (reserved adds) (atoms adds) (allocated adds) packet w).mpr ordinary_pre
  · exact (GeneralNominalVersionedTransport231.projection_iff (reserved adds) (atoms adds) (allocated adds)
      packet w).mpr projection_pre

theorem fresh : GeneralNominalVersionedAllocation231.Fresh raw registry root.identity rootPlan.packet.bindings := by
  rw [show rootPlan.packet.bindings = [(0,2,2),(0,2,2)] from
    (GeneralNominalVersionedTransport231.packet_bindings (reserved adds) (atoms adds) (allocated adds) packet).trans bindings_exact]
  have each : ∀ key ∈ GeneralNominalVersionedAllocation231.keys registry root.identity [(0,2,2),(0,2,2)],
      GeneralNominalIdentities.source raw.seed key ∉ GeneralNominalState.sources raw ∨ key ∈ raw.allocated := by
    decide +kernel
  intro key member actual
  exact (each key member).resolve_left (fun missing => missing actual)

theorem prepared : Prepared registry cur root declaration := by
  refine ⟨source.metadata,⟨?_,by intro out absent; cases absent⟩,
    [(slot0,slot0)],located,?_,?_,w,(GeneralNominalVersionedCandidates231.headModels_packet_iff rootPlan.packet w).mpr head⟩
  · intro index
    constructor <;> exact GeneralNominalAllocationSupport.slot_source raw (0 : Fin 8)
  · change GeneralNominalVersionedAllocation231.Fresh raw registry root.identity rootPlan.packet.bindings
    exact fresh
  · exact (GeneralNominalVersionedPreparedTransport231.finished_iff (reserved adds) (atoms adds) (allocated adds)
      packet.context declaration [(slot0,slot0)]).mpr (by rw [report_exact]; exact ⟨rfl,rfl,rfl⟩)

theorem frame : Frame registry after.core root declaration.id rootPlan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,List.mem_cons_self,rfl,located,prepared⟩
  · rw [raw_sites_after]; exact List.mem_cons_self
  · rw [centers_after]; exact List.mem_cons_self

theorem known : ¬ GeneralNominalState.RootPending raw (inputs root).demand :=
  GeneralVersionedEndpointObstructionHead315.known

theorem child_site (sig : GeneralLiveCompoundRegistry316.otherChild.Signature roles) :
    GeneralNominalVersionedFrame231.childSite plan GeneralLiveCompoundRegistry316.otherChild sig =
      GeneralNominalVersionedFrame231.childSite GeneralLiveCompoundRoot316.plan GeneralLiveCompoundRegistry316.otherChild sig := by
  unfold GeneralNominalVersionedFrame231.childSite GeneralNominalVersionedFrame231.clauseChild
    GeneralDictionaryEmissionPlans.occurrence GeneralDeclarationDemands.emit
    GeneralDeclarationDemands.childDemand GeneralNominalVersionedFrame231.frame
    GeneralNominalVersionedFrame231.emittedCenter
  dsimp only
  congr 1
  congr 1
  congr 1
  all_goals
    funext index
    have same : index = 0 := Fin.ext (by have h := index.isLt; change index.val < 1 at h; omega)
    subst index
    rfl

theorem children_pre :
    GeneralNominalVersionedFrame231.children packet = [childSite.occurrence] := by
  have exactList : GeneralNominalVersionedFrame231.children packet =
      [(GeneralNominalVersionedFrame231.childSite plan GeneralLiveCompoundRegistry316.otherChild signature).occurrence] := by
    unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
      GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
    rfl
  rw [child_site] at exactList
  exact exactList

theorem root_children : GeneralNominalVersionedFrame231.children rootPlan.packet = [child] := by
  have exactChildren := GeneralNominalVersionedTransport231.children_eq (reserved adds) (atoms adds) (allocated adds) packet
  change GeneralNominalVersionedFrame231.children rootPlan.packet =
    GeneralNominalVersionedFrame231.children packet at exactChildren
  exact exactChildren.trans children_pre

theorem chosen : Survivor registry cur root declaration.id [child] :=
  ⟨known,declaration,List.mem_cons_self,declaration_checked,rfl,rfl,[(slot0,slot0)],located,prepared,root_children.symm⟩

theorem unique : Unique registry cur root declaration.id [child] := by
  refine ⟨chosen,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,idEq,role,_,_,_,_⟩ := copy
  rcases List.mem_cons.mp visible with one|last
  · subst d; subst key
    exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional GeneralLiveCompoundRegistry316.checked other chosen⟩
  · cases List.mem_singleton.mp last; cases role

theorem capture_eval : GeneralNominalVersionedFrame231.capture packet =
    GeneralNominalVersionedFrame231.capture GeneralMixedCompoundUpperRoot307.packet := by
  unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
  change GeneralNominalVersionedAllocation231.capture snap registry root.identity declaration.id packet.bindings =
    GeneralNominalVersionedAllocation231.capture GeneralMixedCompoundUpperSnapshot307.snap
      GeneralDictionaryCompoundSource238.registry root.identity GeneralDictionaryCompoundSource238.declaration.id
      GeneralMixedCompoundUpperRoot307.packet.bindings
  rw [bindings_exact,GeneralMixedCompoundUpperRoot307.bindings_exact]
  rfl

theorem binder_eval (name : Nat) : GeneralNominalVersionedFrame231.binder plan name =
    GeneralNominalVersionedFrame231.binder oldPlan name := by
  unfold GeneralNominalVersionedFrame231.binder
  rw [show GeneralNominalVersionedFrame231.capture plan.packet =
    GeneralNominalVersionedFrame231.capture oldPlan.packet from capture_eval]
  rfl

theorem schema_pre : SchemaHolds plan plan.headSchema w := by
  have schemaEq : plan.headSchema = oldPlan.headSchema := by
    unfold Plan.headSchema
    change GeneralNominalMaterialization.schemas
      (GeneralNominalInspection.queries snap context.interpretation declaration) _ _ _ =
      GeneralNominalMaterialization.schemas
        (GeneralNominalInspection.queries GeneralMixedCompoundUpperSnapshot307.snap
          GeneralMixedCompoundUpperSnapshot307.context.interpretation GeneralDictionaryCompoundSource238.declaration) _ _ _
    rw [GeneralLiveCompoundCurrentRoot316.query,GeneralMixedCompoundUpperRoot307.query]
  rw [schemaEq]
  unfold SchemaHolds
  simp only [binder_eval]
  change (_ ∧ ∀ entry ∈ oldPlan.headSchema.variables,
    if entry.mode = .actual then _ else (∃ actual,
      GeneralNominalRecursiveInspection.Observes w entry.origin actual) ∧
      ∀ actual, GeneralNominalRecursiveInspection.Observes w entry.origin actual →
        GeneralNominalMaterialization.VariableHolds declaration (GeneralNominalVersionedFrame231.capture packet)
          w entry.name entry.mode actual)
  rw [capture_eval]
  exact GeneralVersionedEndpointObstructionHead315.schema

theorem schema : SchemaHolds rootPlan rootPlan.headSchema w := by
  change SchemaHolds (extendedPlan (reserved adds) (atoms adds) (allocated adds) plan) _ w
  rw [GeneralNominalVersionedTransport231.headSchema_eq]
  apply (GeneralNominalVersionedTransport231.schemaHolds_iff (reserved adds) (atoms adds) (allocated adds)
    plan plan.headSchema w).mpr
  exact schema_pre

theorem head_equations : HeadEquations rootPlan w := by
  refine ⟨after_model.1.2.2.2.1 rootPlan.input frame.center_recorded,?_,schema⟩
  intro name named
  exact GeneralNominalVersionedCurrentHead237.capture_fits rootPlan frame after_model head schema name (.inl named)

end Yulang.GeneralLiveCompoundPostRootHead316
