import Yulang.GeneralDictionaryDefaultNonpointCertificate210
import Yulang.GeneralNominalCenteredHeadMatStepRefresh

set_option backward.isDefEq.respectTransparency false

/-! Destination Frame construction for the actual nested nominal revision.
Metadata, registration, linkage and allocation freshness are preserved by the
revision; current raw head semantics follows from the replayed total packet. -/
namespace Yulang.GeneralDictionaryDefaultNominalFrame210
open GeneralDeclarations GeneralNominalCenters GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
open GeneralDictionaryDefaultNonpointTerminal210
variable {roles : Roles.RoleDecls} {state : State roles}
variable {revision : GeneralNominalReobservationSteps.Revision state.core.erased.current}

 theorem frame (s : Shape revision) (registry : Registry) (site : GeneralNominalDemandMerging.Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (center : Site roles) (same : center.occurrence = site.occurrence)
    (queries : GeneralNominalInspection.queries state.core.erased.current.context.state
      state.core.erased.current.context.interpretation declaration = [query s])
    (old : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key
      (oldPlan s registry site declaration checked center same))
    (model : GeneralNominalCommonBridge.Assignment)
    (held : GeneralNominalCenteredHeadMatStepPackets.Holds
      (newPlan s registry site declaration checked center same) model) :
    GeneralNominalCenteredHeadOutputs.Frame registry (change state revision.result).core focus key
      (newPlan s registry site declaration checked center same) := by
  have rs := reports s declaration queries
  obtain ⟨metadata,linked,fresh,oldBounds,located,finished,head⟩ := old.prepared
  have boundsEq : oldBounds = [(s.root,s.root)] := Option.some.inj (located.symm.trans old.located)
  subst oldBounds
  refine ⟨old.registry_eq,rfl,old.occurrence_eq,old.key_eq,old.raw_recorded,old.center_recorded,
    old.visible,old.role_eq,old.located,metadata,linked,fresh,[(s.root,s.root)],old.located,?_,model,?_⟩
  · change GeneralNominalRecursiveInspection.Finished
      (GeneralNominalRecursiveCandidates.report (currentContext revision) declaration [(s.root,s.root)])
    rw [rs.2]
    have done := (both_finished s).2
    rw [after_exact] at done
    exact done
  · have head := (GeneralNominalCenteredHeadMatStepPackets.models_iff.mpr held).1
    have occ : site.occurrence = focus := old.occurrence_eq
    change GeneralNominalCenteredHeadCandidates.HeadModels registry (currentContext revision) focus declaration [(s.root,s.root)] model
    simpa only [newPlan,occ] using head

 theorem certificate (s : Shape revision) (registry : Registry) (site : GeneralNominalDemandMerging.Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (center : Site roles) (same : center.occurrence = site.occurrence)
    (queries : GeneralNominalInspection.queries state.core.erased.current.context.state
      state.core.erased.current.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (nonpoint : (GeneralDictionarySemanticCollapseAllocation.firstPair s).1 ≠
      (GeneralDictionarySemanticCollapseAllocation.firstPair s).2)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : GeneralDictionaryTotalEvidence206.Certificate registry state.core model focus key children
      (oldPlan s registry site declaration checked center same))
    (current : GeneralNominalState.Models revision.snapshot model) :
    GeneralDictionaryTotalEvidence206.Certificate registry (change state revision.result).core model focus key children
      (newPlan s registry site declaration checked center same) := by
  have held := replay s registry site declaration checked center same queries names terminal nonpoint model old.packet current
  exact GeneralDictionaryDefaultNonpointCertificate210.certificate s registry site declaration checked center same
    queries names terminal nonpoint model old
    (frame s registry site declaration checked center same queries old.frame model held) current
end Yulang.GeneralDictionaryDefaultNominalFrame210
