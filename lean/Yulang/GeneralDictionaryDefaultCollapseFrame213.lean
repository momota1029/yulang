import Yulang.GeneralDictionaryDefaultCollapseCertificate213
import Yulang.GeneralDictionaryDefaultNominalFrame210

namespace Yulang.GeneralDictionaryDefaultCollapseFrame213
open GeneralDeclarations GeneralNominalCenters GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
open GeneralDictionaryDefaultNonpointTerminal210
variable {roles : Roles.RoleDecls} {state : State roles}
variable {revision : GeneralNominalReobservationSteps.Revision state.core.erased.current}

 theorem certificate (s : Shape revision) (registry : Registry) (site : GeneralNominalDemandMerging.Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (center : Site roles) (same : center.occurrence = site.occurrence)
    (queries : GeneralNominalInspection.queries state.core.erased.current.context.state
      state.core.erased.current.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : GeneralDictionaryTotalEvidence206.Certificate registry state.core model focus key children
      (oldPlan s registry site declaration checked center same))
    (current : GeneralNominalState.Models revision.snapshot model) :
    GeneralDictionaryTotalEvidence206.Certificate registry (change state revision.result).core model focus key children
      (newPlan s registry site declaration checked center same) := by
  have held := GeneralDictionaryDefaultCollapseReplay213.replay s registry site declaration checked center same queries names terminal model old.packet current
  exact GeneralDictionaryDefaultCollapseCertificate213.certificate s registry site declaration checked center same
    queries names terminal model old
    (GeneralDictionaryDefaultNominalFrame210.frame s registry site declaration checked center same queries old.frame model held) current
 theorem certified_leaf (s : Shape revision) (registry : Registry) (site : GeneralNominalDemandMerging.Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (center : Site roles) (same : center.occurrence = site.occurrence)
    (queries : GeneralNominalInspection.queries state.core.erased.current.context.state
      state.core.erased.current.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : GeneralDictionaryTotalEvidence206.Certificate registry state.core model focus key []
      (oldPlan s registry site declaration checked center same))
    (valid : Models (change state revision.result) model) :
    GeneralDictionaryTotalEvidence206.Evidence registry (change state revision.result).core
      model focus (.node key []) :=
  GeneralDictionaryTotalEvidence206.evidence_leaf
    ⟨_,certificate s registry site declaration checked center same queries names terminal model old valid.1⟩

 theorem certified_leaf_from_before (s : Shape revision) (registry : Registry) (site : GeneralNominalDemandMerging.Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (center : Site roles) (same : center.occurrence = site.occurrence)
    (queries : GeneralNominalInspection.queries state.core.erased.current.context.state
      state.core.erased.current.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : GeneralDictionaryTotalEvidence206.Certificate registry state.core model focus key []
      (oldPlan s registry site declaration checked center same))
    (revisionValid : GeneralNominalCenteredHeadMatStepRefresh.Reobserve state revision)
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Evidence registry (change state revision.result).core
      model focus (.node key []) :=
  certified_leaf s registry site declaration checked center same queries names terminal model old
    ((GeneralNominalCenteredHeadMatStepRefresh.reobserve_models revisionValid).mpr valid)

end Yulang.GeneralDictionaryDefaultCollapseFrame213
