import Yulang.GeneralDictionaryDefaultCollapseReplay213
import Yulang.GeneralDictionaryTotalEvidence206
import Yulang.GeneralDictionaryCenteredScalarDiscovery177

/-! Exact certificate replay across both point and nonpoint retained captures.
No source-ID equality is required for the actual binder. -/
namespace Yulang.GeneralDictionaryDefaultCollapseCertificate213
open GeneralDeclarations GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseAllocation
open GeneralDictionarySemanticCollapseBranch GeneralDictionaryDefaultNonpointTerminal210
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : GeneralNominalReobservationSteps.Revision state}

 theorem certificate (s : Shape revision) (registry : Registry) (site : GeneralNominalDemandMerging.Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (center : Site roles) (same : center.occurrence = site.occurrence)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : GeneralDictionaryTotalEvidence206.Certificate registry oldState model focus key children
      (oldPlan s registry site declaration checked center same))
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry newState focus key
      (newPlan s registry site declaration checked center same))
    (current : GeneralNominalState.Models revision.snapshot model) :
    GeneralDictionaryTotalEvidence206.Certificate registry newState model focus key children
      (newPlan s registry site declaration checked center same) := by
  let first := oldPlan s registry site declaration checked center same
  let last := newPlan s registry site declaration checked center same
  have rs := reports s declaration queries
  have before : first.packet.bindings = [(s.binder,firstPair s),(s.binder,lastPair s)] := by
    change bindings state.context.state (GeneralNominalRecursiveCandidates.report state.context declaration [(s.root,s.root)]) = _
    rw [rs.1]; rfl
  have after : last.packet.bindings = [(s.binder,firstPair s)] := by
    change bindings revision.snapshot (GeneralNominalRecursiveCandidates.report (currentContext revision) declaration [(s.root,s.root)]) = _
    rw [rs.2]; rfl
  have oldChildren : first.packet.children = [] :=
    GeneralDictionaryLinearLeaf.children_empty _ _ _ _ _ terminal _
  have newChildren : last.packet.children = [] :=
    GeneralDictionaryLinearLeaf.children_empty _ _ _ _ _ terminal _
  refine ⟨frame,old.children_eq.trans (oldChildren.trans newChildren.symm),
    GeneralDictionaryDefaultCollapseReplay213.replay s registry site declaration checked center same queries names terminal model old.packet current,?_⟩
  intro output member
  obtain ⟨body,supplied,compiled,held⟩ := old.outputs output member
  refine ⟨body,supplied,compiled,?_⟩
  exact (GeneralDictionaryDefaultBodyTransport209.body_transport (first := first) (last := last)
    rfl rfl
    (GeneralDictionaryDefaultCollapseBinders213.binders s registry site declaration checked center same
      queries names terminal model old.packet)
    (fun _ => GeneralDictionaryDefaultExpression209.equivalent_refl _)).mp held


 theorem leaf_evidence (s : Shape revision) (registry : Registry) (site : GeneralNominalDemandMerging.Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (center : Site roles) (same : center.occurrence = site.occurrence)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : GeneralDictionaryTotalEvidence206.Certificate registry oldState model focus key []
      (oldPlan s registry site declaration checked center same))
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry newState focus key
      (newPlan s registry site declaration checked center same))
    (current : GeneralNominalState.Models revision.snapshot model) :
    GeneralDictionaryTotalEvidence206.Evidence registry newState model focus (.node key []) :=
  GeneralDictionaryTotalEvidence206.evidence_leaf ⟨_,certificate s registry site declaration checked center same
    queries names terminal model old frame current⟩
end Yulang.GeneralDictionaryDefaultCollapseCertificate213
