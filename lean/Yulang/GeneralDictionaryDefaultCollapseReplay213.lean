import Yulang.GeneralDictionaryDefaultCollapseBinders213

namespace Yulang.GeneralDictionaryDefaultCollapseReplay213
open GeneralDeclarations GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseAllocation
open GeneralDictionarySemanticCollapseBranch GeneralDictionarySemanticCollapseSchema
open GeneralDictionaryDefaultNonpointTerminal210
open GeneralNominalAllocation GeneralNominalCenteredHeadMatStepPackets
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : GeneralNominalReobservationSteps.Revision state}

 theorem replay (s : Shape revision) (registry : Registry) (site : GeneralNominalDemandMerging.Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (center : Site roles) (same : center.occurrence = site.occurrence)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : Holds (oldPlan s registry site declaration checked center same) model)
    (current : GeneralNominalState.Models revision.snapshot model) :
    Holds (newPlan s registry site declaration checked center same) model := by
  let first := oldPlan s registry site declaration checked center same
  let last := newPlan s registry site declaration checked center same
  have rs := reports s declaration queries
  have before : first.packet.bindings = [(s.binder,firstPair s),(s.binder,lastPair s)] := by
    change bindings state.context.state (GeneralNominalRecursiveCandidates.report state.context declaration [(s.root,s.root)]) = _
    rw [rs.1]
    rfl
  have after : last.packet.bindings = [(s.binder,firstPair s)] := by
    change bindings revision.snapshot (GeneralNominalRecursiveCandidates.report (currentContext revision) declaration [(s.root,s.root)]) = _
    rw [rs.2]
    rfl
  have binders := GeneralDictionaryDefaultCollapseBinders213.binders s registry site declaration checked center same
    queries names terminal model old
  have privateOld := private_models old
  have privateNew := GeneralDictionaryNonpointCollapse.private_state s registry site.occurrence declaration
    queries names model privateOld current
  have ordinary : GeneralNominalPacketSupport.Ordinary last.packet model :=
    ((GeneralNominalPacketSupport.private_exact last.packet model).mp privateNew).2
  have projection : ProjectionModels state.context.state
      (inspect state.context.state (query s) (s.root,s.root) none) model := by
    rw [before_exact]
    have p := old.2.1.2.1
    change ProjectionModels state.context.state
      (GeneralNominalRecursiveCandidates.report state.context declaration [(s.root,s.root)]) model at p
    rw [rs.1] at p
    exact p
  have prop := (GeneralNominalState.extend_models ..).mp privateOld |>.1
  change GeneralNominalState.Models (propagate state.context.state registry site.occurrence.identity declaration
    (bindings state.context.state (GeneralNominalRecursiveCandidates.report state.context declaration [(s.root,s.root)]))) model at prop
  rw [rs.1] at prop
  have propagated : GeneralNominalState.Models (propagate state.context.state registry site.occurrence.identity declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model := by
    rw [before_exact]
    exact prop
  apply GeneralDictionaryDefaultSemanticTerminal213.terminal_replay (first := first) (last := last) rfl rfl rfl rfl rfl rfl
    binders terminal old current ordinary
  · change ProjectionModels revision.snapshot
      (GeneralNominalRecursiveCandidates.report (currentContext revision) declaration [(s.root,s.root)]) model
    rw [rs.2]
    have result := current_projection s model current projection
    rw [after_exact] at result
    exact result
  · intro name needed
    have nameEq : name = s.binder := by
      rcases needed with declared | ⟨clause,member,_⟩
      · change name ∈ declaration.inputNames at declared
        rw [names] at declared
        exact List.mem_singleton.mp declared
      · change clause ∈ declaration.requirements at member
        rw [terminal] at member
        cases member
    subst name
    have oldFits := shared_center old.2.1 (Or.inl (by change s.binder ∈ declaration.inputNames; simp [names]))
    change GeneralNominalCaptureMerges.Fits model
      (capture state.context.state registry site.occurrence.identity declaration.id first.packet.bindings |>.inputs s.binder)
      (model (first.binder s.binder)).1 at oldFits
    rw [before] at oldFits
    change GeneralNominalCaptureMerges.Fits model
      (capture revision.snapshot registry site.occurrence.identity declaration.id last.packet.bindings |>.inputs s.binder) _
    rw [after]
    have result := GeneralDictionaryNonpointCollapse.capture_fits s registry site.occurrence.identity declaration model
      (by simp [names]) propagated (model (first.binder s.binder)).1
    unfold oldCapture newCapture at result
    rw [bindings_before,bindings_after] at result
    have fit := result oldFits
    have equal := binders s.binder
    exact ⟨CommonNominalFullCarrier.subtype_trans fit.1 equal.1,
      CommonNominalFullCarrier.subtype_trans equal.2 fit.2⟩
end Yulang.GeneralDictionaryDefaultCollapseReplay213
