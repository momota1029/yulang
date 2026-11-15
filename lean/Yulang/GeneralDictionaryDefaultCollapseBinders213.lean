import Yulang.GeneralDictionaryDefaultSemanticTerminal213
import Yulang.GeneralDictionaryDefaultNonpointTerminal210

namespace Yulang.GeneralDictionaryDefaultCollapseBinders213
open GeneralDeclarations GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseAllocation
open GeneralDictionarySemanticCollapseBranch GeneralDictionarySemanticCollapseSchema
open GeneralDictionaryDefaultNonpointTerminal210
open GeneralNominalAllocation GeneralNominalCenteredHeadMatStepPackets
open CommonNominalFullCarrier GeneralDictionaryDefaultExpression209
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : GeneralNominalReobservationSteps.Revision state}

 theorem binders (s : Shape revision) (registry : Registry) (site : GeneralNominalDemandMerging.Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (center : Site roles) (same : center.occurrence = site.occurrence)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : Holds (oldPlan s registry site declaration checked center same) model) :
    ∀ name, Equivalent
      (model ((oldPlan s registry site declaration checked center same).binder name)).1
      (model ((newPlan s registry site declaration checked center same).binder name)).1 := by
  let first := oldPlan s registry site declaration checked center same
  let last := newPlan s registry site declaration checked center same
  have rs := reports s declaration queries
  have before : first.packet.bindings = [(s.binder,firstPair s),(s.binder,lastPair s)] := by
    change bindings state.context.state (GeneralNominalRecursiveCandidates.report state.context declaration [(s.root,s.root)]) = _
    rw [rs.1]; rfl
  have after : last.packet.bindings = [(s.binder,firstPair s)] := by
    change bindings revision.snapshot (GeneralNominalRecursiveCandidates.report (currentContext revision) declaration [(s.root,s.root)]) = _
    rw [rs.2]; rfl
  intro name
  by_cases nonpoint : (firstPair s).1 ≠ (firstPair s).2
  · have equal := GeneralDictionaryDefaultBinderShape210.names (first := first) (last := last)
      rfl rfl rfl (fun n _ => GeneralDictionaryDefaultNonpointCollapse210.shape before after nonpoint n) name
    change Equivalent (model (first.binder name)).1 (model (last.binder name)).1
    rw [equal]; exact equivalent_refl _
  · have point : (firstPair s).1 = (firstPair s).2 := Classical.not_not.mp nonpoint
    have outputs : declaration.outputNames = [] :=
      GeneralDictionaryDefaultTerminalReduction212.no_output_names (plan := first) terminal
    by_cases named : name = s.binder
    · subst name
      have privateOld := private_models old
      have prop := (GeneralNominalState.extend_models ..).mp privateOld |>.1
      change GeneralNominalState.Models (propagate state.context.state registry site.occurrence.identity declaration
        (bindings state.context.state (GeneralNominalRecursiveCandidates.report state.context declaration [(s.root,s.root)]))) model at prop
      rw [rs.1] at prop
      have propagated : GeneralNominalState.Models (propagate state.context.state registry site.occurrence.identity declaration
          (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model := by
        rw [before_exact]; exact prop
      have oldFits := shared_center old.2.1 (Or.inl (by change s.binder ∈ declaration.inputNames; simp [names]))
      have oldFits' : GeneralNominalCaptureMerges.Fits model
          ((oldCapture s registry site.occurrence.identity declaration).inputs s.binder)
          (model (first.binder s.binder)).1 := by
        unfold oldCapture
        rw [bindings_before]
        change GeneralNominalCaptureMerges.Fits model
          ((capture state.context.state registry site.occurrence.identity declaration.id first.packet.bindings).inputs s.binder) _ at oldFits
        rw [before] at oldFits
        exact oldFits
      have retained := GeneralDictionaryNonpointCollapse.capture_fits s registry site.occurrence.identity declaration model
        (by simp [names]) propagated (model (first.binder s.binder)).1 oldFits'
      unfold newCapture at retained
      rw [bindings_after] at retained
      change GeneralNominalCaptureMerges.Fits model
        ((capture revision.snapshot registry site.occurrence.identity declaration.id [(s.binder,firstPair s)]).inputs s.binder) _ at retained
      simp only [capture,occurrences,beq_self_eq_true,List.filter_cons_of_pos,List.filter_nil,
        List.map_cons,List.map_nil] at retained
      have retained' : Subtype (model (firstPair s).1).1 (model (first.binder s.binder)).1 ∧
        Subtype (model (first.binder s.binder)).1 (model (firstPair s).2).1 := retained
      have newBinder : last.binder s.binder = (firstPair s).1 := by
        unfold Plan.binder
        change (if s.binder ∈ declaration.outputNames then _ else _) = _
        simp only [outputs,List.not_mem_nil,ite_false]
        unfold GeneralNominalPacketSupport.capture
        rw [after]
        simp only [capture,occurrences,beq_self_eq_true,List.filter_cons_of_pos,List.filter_nil, List.map_cons,List.map_nil]
        exact ite_eq_left point
      change Equivalent (model (first.binder s.binder)).1 (model (last.binder s.binder)).1
      rw [newBinder]
      exact ⟨Eq.mp (congrArg (fun n => Subtype (model (first.binder s.binder)).1 (model n).1) point.symm) retained'.2,retained'.1⟩
    · have shape : GeneralDictionaryDefaultBinderShape210.InputShape first last name := by
        right
        constructor
        · unfold GeneralNominalPacketSupport.capture
          rw [before]
          exact GeneralDictionaryDefaultNonpointCollapse210.repeated_nonpoint _ _ _ _ s.binder name _ _
        · unfold GeneralNominalPacketSupport.capture
          rw [after]
          have different : s.binder ≠ name := Ne.symm named
          simpa [capture,occurrences,different] using
            GeneralDictionaryDefaultNonpointCollapse210.aggregate_nonpoint last.packet.context.state last.packet.registry last.packet.site.occurrence.identity last.packet.declaration.id name
      have equal := GeneralDictionaryDefaultBinderShape210.input_name (first := first) (last := last)
        rfl rfl rfl (by change name ∉ declaration.outputNames; simp [outputs]) shape
      change Equivalent (model (first.binder name)).1 (model (last.binder name)).1
      rw [equal]; exact equivalent_refl _
end Yulang.GeneralDictionaryDefaultCollapseBinders213
