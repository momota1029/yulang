import Yulang.GeneralDictionarySemanticCollapseBranch

/-! One-way semantic transport for nonpoint leaves in the existing depth-two
capture-collapse Shape. The old private constraints, not endpoint equivalence,
supply the retained self check. No general reobserve soundness is asserted. -/
namespace Yulang.GeneralDictionaryNonpointCollapse
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseAllocation
open GeneralDictionarySemanticCollapseBranch
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection
open GeneralNominalAllocation GeneralDeclarations GeneralNominalRecursiveCandidates
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

/-- Actual values fitting the old intersection fit its retained first occurrence.
Unlike endpoint equivalence, this direction needs no point-leaf hypothesis. -/
theorem capture_fits (s : Shape revision) (registry : Registry)
    (invocation : Nat) (declaration : Declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (declared : s.binder ∈ declaration.inputNames)
    (propagated : GeneralNominalState.Models (propagate state.context.state registry invocation declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model)
    (actual : CommonNominalFullCarrier.Ty)
    (valid : GeneralNominalCaptureMerges.Fits model
      ((GeneralDictionarySemanticCollapseSchema.oldCapture s registry invocation declaration).inputs s.binder) actual) :
    GeneralNominalCaptureMerges.Fits model
      ((GeneralDictionarySemanticCollapseSchema.newCapture s registry invocation declaration).inputs s.binder) actual := by
  unfold GeneralDictionarySemanticCollapseSchema.oldCapture at valid
  unfold GeneralDictionarySemanticCollapseSchema.newCapture
  rw [bindings_before] at propagated valid
  rw [bindings_after]
  have exactFits := (GeneralNominalCaptureMerges.capture_interval_exact state.context.state registry invocation
    declaration _ model ((propagate_models ..).mp propagated).2.2 s.binder declared
    (by simp [occurrences]) actual).mp valid
  simpa [capture,occurrences] using exactFits (firstPair s) (by simp [occurrences,firstPair])

/-- Old branch private constraints already contain the retained nonpoint leaf
self-check. Current private Models is derived, not assumed. -/
theorem private_state (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : GeneralNominalState.Models (privateState registry state.context root declaration [(s.root,s.root)]) model)
    (current : GeneralNominalState.Models revision.snapshot model) :
    GeneralNominalState.Models (privateState registry (currentContext revision) root declaration [(s.root,s.root)]) model := by
  have rs := reports s declaration queries
  unfold privateState at old ⊢
  rw [rs.1] at old
  rw [rs.2]
  obtain ⟨oldProp,oldChecks⟩ := (GeneralNominalState.extend_models ..).mp old
  have prop : GeneralNominalState.Models (propagate state.context.state registry root.identity declaration
    (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model := by
    rw [before_exact]
    exact oldProp
  have newProp := current_propagation s registry root.identity declaration model names prop current
  apply (GeneralNominalState.extend_models ..).mpr
  constructor
  · rw [after_exact] at newProp
    exact newProp
  · intro atom member
    unfold selfChecks at member
    obtain ⟨bounds,inside,rfl⟩ := List.mem_map.mp member
    change bounds ∈ [(s.root,s.root),(s.root,s.root),(s.lower,s.lower),s.first] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact CommonNominalFullCarrier.subtype_refl _
    rcases List.mem_cons.mp inside with rfl | inside
    · exact CommonNominalFullCarrier.subtype_refl _
    rcases List.mem_cons.mp inside with rfl | inside
    · exact CommonNominalFullCarrier.subtype_refl _
    have eq := List.mem_singleton.mp inside
    subst bounds
    exact oldChecks _ (by simp [selfChecks,oldRootReport,beforeReport,currentContext,Revision.snapshot])
end Yulang.GeneralDictionaryNonpointCollapse
