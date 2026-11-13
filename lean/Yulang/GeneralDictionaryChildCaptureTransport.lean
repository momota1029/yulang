import Yulang.GeneralDictionaryNonpointCollapse
import Yulang.GeneralDictionaryEmissionRequestIdentity

/-! Actual child identities are stable while capture intervals may change.
Variable-only child input acceptance transports under the existing nonpoint
collapse. This does not prove current child selection or child Evidence. -/
namespace Yulang.GeneralDictionaryChildCaptureTransport
open GeneralDeclarations GeneralDeclarationDemands GeneralNominalAllocation
open GeneralDeclarationPatterns GeneralNominalCaptureMerges
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseSchema
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection

/-- IDs depend on the seed, invocation, declaration and clause, not captures. -/
theorem emitted_identity (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (old current : Capture)
    (allocation : Allocation roles clause) (bindings : Bindings) :
    (GeneralDictionaryEmissionPlans.occurrence (frame state registry invocation bindings)
      (emit invocation declaration clause valid current allocation)).identity =
    (GeneralDictionaryEmissionPlans.occurrence (frame state registry invocation bindings)
      (emit invocation declaration clause valid old allocation)).identity := rfl

theorem child_outputs (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (old current : Capture)
    (same : current.outputs = old.outputs) (allocation : Allocation roles clause) :
    (childDemand declaration clause valid current allocation).outputs =
      (childDemand declaration clause valid old allocation).outputs := by
  unfold childDemand
  apply List.map_congr_left
  intro equation _
  rw [GeneralDictionaryEmissionRequestIdentity.output_target declaration old current same]

theorem variable_argument (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : Capture)
    (allocation : Allocation roles clause) (index : Fin (roles clause.role).arity)
    (name : Nat)
    (isVar : normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var name) :
    (childDemand declaration clause valid capture allocation).arguments index = capture.inputs name := by
  simp only [childDemand, inputInterval, isVar]

/-- A general emitter-only fact, explicitly conditional on capture Fits inclusion. -/
theorem variable_argument_fits (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (old current : Capture)
    (allocation : Allocation roles clause) (index : Fin (roles clause.role).arity)
    (name : Nat) (model : GeneralNominalCommonBridge.Assignment)
    (isVar : normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var name)
    (widen : ∀ actual, Fits model (old.inputs name) actual → Fits model (current.inputs name) actual)
    (actual : CommonNominalFullCarrier.Ty)
    (fits : Fits model ((childDemand declaration clause valid old allocation).arguments index) actual) :
    Fits model ((childDemand declaration clause valid current allocation).arguments index) actual := by
  rw [variable_argument declaration clause valid old allocation index name isVar] at fits
  rw [variable_argument declaration clause valid current allocation index name isVar]
  exact widen actual fits

/-- Complete canonical child-ID lists, including multiplicity and order, are
stable across arbitrary capture changes and source states with the same seed. -/
theorem children_identities (first last : GeneralNominalState.State)
    (sameSeed : last.seed = first.seed) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration) (old current : Bindings) :
    (children last registry root declaration checked current).map (fun child => child.identity) =
      (children first registry root declaration checked old).map (fun child => child.identity) := by
  simp only [children, GeneralDictionaryEmissionPlans.children,
    GeneralCanonicalChildOrder.canonicalEmit, emitAll, List.map_map]
  apply List.map_congr_left
  intro clause _
  simp only [Function.comp_apply, GeneralDictionaryEmissionPlans.occurrence, emit,
    frame, source, sameSeed]

variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

/-- For the real Shape collapse, Fits inclusion is proved from propagation,
not assumed. The child's variable input uses the parent's singleton binder. -/
theorem collapsed_child_fits (s : Shape revision) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (isVar : normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var s.binder)
    (declared : s.binder ∈ declaration.inputNames)
    (model : GeneralNominalCommonBridge.Assignment)
    (propagated : GeneralNominalState.Models (propagate state.context.state registry invocation declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model)
    (actual : CommonNominalFullCarrier.Ty)
    (fits : Fits model ((childDemand declaration clause valid
      (oldCapture s registry invocation declaration)
      (allocation state.context.state registry invocation declaration.id clause)).arguments index) actual) :
    Fits model ((childDemand declaration clause valid
      (newCapture s registry invocation declaration)
      (allocation revision.snapshot registry invocation declaration.id clause)).arguments index) actual := by
  have sameAllocation : allocation (roles := roles) revision.snapshot registry invocation declaration.id clause =
      allocation state.context.state registry invocation declaration.id clause := rfl
  rw [sameAllocation]
  exact variable_argument_fits declaration clause valid _ _ _ index s.binder model isVar
    (GeneralDictionaryNonpointCollapse.capture_fits s registry invocation declaration model declared propagated) actual fits

theorem collapsed_child_outputs (s : Shape revision) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) :
    (childDemand declaration clause valid (newCapture s registry invocation declaration)
      (allocation revision.snapshot registry invocation declaration.id clause)).outputs =
    (childDemand declaration clause valid (oldCapture s registry invocation declaration)
      (allocation state.context.state registry invocation declaration.id clause)).outputs :=
  child_outputs declaration clause valid _ _ rfl _

theorem collapsed_child_identity (s : Shape revision) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) :
    (GeneralDictionaryEmissionPlans.occurrence
      (frame revision.snapshot registry invocation
        (bindings revision.snapshot (inspect revision.snapshot (query s) (s.root,s.root) none)))
      (emit invocation declaration clause valid (newCapture s registry invocation declaration)
        (allocation revision.snapshot registry invocation declaration.id clause))).identity =
    (GeneralDictionaryEmissionPlans.occurrence
      (frame state.context.state registry invocation
        (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none)))
      (emit invocation declaration clause valid (oldCapture s registry invocation declaration)
        (allocation state.context.state registry invocation declaration.id clause))).identity := rfl

end Yulang.GeneralDictionaryChildCaptureTransport
