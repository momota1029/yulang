import Yulang.GeneralDictionarySemanticCollapseAllocation

/-! Replay of the same named-output schema after actual nested capture collapse.
Only semantic endpoint equivalence, derived from old projection/propagation,
is used. This does not identify newly emitted child source identities. -/
namespace Yulang.GeneralDictionarySemanticCollapseSchema
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseAllocation
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection
open GeneralNominalAllocation GeneralDeclarations GeneralNominalMaterialization
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

abbrev oldCapture (s : Shape revision) (registry : Registry) (invocation : Nat) (declaration : Declaration) :=
 capture state.context.state registry invocation declaration.id
   (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))
abbrev newCapture (s : Shape revision) (registry : Registry) (invocation : Nat) (declaration : Declaration) :=
 capture revision.snapshot registry invocation declaration.id
   (bindings revision.snapshot (inspect revision.snapshot (query s) (s.root,s.root) none))

theorem footprint (s : Shape revision) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (schema : Schema) (model : GeneralNominalCommonBridge.Assignment)
    (declared : s.binder ∈ declaration.inputNames)
    (scope : ∀ entry ∈ schema.variables, entry.name ∉ declaration.outputNames → entry.name = s.binder)
    (old : ProjectionModels state.context.state
      (inspect state.context.state (query s) (s.root,s.root) none) model)
    (firstPoint : s.first.1 = s.first.2) (lastPoint : s.last.1 = s.last.2)
    (propagated : GeneralNominalState.Models (propagate state.context.state registry invocation declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model) :
    GeneralDictionarySemanticSchemaTransport.Footprint declaration (oldCapture s registry invocation declaration)
      (newCapture s registry invocation declaration)
      (inspect state.context.state (query s) (s.root,s.root) none)
      (inspect revision.snapshot (query s) (s.root,s.root) none) schema model := by
  refine ⟨?_,?_,?_⟩
  · intro entry member output
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member input
    rw [scope entry member input]
    have same := capture_endpoints s registry invocation declaration model declared old firstPoint lastPoint propagated
    exact ⟨⟨same.1.2,same.1.1⟩,⟨same.2.2,same.2.1⟩⟩
  · intro entry member captured present same actual origin known
    rw [after_exact] at present
    have eq := List.mem_singleton.mp present
    subst captured
    refine ⟨⟨s.binder,s.first,some (leaf s)⟩,?_,rfl,known⟩
    rw [before_exact]; simp [beforeReport]

theorem replay (s : Shape revision) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (schema : Schema) (model : GeneralNominalCommonBridge.Assignment)
    (declared : s.binder ∈ declaration.inputNames)
    (scope : ∀ entry ∈ schema.variables, entry.name ∉ declaration.outputNames → entry.name = s.binder)
    (old : ProjectionModels state.context.state
      (inspect state.context.state (query s) (s.root,s.root) none) model)
    (firstPoint : s.first.1 = s.first.2) (lastPoint : s.last.1 = s.last.2)
    (propagated : GeneralNominalState.Models (propagate state.context.state registry invocation declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model)
    (materialized : GeneralNominalMaterialization.Models state.context.state declaration
      (oldCapture s registry invocation declaration)
      (inspect state.context.state (query s) (s.root,s.root) none) schema model) :
    GeneralNominalMaterialization.Models revision.snapshot declaration
      (newCapture s registry invocation declaration)
      (inspect revision.snapshot (query s) (s.root,s.root) none) schema model :=
  GeneralDictionarySemanticSchemaTransport.replay declaration _ _ _ _ schema schema
    (fun _ h => h) (fun _ h => h) model
    (footprint s registry invocation declaration schema model declared scope old firstPoint lastPoint propagated)
    materialized
end Yulang.GeneralDictionarySemanticCollapseSchema
