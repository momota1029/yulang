import Yulang.GeneralDictionaryRecursiveEvidenceFacts
import Yulang.GeneralDictionaryRecursiveOrder

/-!
# Order independence of recursive source-instance meaning

The context, complete source dictionary and full assignment stay fixed. Canonical
emission and recursive inspection retain all projection/materialization conditions.
This does not compare final states of different saturation schedules.
-/
namespace Yulang.GeneralDictionaryRecursiveSemanticOrder
open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates (Context BranchModels RequestReady)
open GeneralNominalRecursiveInspection (bindings)
open GeneralDictionaryRecursiveEvidence (Instance)
open GeneralDictionaryRecursiveOrder (report_reorders)

/-- Canonical materialization requests are independent of both visible and where order. -/
theorem generated_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (context : Context) (root : Occurrence roles) (a b : Declaration)
    (order : DeclarationReorders a b)
    (ac : DeclarationChecked constructors roles a) (bc : DeclarationChecked constructors roles b)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    GeneralNominalRecursiveCandidates.generated ⟨constructors,roles,first⟩ context root a ac bounds =
      GeneralNominalRecursiveCandidates.generated ⟨constructors,roles,last⟩ context root b bc bounds := by
  have rep := report_reorders context a b order bounds
  unfold GeneralNominalRecursiveCandidates.generated GeneralNominalMaterialization.requests
  have cap : GeneralNominalAllocation.capture context.state ⟨constructors,roles,first⟩ root.identity a.id
      (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds)) =
    GeneralNominalAllocation.capture context.state ⟨constructors,roles,last⟩ root.identity b.id
      (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)) := by
    rw [rep,order.id]
    rfl
  have alloc : GeneralNominalAllocation.allocation (roles := roles) context.state ⟨constructors,roles,first⟩ root.identity a.id =
      GeneralNominalAllocation.allocation (roles := roles) context.state ⟨constructors,roles,last⟩ root.identity b.id := by
    rw [order.id]
    rfl
  rw [← cap,← alloc,GeneralCanonicalChildOrder.canonicalEmit_reorders root.identity order ac bc]
  simp only [GeneralNominalMaterialization.rootRequests,order.associated]

/-- Per-model branch equations, including projection and generated source facts,
are invariant; existence of a branch is not substituted for this assignment. -/
theorem branch_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (context : Context) (root : Occurrence roles) (a b : Declaration)
    (order : DeclarationReorders a b)
    (ac : DeclarationChecked constructors roles a) (bc : DeclarationChecked constructors roles b)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : GeneralNominalCommonBridge.Assignment) :
    BranchModels ⟨constructors,roles,first⟩ context root a ac bounds model ↔
      BranchModels ⟨constructors,roles,last⟩ context root b bc bounds model := by
  rw [GeneralDictionaryRecursiveEvidence.branch_models_iff,
    GeneralDictionaryRecursiveEvidence.branch_models_iff,
    generated_reorders constructors roles first last context root a b order ac bc bounds,
    report_reorders context a b order bounds]
  simp only [GeneralNominalAllocation.merges,Declaration.inputNames,order.head,order.id,
    GeneralNominalMaterialization.Models,GeneralNominalMaterialization.VariableHolds,
    Declaration.outputNames,order.outputBinders,GeneralNominalAllocation.capture,
    GeneralNominalAllocation.source]
  rfl

/-- Independent per-model source instances transport without replacing the
model, dictionary, or full emitted occurrence list. -/
theorem instance_reorders_forward (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (_one : Checked ⟨constructors,roles,first⟩) (two : Checked ⟨constructors,roles,last⟩)
    (order : Reorders ⟨constructors,roles,first⟩ ⟨constructors,roles,last⟩)
    (context : Context) (model : GeneralNominalCommonBridge.Assignment)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (rule : Instance ⟨constructors,roles,first⟩ context model root key children) :
    Instance ⟨constructors,roles,last⟩ context model root key children := by
  obtain ⟨a,present,ac,identity,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := rule
  obtain ⟨b,visible,pair⟩ := reorders_visible order a present
  have bc := two.2 b visible
  have rep := report_reorders context a b pair bounds
  refine ⟨b,visible,bc,pair.id.symm.trans identity,pair.role.symm.trans role,bounds,located,?_,?_,?_,metadata,?_⟩
  · rwa [← rep]
  · refine ⟨?_,?_⟩
    · simpa only [GeneralNominalMaterialization.RootDefined,← pair.associated] using ready.1
    · rw [← generated_reorders constructors roles first last context root a b pair ac bc bounds]
      exact ready.2
  · rw [emitted]
    unfold GeneralNominalAllocation.children
    rw [rep]
    have frames : GeneralNominalAllocation.frame (roles := roles) context.state ⟨constructors,roles,first⟩ root.identity
        (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)) =
      GeneralNominalAllocation.frame (roles := roles) context.state ⟨constructors,roles,last⟩ root.identity
        (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)) := rfl
    rw [frames]
    exact GeneralDictionaryEmissionPlans.children_reorders _ root pair ac bc
  · exact (branch_reorders constructors roles first last context root a b pair ac bc bounds model).mp branch

/-- The equality is at the independent source judgment, not just executor output. -/
theorem instance_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors,roles,first⟩) (two : Checked ⟨constructors,roles,last⟩)
    (order : Reorders ⟨constructors,roles,first⟩ ⟨constructors,roles,last⟩)
    (context : Context) (model : GeneralNominalCommonBridge.Assignment)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles)) :
    Instance ⟨constructors,roles,first⟩ context model root key children ↔
      Instance ⟨constructors,roles,last⟩ context model root key children :=
  ⟨instance_reorders_forward constructors roles first last one two order context model root key children,
    instance_reorders_forward constructors roles last first two one
      (GeneralRegistryChildOrder.reorders_symm order) context model root key children⟩

/-- Every finite semantic source tree keeps the identical assignment and nodes. -/
theorem indexed_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors,roles,first⟩) (two : Checked ⟨constructors,roles,last⟩)
    (order : Reorders ⟨constructors,roles,first⟩ ⟨constructors,roles,last⟩)
    (context : Context) (model : GeneralNominalCommonBridge.Assignment)
    (tree : Dictionary roles) :
    Evidence (Instance ⟨constructors,roles,first⟩ context model) tree ↔
      Evidence (Instance ⟨constructors,roles,last⟩ context model) tree :=
  ⟨evidence_mono _ _ (instance_reorders_forward constructors roles first last one two order context model),
    evidence_mono _ _ (instance_reorders_forward constructors roles last first two one
      (GeneralRegistryChildOrder.reorders_symm order) context model)⟩

/-- Runtime Evidence has the same source witness before and after reordering. -/
theorem evidence_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors,roles,first⟩) (two : Checked ⟨constructors,roles,last⟩)
    (order : Reorders ⟨constructors,roles,first⟩ ⟨constructors,roles,last⟩)
    (context : Context) (model : GeneralNominalCommonBridge.Assignment)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence ⟨constructors,roles,first⟩ context model root payload ↔
      GeneralDictionaryRecursiveEvidence.Evidence ⟨constructors,roles,last⟩ context model root payload := by
  constructor
  · rintro ⟨tree,readback,evidence⟩
    exact ⟨tree,readback,(indexed_reorders constructors roles first last one two order context model tree).mp evidence⟩
  · rintro ⟨tree,readback,evidence⟩
    exact ⟨tree,readback,(indexed_reorders constructors roles first last one two order context model tree).mpr evidence⟩

end Yulang.GeneralDictionaryRecursiveSemanticOrder
