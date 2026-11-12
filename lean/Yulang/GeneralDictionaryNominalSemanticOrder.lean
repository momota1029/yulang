import Yulang.GeneralDictionaryNominalSourceEvidence
import Yulang.GeneralDictionaryNominalCandidateOrder

/-!
# Registry-order invariance of arbitrary nominal source evidence

Visible and where enumeration preserve actual variable-head intervals, captured
binder values, explicit RHS meaning and complete canonical children. The result
applies to arbitrary source evidence, not only successfully prepared recipes.
Source frames, assignments, chosen keys and dictionary occurrences stay fixed;
no candidate-selection or final-state independence is asserted. Full nominal
assignments are arbitrary and need not be lifted from the Common carrier.
-/
namespace Yulang.GeneralDictionaryNominalSemanticOrder
open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open GeneralDictionaryTransactions (Frames)
open GeneralDictionaryNominalSourceEvidence (Realizes)
open GeneralDictionaryNominalSourceEvidence (Instance)
open GeneralNominalCommonBridge (Assignment)

/-- The very same values realize the reordered declaration; no replacement
instantiation or new model is selected by this transport. -/
theorem realizes_reorders (order : DeclarationReorders first last)
    (capture : GeneralDeclarationDemands.Capture) (assignment : Assignment)
    (binderValues : Nat → CommonNominalFullCarrier.Ty) :
    Realizes first capture assignment binderValues ↔ Realizes last capture assignment binderValues := by
  rw [declarationReorders_update order]
  rfl

/-- Forward transport preserves the source declaration's identity, all children
and the existing witness values, without using materializer success. -/
theorem instance_reorders_forward (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frames : Frames roles) (assignment : Assignment) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles))
    (instanceRule : Instance ⟨constructors, roles, first⟩ one frames assignment root key children) :
    Instance ⟨constructors, roles, last⟩ two frames assignment root key children := by
  obtain ⟨declaration, present, identity, role, generated, binderValues, realized, head, outputs⟩ := instanceRule
  obtain ⟨other, member, reordered⟩ := reorders_visible order declaration present
  refine ⟨other, member, reordered.id.symm.trans identity, reordered.role.symm.trans role,
    generated.trans (GeneralDictionaryEmissionPlans.children_reorders (frames root) root reordered
      (one.2 declaration present) (two.2 other member)), binderValues, ?_, ?_, ?_⟩
  · rw [← reordered.id]
    exact (realizes_reorders reordered _ assignment binderValues).mp realized
  · intro index
    obtain ⟨pattern, binder, atIndex, normalized, lower, upper⟩ := head index
    exact ⟨pattern, binder, by rw [← reordered.head]; exact atIndex, normalized, lower, upper⟩
  · intro index
    obtain ⟨equation, binder, supplied, normalized, equivalent⟩ := outputs index
    exact ⟨equation, binder,
      (GeneralDictionaryAssociatedProvenance.supplies_reorders roles reordered _ _).mp supplied,
      normalized, equivalent⟩

/-- Independent source instances are unchanged by visible and where order. -/
theorem instance_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frames : Frames roles) (assignment : Assignment) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) :
    Instance ⟨constructors, roles, first⟩ one frames assignment root key children ↔
      Instance ⟨constructors, roles, last⟩ two frames assignment root key children :=
  ⟨instance_reorders_forward constructors roles first last one two order frames assignment root key children,
    instance_reorders_forward constructors roles last first two one
      (GeneralRegistryChildOrder.reorders_symm order) frames assignment root key children⟩

/-- All finite source evidence transports, including evidence not obtained by
the partial singleton-input materializer. The dictionary itself stays fixed. -/
theorem evidence_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frames : Frames roles) (assignment : Assignment) (dictionary : Dictionary roles) :
    Evidence (Instance ⟨constructors, roles, first⟩ one frames assignment) dictionary ↔
      Evidence (Instance ⟨constructors, roles, last⟩ two frames assignment) dictionary := by
  constructor
  · exact evidence_mono _ _
      (instance_reorders_forward constructors roles first last one two order frames assignment)
  · exact evidence_mono _ _
      (instance_reorders_forward constructors roles last first two one
        (GeneralRegistryChildOrder.reorders_symm order) frames assignment)

/-- The adapter itself computes both frame functions. This removes the caller's
frame-equality premise while retaining the fixed candidate context. -/
theorem computed_instance_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (context : GeneralNominalCandidates.Context) (assignment : Assignment)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles)) :
    Instance ⟨constructors, roles, first⟩ one
      (GeneralDictionaryNominalCandidateReadback.frames ⟨constructors, roles, first⟩ context)
      assignment root key children ↔
    Instance ⟨constructors, roles, last⟩ two
      (GeneralDictionaryNominalCandidateReadback.frames ⟨constructors, roles, last⟩ context)
      assignment root key children := by
  rw [GeneralDictionaryNominalCandidateOrder.frames_reorders constructors roles first last two order context]
  exact instance_reorders constructors roles first last one two order _ assignment root key children

/-- One unchanged source dictionary carries independent nominal meaning in both
registry orders, at the same assignment and computed candidate context. -/
theorem computed_evidence_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (context : GeneralNominalCandidates.Context) (assignment : Assignment) (dictionary : Dictionary roles) :
    Evidence (Instance ⟨constructors, roles, first⟩ one
      (GeneralDictionaryNominalCandidateReadback.frames ⟨constructors, roles, first⟩ context) assignment) dictionary ↔
    Evidence (Instance ⟨constructors, roles, last⟩ two
      (GeneralDictionaryNominalCandidateReadback.frames ⟨constructors, roles, last⟩ context) assignment) dictionary := by
  rw [GeneralDictionaryNominalCandidateOrder.frames_reorders constructors roles first last two order context]
  exact evidence_reorders constructors roles first last one two order _ assignment dictionary

end Yulang.GeneralDictionaryNominalSemanticOrder
