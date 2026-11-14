import Yulang.GeneralDictionaryCenteredJournalOverlap180

/-! Exact overlap criterion for extending a fixed centered journal model with
an actual linear nominal leaf. Compatibility is semantic, not name freshness.
The result does not assert the unrestricted ground evidence field. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCenteredOverlapExact181
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalCenteredSteps GeneralDictionaryLinearLeaf
open GeneralDictionaryCenteredPointReadback179 GeneralDictionaryCenteredPointJoint179
open GeneralNominalRawFrame179 (fullSources)
open CommonNominalFullCarrier GeneralNominalCenteredModelExtension
variable {roles : Roles.RoleDecls} (journal : State roles) (plan : Plan roles)
  (shape : LinearLeafShape plan.packet.context plan.packet.site.occurrence plan.packet.declaration)

/-- Only non-point input binders can impose additional overlap constraints. -/
def Compatible (previous : GeneralNominalCommonBridge.Assignment) : Prop :=
  ∀ i : Fin shape.arity,
    plan.packet.context.state.base.source (shape.bounds i).1 ≠
      plan.packet.context.state.base.source (shape.bounds i).2 →
    plan.binder (shape.names i) ∈ fullSources journal →
    ∀ value, Observes previous
      (.nominal (.source (plan.packet.context.state.base.source shape.slot))
        shape.descriptor.declaration.name i.val) value →
    Equivalent value (previous (plan.binder (shape.names i))).1

 theorem joint_model
    (contextEq : plan.packet.context = journal.erased.current.context)
    (located : plan.packet.bounds = [(shape.slot,shape.slot)])
    (named : plan.input.PointNames)
    (previous : GeneralNominalCommonBridge.Assignment)
    (valid : Models journal previous)
    (compatible : Compatible journal plan shape previous) :
    ∃ extended, Models journal extended ∧ plan.Holds extended ∧
      ∀ name ∈ fullSources journal, extended name = previous name := by
  obtain ⟨extended,models,kept,readback⟩ :=
    GeneralDictionaryCenteredJournalOverlap180.readback_extension journal plan shape
      contextEq located previous compatible valid
  have source : GeneralNominalState.Models plan.packet.context.state extended := by
    rw [contextEq]; exact models.1.1
  exact ⟨extended,models,
    (holds_iff_readback plan shape located (centers_exact plan shape named) extended source
      (point_input plan shape named extended)).mpr readback,kept⟩

 theorem compatible_of_joint
    (contextEq : plan.packet.context = journal.erased.current.context)
    (located : plan.packet.bounds = [(shape.slot,shape.slot)])
    (named : plan.input.PointNames)
    (previous extended : GeneralNominalCommonBridge.Assignment)
    (models : Models journal extended) (holds : plan.Holds extended)
    (kept : ∀ name ∈ fullSources journal, extended name = previous name) :
    Compatible journal plan shape previous := by
  have source : GeneralNominalState.Models plan.packet.context.state extended := by
    rw [contextEq]; exact models.1.1
  have readback := (holds_iff_readback plan shape located (centers_exact plan shape named)
    extended source (point_input plan shape named extended)).mp holds
  have member : plan.packet.context.state.base.source shape.slot ∈ fullSources journal := by
    have one := GeneralDictionaryCenteredPointJoint179.source_member shape.slot
    have sources : GeneralNominalState.sources plan.packet.context.state =
        GeneralNominalState.sources journal.erased.current.context.state := by rw [contextEq]
    rw [sources] at one
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ one))
  intro i _ overlap value observed
  have seen : Observes extended
      (.nominal (.source (plan.packet.context.state.base.source shape.slot))
        shape.descriptor.declaration.name i.val) value :=
    observes_same observed (kept _ member).symm
  have result := (readback i).2.2 value (extended (plan.binder (shape.names i))).1 seen (.source _)
  rwa [kept _ overlap] at result

 theorem joint_iff
    (contextEq : plan.packet.context = journal.erased.current.context)
    (located : plan.packet.bounds = [(shape.slot,shape.slot)])
    (named : plan.input.PointNames)
    (previous : GeneralNominalCommonBridge.Assignment) (valid : Models journal previous) :
    (∃ extended, Models journal extended ∧ plan.Holds extended ∧
      ∀ name ∈ fullSources journal, extended name = previous name) ↔
    Compatible journal plan shape previous := by
  constructor
  · rintro ⟨extended,models,holds,kept⟩
    exact compatible_of_joint journal plan shape contextEq located named previous extended models holds kept
  · exact joint_model journal plan shape contextEq located named previous valid

end Yulang.GeneralDictionaryCenteredOverlapExact181
