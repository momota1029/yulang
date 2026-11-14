import Yulang.GeneralDictionaryCenteredOverlapExact181
import Yulang.GeneralNominalSupportProvenance182
import Yulang.GeneralDictionaryCenteredProvenance181
import Yulang.GeneralDictionaryCenteredGuard177
import Yulang.GeneralDictionaryCenteredNovel177

/-! All registered schema locations can discharge the linear-leaf overlap premise.
The finite coverage certificate is an explicit residual; reachability alone is
not claimed to produce it, nor to produce raw installation or value support. -/
namespace Yulang.GeneralDictionaryCenteredSchemaCoverage182
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection GeneralDictionaryLinearLeaf
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryCenteredOverlapExact181
open GeneralNominalRawFrame179 (fullSources)

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {root focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}
  (plan : Plan roles)
  (shape : LinearLeafShape plan.packet.context plan.packet.site.occurrence plan.packet.declaration)

/-- The certificate names existing actual uses rather than asserting a model
extension, final Plan.Holds, or the desired semantic equality. -/
def Covered (state : State roles) : Prop :=
  ∀ i : Fin shape.arity,
    plan.packet.context.state.base.source (shape.bounds i).1 ≠
      plan.packet.context.state.base.source (shape.bounds i).2 →
    plan.binder (shape.names i) ∈ fullSources state →
    GeneralNominalSupportProvenance182.ActualBinder state (plan.binder (shape.names i))
      (.nominal (.source (plan.packet.context.state.base.source shape.slot))
        shape.descriptor.declaration.name i.val)

 theorem of_head_covered (covered : GeneralDictionaryCenteredProvenance181.Covered plan shape state) :
    Covered plan shape state := by
  intro i nonpoint member
  obtain ⟨old,registered,entry,present,actual,origin,center⟩ := covered i nonpoint member
  exact ⟨old,registered,old.headSchema,.head,entry,present,actual,center.symm,origin.symm⟩

 theorem compatible
    (covered : Covered plan shape state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    Compatible state plan shape model := by
  intro i nonpoint member value seen
  exact GeneralNominalSupportProvenance182.actual_readback valid (covered i nonpoint member) value seen

 theorem joint
    (candidate : Candidate registry state focus key children plan)
    (named : plan.input.PointNames) (covered : Covered plan shape state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    ∃ extended, Models state extended ∧ plan.Holds extended ∧
      ∀ name ∈ fullSources state, extended name = model name := by
  have located : plan.packet.bounds = [(shape.slot,shape.slot)] :=
    Option.some.inj (candidate.located.symm.trans shape.located)
  exact joint_model state plan shape candidate.context_eq located named model valid
    (compatible plan shape covered model valid)

 theorem installable
    (candidate : Candidate registry state focus key children plan)
    (selected : GeneralNominalCenteredBoundary.Local registry state focus (.selected key children))
    (raw : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (support : List (Occurrence roles))
    (values : GeneralNominalValueSupport.PacketGuard state.erased plan.packet support)
    (named : plan.input.PointNames) (covered : Covered plan shape state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralNominalCenteredBoundary.Installable registry state plan := by
  obtain ⟨extended,models,holds,_⟩ := joint plan shape candidate named covered model valid
  exact ⟨raw,support,(GeneralDictionaryCenteredGuard177.candidate_guard_iff
    candidate selected support).mpr ⟨values,extended,models,holds⟩⟩

 theorem stable_instance
    (candidate : Candidate registry state focus key children plan)
    (selected : GeneralNominalCenteredBoundary.Local registry state focus (.selected key children))
    (stable : Stable registry state focus)
    (raw : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (support : List (Occurrence roles))
    (values : GeneralNominalValueSupport.PacketGuard state.erased plan.packet support)
    (named : plan.input.PointNames) (covered : Covered plan shape state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.erased.current.context model focus key children :=
  GeneralDictionaryCenteredNovel177.committed_or_installable_instance candidate stable
    (.inr (installable plan shape candidate selected raw support values named covered model valid)) model valid

end Yulang.GeneralDictionaryCenteredSchemaCoverage182
