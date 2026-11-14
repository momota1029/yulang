import Yulang.GeneralDictionaryCenteredProvenance181
import Yulang.GeneralNominalOriginRootAlias181

/-! Current ordinary source equations transport an old registered actual-use
origin to its renamed current origin. Coverage refers only to syntax and old
journal membership; no semantic readback or joint-model result is supplied. -/
namespace Yulang.GeneralDictionaryCenteredAliasProvenance181
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection GeneralDictionaryLinearLeaf CommonNominalFullCarrier
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryCenteredOverlapExact181
open GeneralNominalRawFrame179 (fullSources)
open GeneralNominalOriginAlias181 (mapSource)
open GeneralNominalOriginRootAlias181 (RootRecorded recorded_root_similar)

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {root focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}
  (plan : Plan roles)
  (shape : LinearLeafShape plan.packet.context plan.packet.site.occurrence plan.packet.declaration)

 def Covered (state : State roles) : Prop :=
  ∀ i : Fin shape.arity,
    plan.packet.context.state.base.source (shape.bounds i).1 ≠
      plan.packet.context.state.base.source (shape.bounds i).2 →
    plan.binder (shape.names i) ∈ fullSources state →
    ∃ old ∈ state.plans, ∃ use ∈ old.headSchema.variables,
      use.mode = .actual ∧ ∃ rename : Nat → Nat,
      RootRecorded state.erased.current.context.state rename use.origin ∧
      (.nominal (.source (plan.packet.context.state.base.source shape.slot))
        shape.descriptor.declaration.name i.val : Origin) = mapSource rename use.origin ∧
      plan.binder (shape.names i) = old.binder use.name

 theorem compatible
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (covered : Covered plan shape state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    Compatible state plan shape model := by
  intro i nonpoint member value seen
  obtain ⟨old,registered,use,present,actual,rename,recorded,origin,center⟩ := covered i nonpoint member
  have related := recorded_root_similar state.erased.current.context.state model valid.1.1
    rename use.origin recorded
  rw [origin] at seen
  obtain ⟨prior,observed,equal⟩ := related.2 value seen
  have oldReadback := GeneralNominalBinderIdentity181.registered_readback path old plan registered
    valid use present actual use.origin rfl _ center prior observed
  exact ⟨subtype_trans equal.1 oldReadback.1,subtype_trans oldReadback.2 equal.2⟩

 theorem joint
    (candidate : Candidate registry state focus key children plan)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (named : plan.input.PointNames) (covered : Covered plan shape state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    ∃ extended, Models state extended ∧ plan.Holds extended ∧
      ∀ name ∈ fullSources state, extended name = model name := by
  have located : plan.packet.bounds = [(shape.slot,shape.slot)] :=
    Option.some.inj (candidate.located.symm.trans shape.located)
  exact joint_model state plan shape candidate.context_eq located named model valid
    (compatible plan shape path covered model valid)

end Yulang.GeneralDictionaryCenteredAliasProvenance181
