import Yulang.GeneralDictionaryCenteredAliasProvenance181
import Yulang.GeneralNominalLedgerReadback181

/-! The centered ledger itself supplies registered head equations. Raw packet
registration and execution history are unnecessary for this local readback
step. Coverage of unregistered current candidates remains an explicit input. -/
namespace Yulang.GeneralDictionaryCenteredLedger181
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection GeneralDictionaryLinearLeaf CommonNominalFullCarrier
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryCenteredOverlapExact181
open GeneralNominalRawFrame179 (fullSources)
open GeneralDictionaryCenteredPointReadback179 GeneralDictionaryCenteredPointJoint179

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}
  (plan : Plan roles)
  (shape : LinearLeafShape plan.packet.context plan.packet.site.occurrence plan.packet.declaration)

 theorem registered_covered (registered : plan ∈ state.plans) (named : plan.input.PointNames) :
    GeneralDictionaryCenteredProvenance181.Covered plan shape state := by
  intro i _ _
  let use : GeneralNominalMaterialization.Use :=
    ⟨shape.names i,.nominal (.source (plan.packet.context.state.base.source shape.slot))
      shape.descriptor.declaration.name i.val,.actual⟩
  refine ⟨plan,registered,use,?_,rfl,rfl,rfl⟩
  rw [head_schema plan shape (centers_exact plan shape named)]
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

 theorem compatible
    (covered : GeneralDictionaryCenteredProvenance181.Covered plan shape state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    Compatible state plan shape model := by
  intro i nonpoint member value seen
  obtain ⟨old,registered,use,present,actual,origin,center⟩ := covered i nonpoint member
  have readback := GeneralNominalLedgerReadback181.registered_actual old registered model valid
    use present actual
  rw [origin] at seen
  rw [center]
  exact readback.2.2 value (model (old.binder use.name)).1 seen (.source _)

 theorem joint
    (candidate : Candidate registry state focus key children plan)
    (named : plan.input.PointNames)
    (covered : GeneralDictionaryCenteredProvenance181.Covered plan shape state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    ∃ extended, Models state extended ∧ plan.Holds extended ∧
      ∀ name ∈ fullSources state, extended name = model name := by
  have located : plan.packet.bounds = [(shape.slot,shape.slot)] :=
    Option.some.inj (candidate.located.symm.trans shape.located)
  exact joint_model state plan shape candidate.context_eq located named model valid
    (compatible plan shape covered model valid)

 theorem alias_compatible
    (covered : GeneralDictionaryCenteredAliasProvenance181.Covered plan shape state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    Compatible state plan shape model := by
  intro i nonpoint member value seen
  obtain ⟨old,registered,use,present,actual,rename,recorded,origin,center⟩ := covered i nonpoint member
  rw [origin] at seen
  exact GeneralNominalLedgerReadback181.registered_alias_readback old plan registered model valid
    use present actual rename recorded _ center value seen

 theorem alias_joint
    (candidate : Candidate registry state focus key children plan)
    (named : plan.input.PointNames)
    (covered : GeneralDictionaryCenteredAliasProvenance181.Covered plan shape state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    ∃ extended, Models state extended ∧ plan.Holds extended ∧
      ∀ name ∈ fullSources state, extended name = model name := by
  have located : plan.packet.bounds = [(shape.slot,shape.slot)] :=
    Option.some.inj (candidate.located.symm.trans shape.located)
  exact joint_model state plan shape candidate.context_eq located named model valid
    (alias_compatible plan shape covered model valid)

end Yulang.GeneralDictionaryCenteredLedger181
