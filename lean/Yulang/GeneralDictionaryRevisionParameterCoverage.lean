import Yulang.GeneralDictionaryRevisionArgumentBridge
import Yulang.GeneralNominalLinearMaterializationFacts

/-! Every old parameter position has a compatible current parameter after a
certified revision, without separately assuming current arity or indexed lookup.
This is semantic compatibility, not source endpoint equality. -/
namespace Yulang.GeneralDictionaryRevisionParameterCoverage
open GeneralNominalReobservationSteps GeneralNominalState
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}

theorem arity (revision : Revision state) (certificate : Certified revision)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalSaturationState.Models revision.result model)
    (slot : Fin state.context.state.base.slots) (old new : Descriptor state.context.state.base.slots)
    (before : state.context.state.nominals slot = some old)
    (after : revision.snapshot.nominals slot = some new) : old.arguments.length = new.arguments.length := by
  obtain ⟨xs,fitOld,oldEqual⟩ := (certificate.raw model valid.1).2.1 slot old before
  obtain ⟨ys,fitNew,newEqual⟩ := valid.1.2.1 slot new after
  have length := (CommonNominalFullCarrier.nominal_regular_invariant_exact _ _ _ _).mp
    (CommonNominalFullCarrier.subtype_trans oldEqual.2 newEqual.1) |>.2.1
  rw [GeneralNominalLinearMaterializationFacts.fitsAll_length _ _ _ _ fitOld,
    GeneralNominalLinearMaterializationFacts.fitsAll_length _ _ _ _ fitNew] at length
  exact length

theorem parameter_covered (revision : Revision state) (certificate : Certified revision)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalSaturationState.Models revision.result model)
    (slot : Fin state.context.state.base.slots) (old new : Descriptor state.context.state.base.slots)
    (before : state.context.state.nominals slot = some old)
    (after : revision.snapshot.nominals slot = some new)
    (index : Nat) (one : Parameter state.context.state.base.slots)
    (oldArg : old.arguments[index]? = some one) :
    ∃ two, new.arguments[index]? = some two ∧
      GeneralNominalIntervalLaws.ParameterChecks state.context.state.base model one two := by
  have bounded : index < old.arguments.length := (List.getElem?_eq_some_iff.mp oldArg).choose
  have current : index < new.arguments.length := by rw [← arity revision certificate model valid slot old new before after]; exact bounded
  refine ⟨new.arguments[index],List.getElem?_eq_getElem current,?_⟩
  exact GeneralDictionaryRevisionArgumentBridge.cross_checks revision certificate model valid slot old new before after index one _ oldArg (List.getElem?_eq_getElem current)
end Yulang.GeneralDictionaryRevisionParameterCoverage
