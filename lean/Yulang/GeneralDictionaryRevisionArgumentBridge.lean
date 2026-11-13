import Yulang.GeneralNominalReobservationSteps
import Yulang.GeneralNominalProjections

/-! A semantic bridge where descriptor-preserving Refines is unavailable.
A retained nominal origin has a common actual argument fitting both old and new
intervals. Endpoint/source-ID equality is deliberately not asserted. This does
not yet transport a whole recursive Report or its emitted children. -/
namespace Yulang.GeneralDictionaryRevisionArgumentBridge
open GeneralNominalReobservationSteps GeneralNominalProjections
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}

theorem descriptor_name (revision : Revision state) (certificate : Certified revision)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalSaturationState.Models revision.result model)
    (slot : Fin state.context.state.base.slots)
    (old new : GeneralNominalState.Descriptor state.context.state.base.slots)
    (before : state.context.state.nominals slot = some old)
    (after : revision.snapshot.nominals slot = some new) :
    old.declaration.name = new.declaration.name := by
  obtain ⟨xs,_,oldEqual⟩ := (certificate.raw model valid.1).2.1 slot old before
  obtain ⟨ys,_,newEqual⟩ := valid.1.2.1 slot new after
  exact (CommonNominalFullCarrier.nominal_regular_invariant_exact _ _ _ _).mp
    (CommonNominalFullCarrier.subtype_trans oldEqual.2 newEqual.1) |>.1

theorem shared_argument (revision : Revision state) (certificate : Certified revision)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalSaturationState.Models revision.result model)
    (slot : Fin state.context.state.base.slots)
    (old new : GeneralNominalState.Descriptor state.context.state.base.slots)
    (before : state.context.state.nominals slot = some old)
    (after : revision.snapshot.nominals slot = some new)
    (index : Nat) (one two : GeneralNominalState.Parameter state.context.state.base.slots)
    (oldArg : old.arguments[index]? = some one) (newArg : new.arguments[index]? = some two) :
    ∃ value, Observes model (.argument (.source (state.context.state.base.source slot)) old.declaration.name index) value ∧
      GeneralNominalState.Fits state.context.state.base model one value ∧
      GeneralNominalState.Fits state.context.state.base model two value := by
  have sameName := descriptor_name revision certificate model valid slot old new before after
  obtain ⟨x,seen,first⟩ := parameter_binding_valid state.context.state model
    (certificate.raw model valid.1) slot old before index 0 one oldArg
  obtain ⟨y,observed,last⟩ := parameter_binding_valid revision.snapshot model
    valid.1 slot new after index 0 two newArg
  change Observes model (.argument (.source (state.context.state.base.source slot)) old.declaration.name index) x at seen
  change Observes model (.argument (.source (state.context.state.base.source slot)) new.declaration.name index) y at observed
  rw [← sameName] at observed
  have equal := observation_unique model _ x y seen observed
  refine ⟨y,observed,?_,last⟩
  exact (GeneralNominalIntervalLaws.fits_equivalent _ _ _ _ _ equal).mp first

theorem cross_checks (revision : Revision state) (certificate : Certified revision)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalSaturationState.Models revision.result model)
    (slot : Fin state.context.state.base.slots)
    (old new : GeneralNominalState.Descriptor state.context.state.base.slots)
    (before : state.context.state.nominals slot = some old)
    (after : revision.snapshot.nominals slot = some new)
    (index : Nat) (one two : GeneralNominalState.Parameter state.context.state.base.slots)
    (oldArg : old.arguments[index]? = some one) (newArg : new.arguments[index]? = some two) :
    GeneralNominalIntervalLaws.ParameterChecks state.context.state.base model one two := by
  obtain ⟨value,_,first,last⟩ := shared_argument revision certificate model valid slot old new before after index one two oldArg newArg
  exact GeneralNominalIntervalLaws.fits_checks _ _ _ _ value first last
end Yulang.GeneralDictionaryRevisionArgumentBridge
