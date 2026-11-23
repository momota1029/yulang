import Yulang.GeneralDeclarativeWitnessForwardModel360
import Yulang.GeneralDeclarativeWitnessNestedOrdered360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessBranchFootprint360
open GeneralDeclarativeWitnessNestedOrdered360 (finalStage)
open GeneralDeclarativeWitnessForwardModel360 (state model fitting_forwarding_state)
open GeneralDeclarativeWitnessRecordWidthFixture359 (lowTy lowRest)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Row Equivalent Subtype subtype_trans observeTy record)
open CommonNominalFullDemand (ProbeAt Environment producerLe_iff_probe)
open PresenceNormalForm (Atom)

def link (a b : Nat) : Atom Nat := .tyLe (.var a) (.var b)

theorem independent_allocations_overlap (m : Assignment)
    (first : Models finalStage m) (later : Models state m) :
    Equivalent (m 106).1 (m 101).1 := by
  have fromFirst := first.1.1 (link 106 110) (by decide +kernel)
  have intoFirst := first.1.1 (link 110 106) (by decide +kernel)
  have fromLater := later.1.1 (link 101 110) (by decide +kernel)
  have intoLater := later.1.1 (link 110 101) (by decide +kernel)
  exact ⟨subtype_trans fromFirst intoLater,subtype_trans fromLater intoFirst⟩

private def small : Environment Row := ⟨fun _ => .bottom,fun _ => []⟩

theorem record_source_not_int : ¬ Subtype lowTy (.base .int) := by
  intro bad
  have observed : ProbeAt Common.rowLe 0 small (observeTy 1 (.base .int)) (.base .int) := by
    simp [ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep,
      observeTy,CommonNominalSyntax.Layer.evalAt]
  have wrong := (producerLe_iff_probe _ _).mp (bad 1) 0 small (.base .int) observed
  simp [lowTy,record,observeTy,CommonNominalSyntax.Layer.evalAt,ProbeAt,
    CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at wrong

/-- Independent previews can reuse numeric aliases. These two concrete
paths do not share the same allocation snapshot, so do not union their
ordinary constraints; recompile any later path after the earlier one. -/
theorem no_naive_union_of_previews :
    Models state (model false .int) ∧ ¬ Models finalStage (model false .int) := by
  have actual := fitting_forwarding_state false .int
  refine ⟨actual,fun conflicted => ?_⟩
  exact record_source_not_int (independent_allocations_overlap _ conflicted actual).1

end Yulang.GeneralDeclarativeWitnessBranchFootprint360
