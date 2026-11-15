import Yulang.GeneralDictionaryDefaultGrowth208
import Yulang.GeneralNominalCenteredHeadMatStepCache

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultCache208
open GeneralNominalCenteredHeadMatStepJournal (State initial)
open GeneralNominalCenteredHeadMatStepObservations
open GeneralCanonicalObservations (Observation Recorded)
variable {roles : Roles.RoleDecls} {before after : State roles}

def Valid (state : State roles) : Prop := CacheSound state state.core.erased.current.context.state

theorem recorded_extend (recorded : Recorded (GeneralNominalState.extend snapshot reserved atoms) observation) :
    Recorded snapshot observation := by
  cases recorded with
  | scalar slot base same => exact Recorded.scalar (snapshot := snapshot) slot base same
  | structural slot kind children same => exact Recorded.structural (snapshot := snapshot) slot kind children same
  | nominal slot descriptor same => exact Recorded.nominal (snapshot := snapshot) slot descriptor same

theorem recorded_private (packet : GeneralNominalSaturationState.Packet roles)
    (recorded : Recorded packet.privateContext.state observation) : Recorded packet.context.state observation := by
  cases recorded with
  | scalar slot base same => exact Recorded.scalar (snapshot := packet.context.state) slot base same
  | structural slot kind children same => exact Recorded.structural (snapshot := packet.context.state) slot kind children same
  | nominal slot descriptor same => exact Recorded.nominal (snapshot := packet.context.state) slot descriptor same

theorem administrative (action : GeneralDictionaryDefaultKernel208.Administrative before focus after)
    (valid : Valid before) : Valid after := by
  apply GeneralNominalCenteredHeadMatStepTrustedGrowth.cache
    (GeneralDictionaryDefaultGrowth208.administrative action)
  cases action with
  | enqueue linked absent => exact valid
  | refresh context certificate source member unknown known => exact certificate.cache
  | reobserve revision certificate improved => exact certificate.cache
  | equate first last one two equal novel =>
      exact fun observation recorded => valid observation (recorded_extend recorded)

theorem at_cache (action : GeneralDictionaryDefaultKernel208.At registry before focus after)
    (valid : Valid before) : Valid after := by
  cases action with
  | administrative action => exact administrative action valid
  | refresh focus context certificate source member unknown known =>
      exact administrative (.refresh focus context certificate source member unknown known) valid
  | install effect enabled novel =>
      apply GeneralNominalCenteredHeadMatStepTrustedGrowth.cache
        (GeneralDictionaryDefaultGrowth208.at_growth (.install effect enabled novel))
      intro observation recorded
      have old := recorded_private effect.plan.packet recorded
      have context := effect.frame.context_eq.trans (congrArg (fun state => state.erased.current.context) enabled.snapshot_eq)
      exact valid observation (context ▸ old)
  | merge first last one two same novel =>
      apply GeneralNominalCenteredHeadMatStepTrustedGrowth.cache
        (GeneralDictionaryDefaultGrowth208.at_growth (registry := registry) (.merge first last one two same novel))
      exact fun observation recorded => valid observation (recorded_extend recorded)

theorem step_cache (action : GeneralDictionaryDefaultKernel208.Step registry root before after)
    (valid : Valid before) : Valid after := at_cache action.choose_spec.2 valid

theorem steps_cache (path : B4Target.Steps (GeneralDictionaryDefaultKernel208.Step registry root) before after)
    (valid : Valid before) : Valid after := by
  induction path with
  | refl => exact valid
  | tail _ action ih => exact step_cache action ih

theorem initial_valid (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles) :
    Valid (initial context root) := initial_cache context root

end Yulang.GeneralDictionaryDefaultCache208
