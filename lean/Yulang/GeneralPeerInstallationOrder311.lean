import Yulang.GeneralNominalVersionedMixedKernel234
import Yulang.GeneralNominalVersionedMixedGrowth234

set_option backward.isDefEq.respectTransparency false
/-! A previously installed peer can join a class later, but an equal and
registered peer cannot be ignored during installation. This is a guard law,
not a scheduling or termination claim. -/
namespace Yulang.GeneralPeerInstallationOrder311
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalSaturationState (Alias)
variable {roles : Roles.RoleDecls} {before : State roles} {effect : Effect roles}

theorem administrative (enabled : Installable registry before effect) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady before effect.plan.packet.site.occurrence := by
  classical
  apply Classical.byContradiction
  intro wrong
  exact enabled.safe.2.2.2 (.inr wrong)

theorem registered_peer_alias (enabled : Installable registry before effect)
    {first last : Site roles}
    (a : first ∈ before.core.sites) (b : last ∈ before.core.sites)
    (owner : first.occurrence = effect.plan.packet.site.occurrence)
    (equal : SameInputs (Models before) first last) :
    Alias before.core.erased.current first.occurrence.identity last.occurrence.identity :=
  (administrative enabled).2 first a owner last b equal

theorem no_install_before_join (a : first ∈ before.core.sites) (b : last ∈ before.core.sites)
    (owner : first.occurrence = effect.plan.packet.site.occurrence)
    (equal : SameInputs (Models before) first last)
    (notYet : ¬ Alias before.core.erased.current first.occurrence.identity last.occurrence.identity) :
    ¬ Installable registry before effect :=
  fun enabled => notYet (registered_peer_alias enabled a b owner equal)

end Yulang.GeneralPeerInstallationOrder311
