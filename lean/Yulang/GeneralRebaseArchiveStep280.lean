import Yulang.GeneralRebaseArchiveGuards280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseArchiveStep280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Administrative At Step)
open GeneralNominalVersionedMixedObservations233 (Refresh Reobserve)
open GeneralNominalReobservationSteps (Revision)
open GeneralRebaseArchiveTrust280 (Correspond changeEffects archive cache_iff same_inputs_mono)
open GeneralRebaseArchiveGuards280 (models committed enabled)
open GeneralRebaseEffectSnapshot280 (ArchiveRelated EffectRelated)

variable {roles : Roles.RoleDecls} {s next : State roles} {ys : List (Effect roles)}

def refresh (pair : Correspond s.effects ys) (known : Refresh s context) :
    Refresh (changeEffects s ys) context :=
  ⟨known.refines,known.interpretation,known.support,
    fun m valid => known.constraints m (((archive s pair).models m).mpr valid),
    (cache_iff pair _).mp known.cache⟩

theorem reobserve (pair : Correspond s.effects ys)
    {revision : Revision s.core.erased.current} (known : Reobserve s revision) :
    Reobserve (changeEffects s ys) revision :=
  ⟨known.raw,(cache_iff pair _).mp known.cache⟩

theorem admin (pair : Correspond s.effects ys) (action : Administrative s focus next) :
    Administrative (changeEffects s ys) focus (changeEffects next ys) ∧
      ArchiveRelated next (changeEffects next ys) := by
  cases action with
  | enqueue linked absent =>
    exact ⟨.enqueue _ linked absent,archive _ pair⟩
  | refresh ctx certificate changed recorded none some =>
    exact ⟨.refresh _ ctx (refresh pair certificate) changed recorded none some,archive _ pair⟩
  | equate first last a b equal fresh =>
    exact ⟨.equate _ first last a b (fun m valid => equal m (((archive s pair).models m).mpr valid))
      fresh,archive _ pair⟩
  | reobserve rev certificate improves =>
    exact ⟨.reobserve (before := changeEffects s ys) _ rev (reobserve pair certificate) improves,archive _ pair⟩

theorem at_step (pair : Correspond s.effects ys) (action : At r s focus next) :
    ∃ newer, At r (changeEffects s ys) focus newer ∧ ArchiveRelated next newer := by
  cases action with
  | administrative step =>
    have got := admin pair step
    exact ⟨_,.administrative got.1,got.2⟩
  | refresh _ ctx certificate changed recorded none some =>
    exact ⟨_,.refresh _ ctx (refresh pair certificate) changed recorded none some,archive _ pair⟩
  | install eff support fresh =>
    exact ⟨_,.install eff ((enabled pair r eff).mp support) ((not_congr (committed pair _)).mp fresh),
      archive _ (pair.cons (EffectRelated.refl eff))⟩
  | merge first last a b equal notAlias =>
    exact ⟨_,.merge first last a b (same_inputs_mono
      (fun m valid => ((archive s pair).models m).mpr valid) equal) notAlias,archive _ pair⟩

theorem step (pair : Correspond s.effects ys) (action : Step r root s next) :
    ∃ newer, Step r root (changeEffects s ys) newer ∧ ArchiveRelated next newer := by
  obtain ⟨focus,generated,atFocus⟩ := action
  obtain ⟨newer,valid,rel⟩ := at_step pair atFocus
  exact ⟨newer,⟨focus,generated,valid⟩,rel⟩

end Yulang.GeneralRebaseArchiveStep280
