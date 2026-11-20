import Yulang.GeneralRebaseDepthScalarMark286

/-! Both scalar sources remain available at every actual reachable state.
Certified refresh transports the trusted cache; the single install has a
source-exact raw snapshot, even though its full journal adds an output. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthScalarOffer286
open GeneralDictionaryOutputDepth252 (roles registry root initial)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedObservations233 (CacheSound)
open GeneralRebaseDepthScalarMark286 (Seed Atoms target)
open GeneralRebaseDepthPhase286 (Hop InstallHop Covered Pre)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralNominalState (Known)

private abbrev sourceSnapshot := GeneralDictionaryOutputDepth252.snapshot

structure Available (s : State roles) : Prop where
  source : s.core.erased.source.state = sourceSnapshot
  cache : CacheSound s (snapshot s)
  zero : Seed (snapshot s) 0
  one : Seed (snapshot s) 1

theorem start : Available initial := by
  refine ⟨rfl,GeneralRebaseDepthEnableSafety286.cache GeneralRebaseDepthEnableShape286.initial,?_,?_⟩
  · exact ⟨(0 : Fin 4),rfl,by decide +kernel,by decide +kernel⟩
  · exact ⟨(1 : Fin 4),rfl,by decide +kernel,by decide +kernel⟩

theorem along_refresh {s t : State roles} (before : Available s) (h : Hop s t) : Available t := by
  cases h with
  | refresh ctx cert _ _ _ _ =>
    exact ⟨before.source,GeneralRebaseDepthRefreshTrust286.retained cert,
      GeneralRebaseDepthScalarMark286.retains cert.refines before.zero,
      GeneralRebaseDepthScalarMark286.retains cert.refines before.one⟩

theorem along_install {s t : State roles} (before : Available s) (pre : Pre s)
    (h : InstallHop s t) : Available t := by
  cases h with
  | take e allowed rootEq _ =>
    let q := e.plan
    have v := GeneralRebaseDepthPreInstall286.installed_uses_certified pre.anchor pre.plan allowed rootEq
    refine ⟨before.source,?_,?_,?_⟩
    · intro o seen
      exact ⟨[],[],.source,.source,fun m _ valid => by
        have raw : GeneralNominalState.Models sourceSnapshot m := before.source ▸ valid.1
        have check := (GeneralRebaseDepthGroundModels285.source_inputs m).mp raw
        exact GeneralCanonicalObservations.recorded_sound _ m
          ((GeneralRebaseDepthCrossAnchor286.raw_check pre.anchor v m).mpr check) seen⟩
    · change Seed (GeneralNominalVersionedInstallation231.replayPlan q).packet.context.state 0
      exact GeneralRebaseDepthScalarMark286.retains (GeneralRebaseDepthCrossWitness286.replay_refines q)
        (v.frame.context_eq.symm ▸ before.zero)
    · change Seed (GeneralNominalVersionedInstallation231.replayPlan q).packet.context.state 1
      exact GeneralRebaseDepthScalarMark286.retains (GeneralRebaseDepthCrossWitness286.replay_refines q)
        (v.frame.context_eq.symm ▸ before.one)

theorem along_step {s t : State roles} (before : Available s) (covered : Covered s)
    (move : Step registry root s t) : Available t := by
  rcases covered with pre|post
  · rcases GeneralRebaseDepthPhase286.pre_partition pre move with refresh|install
    · exact along_refresh before refresh
    · exact along_install before pre install
  · exact along_refresh before (GeneralRebaseDepthPhase286.post_step post move)

theorem reached {s : State roles} {moves : Nat} (path : ActualPath initial s moves) :
    Available s := by
  induction path with
  | empty => exact start
  | more prior move ih =>
    exact along_step ih (GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) prior) move

theorem offers {s : State roles} (a : Available s) {n : Nat} (small : n ≤ 1)
    (missing : ¬ Known (snapshot s) n) : ∃ (slot : Fin (snapshot s).base.slots) (seed : Atoms (snapshot s) n slot),
      Hop s (GeneralNominalVersionedRefresh232.refresh s (target seed missing)) := by
  have seed : Seed (snapshot s) n := by
    have choice : n = 0 ∨ n = 1 := by omega
    rcases choice with rfl|rfl
    · exact a.zero
    · exact a.one
  obtain ⟨slot,atoms⟩ := seed
  exact ⟨slot,atoms,GeneralRebaseDepthScalarMark286.step atoms missing a.cache a.source small⟩

theorem hop_step {s t : State roles} (h : Hop s t) : Step registry root s t := by
  cases h with
  | refresh ctx cert n present old new =>
    exact ⟨root,.root,.refresh root ctx cert n present old new⟩

theorem halt_known {s : State roles} {moves : Nat} (path : ActualPath initial s moves)
    (halted : ∀ next, ¬ Step registry root s next) (n : Nat) (small : n ≤ 1) : Known (snapshot s) n := by
  apply Classical.byContradiction
  intro missing
  obtain ⟨_,_,hop⟩ := offers (reached path) small missing
  exact halted _ (hop_step hop)

end Yulang.GeneralRebaseDepthScalarOffer286
