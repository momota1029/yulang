import Yulang.GeneralRebaseDepthReachableReadback286

/-! The two raw scalar observations may be recorded by one certified refresh.
Both placements of that batch, relative to the one install, are realized. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthBatch286
open GeneralDictionaryOutputDepth252 (roles root registry initial)
open GeneralRebaseDepthPreSharp286 (old target present previously_unknown new_zero new_one)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralRebaseDepthFullTrace286 (RefreshTrace)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralRebaseDepthPhase286 (Hop InstallHop)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthSchedule286 (Both Halted)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalState (Known)

theorem keeps (n : Nat) : Known old.state n → Known target.state n := by
  rintro ⟨slot,name,head|nominal⟩
  · exact (head rfl).elim
  · exact ⟨slot,name,Or.inr nominal⟩

noncomputable def pre_cert : Refresh initial target where
  refines := { (GeneralNominalRefinements.refl old.state) with known := keeps }
  interpretation := rfl
  support := fun _ member => member
  constraints := fun _ valid => ⟨valid.1.1.1,valid.1.1.2.2⟩
  cache := by
    intro obs recorded
    exact ⟨[],[],.source,.source,fun m _ valid =>
      GeneralCanonicalObservations.recorded_sound target.state m
        (GeneralRebaseDepthPreSharp286.from_source m valid.1) recorded⟩

noncomputable def prebatched := refresh initial target

theorem batch_first : Hop initial prebatched ∧ Both prebatched :=
  ⟨.refresh target pre_cert 0 (present 0 (by decide)) (previously_unknown 0 (by decide)) new_zero,
    new_zero,new_one⟩

theorem pre_batch_install :
    ∃ finish, Hop initial prebatched ∧ InstallHop prebatched finish ∧
      ActualPath initial finish 2 ∧ Halted finish := by
  have h := batch_first.1
  have seen : RefreshTrace initial prebatched 1 := .more (.empty _) h
  have linked := GeneralRebaseDepthFullTrace286.linked_after seen
  have pre := GeneralRebaseDepthEnableShape286.as_pre linked
  obtain ⟨finish,install⟩ := GeneralRebaseDepthPreAvailable286.offers linked
  have after := GeneralRebaseDepthPhase286.cross pre install
  have prior := batch_first.2
  exact ⟨finish,h,install,.more (GeneralRebaseDepthFullTrace286.real_refresh_trace seen)
    (GeneralRebaseDepthPhase286.as_step install),GeneralRebaseDepthSchedule286.halt_of_done after
      ⟨(GeneralRebaseDepthSchedule286.known_same_on_install pre install 0).mpr prior.1,
       (GeneralRebaseDepthSchedule286.known_same_on_install pre install 1).mpr prior.2⟩⟩

theorem install_post_batch :
    InstallHop initial GeneralDictionaryOutputDepthInstall252.installed ∧
      Hop GeneralDictionaryOutputDepthInstall252.installed GeneralRebaseDepthScalar285.refreshed ∧
      ActualPath initial GeneralRebaseDepthScalar285.refreshed 2 ∧
      Halted GeneralRebaseDepthScalar285.refreshed := by
  have action := GeneralRebaseDepthPhase286.pre_partition GeneralRebaseDepthPhase286.start
    GeneralDictionaryOutputDepthInstall252.step
  have hit : InstallHop initial GeneralDictionaryOutputDepthInstall252.installed := by
    rcases action with h | exactHit
    · exact ((GeneralRebaseDepthPhase286.exclusive (GeneralRebaseDepthPhase286.pre_refresh
        GeneralRebaseDepthPhase286.start h) GeneralRebaseDepthPhase286.installed_post)).elim
    · exact exactHit
  exact ⟨hit,.refresh GeneralRebaseDepthScalar285.target GeneralRebaseDepthScalar285.cert 0
    (GeneralRebaseDepthScalar285.present 0 (by decide)) (GeneralRebaseDepthScalar285.previously_unknown 0 (by decide))
    GeneralRebaseDepthScalar285.new_zero,GeneralRebaseDepthExactEnd286.short_maximal⟩

end Yulang.GeneralRebaseDepthBatch286
