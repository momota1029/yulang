import Yulang.GeneralRebaseFiniteCodeBoundary277
import Yulang.GeneralDictionaryVersionLoopInstall239
import Yulang.GeneralRebaseRoundProjection265

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 10000000
namespace Yulang.Cycle277OwnerKeyObstruction
open GeneralDictionaryVersionLoopSource237 (sourceRegistry roles root)
open GeneralDictionaryVersionLoopBook239 (plan)
open GeneralDictionaryVersionLoopIteration239 (stages state)
open GeneralDictionaryVersionLoopInstall239 (chosen installable)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)

def ownerKey (p : Plan roles) : Nat × Nat :=
  (p.packet.site.occurrence.identity,p.packet.declaration.id)

theorem repeated_owner_not_absorbed :
    ∃ s : State roles, ∃ old : Plan roles, ∃ next : Effect roles,
      Reachable sourceRegistry root s ∧ old ∈ s.plans ∧
      Installable (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) s next ∧
      ownerKey old = ownerKey next.plan ∧ ¬ Committed s next.plan := by
  let stage := stages 1
  exact ⟨stage.state,plan 0,chosen stage.shape,stage.reachable,stage.recorded 0 (by decide),
    installable stage.shape stage.valid stage.recorded,rfl,GeneralDictionaryVersionLoopStage239.novel stage⟩

theorem repeated_owner_every_round (n : Nat) :
    (plan n) ∈ (state (n+1)).plans ∧
    ownerKey (plan n) = ownerKey (plan (n+1)) ∧
    ¬ Committed (state (n+1)) (plan (n+1)) := by
  let stage := stages (n+1)
  exact ⟨stage.recorded n (Nat.lt_succ_self n),rfl,GeneralDictionaryVersionLoopStage239.novel stage⟩

theorem stabilized_projection_not_absorption (owners : List Nat) (pool : List GeneralSourceState.Output) :
    ∃ N, ∀ n ≥ N,
      GeneralRebaseLiveProjection264.project owners pool (state (n+2)) =
        GeneralRebaseLiveProjection264.project owners pool (state (n+1)) ∧
      ownerKey (plan n) = ownerKey (plan (n+1)) ∧
      ¬ Committed (state (n+1)) (plan (n+1)) := by
  obtain ⟨N,stable,_⟩ := GeneralRebaseRoundProjection265.version239 owners pool
  refine ⟨N,fun n ready => ⟨?_,(repeated_owner_every_round n).2⟩⟩
  exact (stable (n+2) (by omega)).trans (stable (n+1) (by omega)).symm

#print axioms repeated_owner_not_absorbed
#print axioms stabilized_projection_not_absorption
end Yulang.Cycle277OwnerKeyObstruction
