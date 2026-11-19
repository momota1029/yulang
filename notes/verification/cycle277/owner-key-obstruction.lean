import Yulang.GeneralRebaseFiniteCodeBoundary277
import Yulang.GeneralDictionaryVersionLoopInstall239

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 10000000
namespace Yulang.Cycle277OwnerKeyObstruction
open GeneralDictionaryVersionLoopSource237 (sourceRegistry roles root)
open GeneralDictionaryVersionLoopBook239 (plan)
open GeneralDictionaryVersionLoopIteration239 (stages)
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

#print axioms repeated_owner_not_absorbed
end Yulang.Cycle277OwnerKeyObstruction
