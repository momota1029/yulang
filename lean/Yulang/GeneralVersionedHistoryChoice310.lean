import Yulang.GeneralVersionedRecursiveBridge310
import Yulang.GeneralNominalVersionedMixedChoice236
import Yulang.GeneralNominalVersionedPreparedTransport231

set_option backward.isDefEq.respectTransparency false
/-! An actual historical packet can justify compatibility with a current
selection through its recorded frame, when its original occurrence and
allocated keys still match the supplied ordinary extension. No promise is
made about aliasing different historical occurrences or refreshed semantics. -/
namespace Yulang.GeneralVersionedHistoryChoice310
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedCandidates231 (Prepared HeadModels)
open GeneralNominalVersionedTransport231 (extendedPlan extendedPacket)
open GeneralDictionaryOrdinaryTransport (extend)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalSaturationState (Alias Packet)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {registry : Registry} {s : State roles}
  {root focus : Occurrence roles} {m : Assignment}

theorem historical_effect
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    {prior : Packet roles} (member : prior ∈ s.core.erased.current.packets) :
    ∃ stored ∈ s.effects, stored.plan.packet = prior := by
  obtain ⟨old,seen,rfl⟩ := GeneralNominalVersionedMixedChoiceHistory236.packet_plan path member
  have synced := (GeneralNominalVersionedMixedPlanLedger235.reachable path).1
  rw [synced] at seen
  obtain ⟨effect,inside,same⟩ := List.mem_map.mp seen
  exact ⟨effect,inside,congrArg Plan.packet same⟩

def OrdinaryOwner (s : State roles) (prior : Packet roles) (focus : Occurrence roles) : Prop :=
  prior.site.occurrence = focus ∧
    ∃ rs ats allocated, s.core.erased.current.context = extend prior.context rs ats allocated ∧
      GeneralNominalVersionedAllocation231.keys prior.registry focus.identity prior.bindings ⊆ allocated

theorem historical_prepared
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    {prior : Packet roles} (member : prior ∈ s.core.erased.current.packets)
    (matching : OrdinaryOwner s prior focus) (valid : Models s m) :
    Prepared (Compiled registry) s.core.erased.current.context focus prior.declaration := by
  obtain ⟨effect,logged,rfl⟩ := historical_effect path member
  obtain ⟨occ,rs,ats,owned,current,allocated⟩ := matching
  have recRegistry := (GeneralNominalVersionedMixedRegistry234.reachable path).2.2 effect logged
  have fr := effect.frame
  have regEq := fr.registry_eq.trans recRegistry
  have fresh : GeneralNominalVersionedAllocation231.keys (Compiled registry) focus.identity effect.plan.packet.bindings ⊆ owned := by
    simpa only [regEq] using allocated
  have previous : Prepared (Compiled registry) effect.plan.packet.context focus effect.plan.packet.declaration :=
by
    have old := fr.prepared
    rw [← fr.context_eq,recRegistry,occ] at old
    exact old
  have fits : GeneralNominalRecursiveCandidates.arguments effect.plan.packet.context
      (GeneralNominalVersionedCandidates231.inputs focus) = some effect.plan.packet.bounds :=
    occ ▸ fr.located
  have committed := GeneralNominalVersionedMixedReplay237.extended_committed rs ats owned effect.plan
    (GeneralNominalVersionedMixedHistory235.committed path logged) current.symm
  have live := GeneralNominalVersionedPlans231.head_models (committed.1 m valid).1
  have head := (GeneralNominalVersionedCandidates231.headModels_packet_iff
    (extendedPacket rs ats owned effect.plan.packet) m).mpr live
  change HeadModels effect.plan.packet.registry (extend effect.plan.packet.context rs ats owned)
    effect.plan.packet.site.occurrence effect.plan.packet.declaration effect.plan.packet.bounds m at head
  rw [regEq,occ] at head
  rw [current]
  exact GeneralNominalVersionedPreparedTransport231.prepared_extended rs ats owned effect.plan.packet.context
    (Compiled registry) focus effect.plan.packet.declaration effect.plan.packet.bounds previous fits fresh ⟨m,head⟩

theorem choice_of_rechecked_history
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    {packet : Packet roles}
    (selected : Local registry s packet.site.occurrence (.selected packet.declaration.id children))
    (valid : Models s m)
    (overlap : ∀ prior ∈ s.core.erased.current.packets,
      Alias s.core.erased.current packet.site.occurrence.identity prior.site.occurrence.identity →
        OrdinaryOwner s prior packet.site.occurrence) :
    GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current packet := by
  apply (GeneralNominalVersionedMixedChoice236.choice_iff_prepared checked path selected).mpr
  intro prior member overlapAlias
  exact historical_prepared path member (overlap prior member overlapAlias) valid

end Yulang.GeneralVersionedHistoryChoice310
