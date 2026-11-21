import Yulang.GeneralVersionedAliasReport312
import Yulang.GeneralVersionedProtectedLookup312

set_option backward.isDefEq.respectTransparency false
/-! Actual checked source traces discharge all historical-choice feasibility
except protected aggregate support. In particular no comparison of old and
current read lists is needed; real refresh and merge remain in the trace. -/
namespace Yulang.GeneralVersionedAliasChoice312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoricalTransport312 (atFocus Transfer)
open GeneralVersionedProtectedPeer312 (semanticPool)
open GeneralNominalSaturationState (Packet Alias)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedPeerChoice311 (reads)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {root focus : Occurrence roles} {m : Assignment}

def Coverage (registry : Registry) (state : State roles) (focus : Occurrence roles)
    (decl : Declaration) : Prop :=
  ∀ proof : DeclarationChecked (Compiled registry).constructors roles decl,
  ∀ bounds, reads state.core.erased.current.context focus = some bounds →
    let p := atFocus state registry focus decl proof bounds
    IdCovered (semanticPool p) state p

theorem transfer
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (selected : Local registry state focus (.selected key children))
    (valid : Models state m)
    {prior : Packet roles} (stored : prior ∈ state.core.erased.current.packets)
    (alias : Alias state.core.erased.current focus.identity prior.site.occurrence.identity)
    (coverage : Coverage registry state focus prior.declaration) :
    Transfer registry state focus prior.declaration m := by
  intro proof bounds locate
  let p := atFocus state registry focus prior.declaration proof bounds
  obtain ⟨current,frame,_⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
  let prospective : Plan roles := ⟨p,current.input,current.input_exact.trans frame.occurrence_eq⟩
  obtain ⟨historical,member,packetEq⟩ := GeneralNominalVersionedMixedChoiceHistory236.packet_plan path stored
  have aliasActual : Alias state.core.erased.current
      prospective.packet.site.occurrence.identity historical.packet.site.occurrence.identity := by
    rw [packetEq]
    exact alias
  have meaning := GeneralVersionedAliasReport312.from_alias checked path historical prospective member frame.center_recorded
    rfl locate aliasActual (congrArg Packet.declaration packetEq).symm m valid
  exact ⟨meaning.1,meaning.2,coverage proof bounds locate⟩

theorem choice {packet : Packet roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (selected : Local registry state packet.site.occurrence (.selected packet.declaration.id children))
    (inhabited : ∃ m, Models state m)
    (coverage : ∀ prior ∈ state.core.erased.current.packets,
      Alias state.core.erased.current packet.site.occurrence.identity prior.site.occurrence.identity →
      Coverage registry state packet.site.occurrence prior.declaration) :
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current packet := by
  obtain ⟨m,valid⟩ := inhabited
  apply GeneralVersionedHistoricalTransport312.choice checked path selected valid
  intro prior stored alias
  exact transfer checked path selected valid stored alias (coverage prior stored alias)

theorem coverage_from_check
    (passes : ∀ checked bounds, reads state.core.erased.current.context focus = some bounds →
      let p := atFocus state registry focus decl checked bounds
      GeneralVersionedProtectedLookup312.verify (semanticPool p) state p = true) :
    Coverage registry state focus decl := by
  intro checked bounds located
  exact (GeneralVersionedProtectedLookup312.verify_iff ..).mp (passes checked bounds located)

end Yulang.GeneralVersionedAliasChoice312
