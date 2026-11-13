import Yulang.GeneralDictionaryInstallationOrigin
import Yulang.GeneralNominalValueBoundary

/-! The old inspection facts are consequences of actual packet installation,
not assumptions added to current-state dictionary evidence. -/
namespace Yulang.GeneralDictionaryRecordedInspectionFacts
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
variable {roles : Roles.RoleDecls}

theorem prepared (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) :
    Prepared packet.registry packet.context packet.site.occurrence packet.declaration packet.checked := by
  have formed := GeneralNominalDownstreamSteps.formed_old (GeneralNominalValueSteps.formed_old
    (GeneralNominalValueBoundary.reachable_formed packet.registry state root reachable))
  obtain ⟨_,_,_,_,enabled,_⟩ := GeneralDictionaryInstallationOrigin.packet_origin packet.registry root state formed packet recorded
  exact enabled.1.2.2.2.2.2.2.1

theorem located (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) :
    arguments packet.context packet.site.occurrence = some packet.bounds := by
  have formed := GeneralNominalDownstreamSteps.formed_old (GeneralNominalValueSteps.formed_old
    (GeneralNominalValueBoundary.reachable_formed packet.registry state root reachable))
  obtain ⟨_,_,_,_,enabled,_⟩ := GeneralDictionaryInstallationOrigin.packet_origin packet.registry root state formed packet recorded
  exact enabled.1.2.2.2.2.2.1

theorem role (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) :
    packet.declaration.role = packet.site.occurrence.demand.role := by
  have formed := GeneralNominalDownstreamSteps.formed_old (GeneralNominalValueSteps.formed_old
    (GeneralNominalValueBoundary.reachable_formed packet.registry state root reachable))
  obtain ⟨_,_,_,_,enabled,_⟩ := GeneralDictionaryInstallationOrigin.packet_origin packet.registry root state formed packet recorded
  exact enabled.1.2.2.2.2.1

theorem finished (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) : Finished (report packet.context packet.declaration packet.bounds) := by
  obtain ⟨_,_,_,bounds,found,done,_⟩ := prepared packet root state reachable recorded
  have equal := Option.some.inj (found.symm.trans (located packet root state reachable recorded))
  subst bounds
  exact done

theorem root_defined (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) : GeneralNominalMaterialization.RootDefined packet.declaration packet.site.occurrence := by
  obtain ⟨_,_,_,_,_,_,ready,_⟩ := prepared packet root state reachable recorded
  exact ready.1

theorem metadata (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) : Metadata packet.registry packet.context :=
  (prepared packet root state reachable recorded).1
end Yulang.GeneralDictionaryRecordedInspectionFacts
