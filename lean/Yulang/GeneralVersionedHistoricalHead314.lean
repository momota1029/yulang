import Yulang.GeneralVersionedAggregateJournal314
import Yulang.GeneralVersionedPrivateJournal314

set_option backward.isDefEq.respectTransparency false
/-! General producer for the selected centered head in one live mixed
model. Previously installed numerical owners reuse exact address-level
aggregate equations and the actual binder producer; new owners use
source exclusion. This is not a child/output/write-safety assertion. -/
namespace Yulang.GeneralVersionedHistoricalHead314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Alias)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralVersionedSemanticPeer312 (Sufficient)

theorem declaration {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p)
    (valid : Models s m)
    (stored : q ∈ s.plans)
    (same : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity) :
    q.packet.declaration = p.packet.declaration := by
  have record : q.packet ∈ s.core.erased.current.packets := by
    rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2]
    exact List.mem_map.mpr ⟨q,stored,rfl⟩
  have oldKey := GeneralVersionedSameOwnerChoice314.key_eq checked actual selected valid record
    (same.trans (congrArg (fun o : Occurrence roles => o.identity) frame.occurrence_eq))
  exact GeneralDictionaryEmissionPlans.declaration_key_unique _
    (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2 _ _
    (GeneralNominalVersionedMixedChoiceHistory236.visible actual record) frame.visible
    (oldKey.trans frame.key_eq.symm)

theorem ledger {s : State roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p)
    (valid : Models s m) :
    IdCovered (GeneralVersionedSemanticPeer312.protectedPool p.packet (sources s)) s p.packet := by
  apply GeneralVersionedAggregateJournal314.full_support checked actual frame.context_eq frame.visible
  intro past member owner
  exact congrArg Declaration.id (declaration checked actual selected frame valid member owner)

theorem of_history {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (same : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (inhabited : ∃ m, Models s m) :
    ∃ m, Models s m ∧ HeadEquations p m := by
  obtain ⟨m,valid⟩ := inhabited
  have sameRule := (declaration checked actual selected frame valid stored same).symm
  have alias : Alias s.core.erased.current p.packet.site.occurrence.identity q.packet.site.occurrence.identity :=
    same.symm ▸ Alias.refl _
  have read := (GeneralVersionedAliasReport312.from_alias checked actual q p stored frame.center_recorded
    frame.context_eq (frame.occurrence_eq.symm ▸ frame.located) alias sameRule m valid).2
  have sup := GeneralNominalVersionedModelSupport237.current s
  have adequate : Sufficient s p.packet := ⟨sources s,sup,ledger checked actual selected frame valid⟩
  obtain ⟨n,live,head⟩ := GeneralVersionedSemanticPeer312.full_head_of_trace actual frame.context_eq
    valid read adequate
  have selfFrame : Frame (Compiled registry) s.core p.packet.site.occurrence p.packet.declaration.id p :=
    frame.occurrence_eq.symm ▸ frame.key_eq.symm ▸ frame
  obtain ⟨coherent,protectedRows⟩ := GeneralVersionedBinderTable312.certified checked actual selfFrame
    stored alias sameRule
    (GeneralVersionedBinderReuse312.reused checked actual stored alias sameRule
      (GeneralVersionedPrivateJournal314.owned checked actual frame)) n live head
  obtain ⟨liveFinal,_,held⟩ := GeneralVersionedAliasHeadWrites312.complete checked actual selfFrame
    stored alias sameRule sup n live head coherent protectedRows
  exact ⟨_,liveFinal,held⟩

theorem head {s : State roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p)
    (inhabited : ∃ m, Models s m) :
    ∃ m, Models s m ∧ HeadEquations p m := by
  classical
  by_cases old : ∃ q ∈ s.plans, q.packet.site.occurrence.identity = p.packet.site.occurrence.identity
  · obtain ⟨q,stored,same⟩ := old
    exact of_history checked actual selected frame stored same inhabited
  · have unseen : GeneralVersionedUnseenBinder313.Unseen s p :=
      fun q stored same => old ⟨q,stored,same⟩
    exact GeneralVersionedNewOwnerHead314.head checked actual selected frame unseen inhabited

end Yulang.GeneralVersionedHistoricalHead314
