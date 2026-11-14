import Yulang.GeneralDictionaryAgreedEvidence174
/-! Ordinary-extension history is incompatible with genuine observation progress
once a packet has been recorded. These are conditional shape obstructions,
not counterexamples to source Evidence, B4, or existence of a reachable refresh.
The old invariant plus one recorded packet and an improving operation imply
failure of that invariant afterwards; semantic transport needs another invariant. -/
namespace Yulang.GeneralDictionaryAgreedHistoryObstruction174
open GeneralDictionaryOrdinaryTrace

theorem extension_known (growth : Extension before after) (source : Nat) :
    GeneralNominalState.Known after.state source ↔ GeneralNominalState.Known before.state source := by
  obtain ⟨rs, ats, ks, rfl⟩ := growth
  rfl

theorem refresh_not_extension
    (unknown : ¬ GeneralNominalState.Known before.state source)
    (known : GeneralNominalState.Known after.state source) : ¬ Extension before after := by
  intro growth
  exact unknown ((extension_known growth source).mp known)

theorem historical_refresh_not_extension
    (old : Extension history before)
    (unknown : ¬ GeneralNominalState.Known before.state source)
    (known : GeneralNominalState.Known after.state source) : ¬ Extension history after := by
  intro fresh
  exact unknown ((extension_known old source).mpr ((extension_known fresh source).mp known))

def PointIndex (context : GeneralNominalCandidates.Context) (index : Nat) : Prop :=
  ∃ slot : Fin context.state.base.slots, slot.val = index ∧
    GeneralNominalReobservationSteps.PointAt context.state slot

theorem extension_point (growth : Extension before after) (index : Nat) :
    PointIndex after index ↔ PointIndex before index := by
  obtain ⟨rs, ats, ks, rfl⟩ := growth
  rfl

theorem revision_not_extension {roles : Roles.RoleDecls}
    {state : GeneralNominalSaturationState.State roles}
    (revision : GeneralNominalReobservationSteps.Revision state)
    (improved : GeneralNominalReobservationSteps.Improves revision) :
    ¬ Extension state.context revision.result.context := by
  intro growth
  obtain ⟨_, slot, notPoint, isPoint⟩ := improved
  have newPoint : PointIndex revision.result.context slot.val := ⟨slot,rfl,isPoint⟩
  obtain ⟨oldSlot, same, oldPoint⟩ := (extension_point growth slot.val).mp newPoint
  have slotSame : oldSlot = slot := Fin.ext same
  exact notPoint (slotSame ▸ oldPoint)

theorem historical_revision_not_extension {roles : Roles.RoleDecls}
    {state : GeneralNominalSaturationState.State roles}
    (old : Extension history state.context)
    (revision : GeneralNominalReobservationSteps.Revision state)
    (improved : GeneralNominalReobservationSteps.Improves revision) :
    ¬ Extension history revision.result.context := by
  intro growth
  obtain ⟨_, slot, notPoint, isPoint⟩ := improved
  have newPoint : PointIndex revision.result.context slot.val := ⟨slot,rfl,isPoint⟩
  have oldPoint := (extension_point old slot.val).mpr ((extension_point growth slot.val).mp newPoint)
  obtain ⟨oldSlot, same, oldPoint⟩ := oldPoint
  have slotSame : oldSlot = slot := Fin.ext same
  exact notPoint (slotSame ▸ oldPoint)

theorem recorded_refresh_failure {roles : Roles.RoleDecls}
    (state : GeneralNominalSupport.Tracked roles)
    (old : GeneralDictionaryAgreedEvidence174.RecordedExtensions state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.current.packets)
    (context : GeneralNominalCandidates.Context) (source : Nat)
    (unknown : ¬ GeneralNominalState.Known state.current.context.state source)
    (known : GeneralNominalState.Known context.state source) :
    ¬ GeneralDictionaryAgreedEvidence174.RecordedExtensions
      {state with current := GeneralNominalSaturationState.regenerate state.current context} := by
  intro fresh
  exact historical_refresh_not_extension (old packet member) unknown known (fresh packet member)

theorem recorded_revision_failure {roles : Roles.RoleDecls}
    (state : GeneralNominalSupport.Tracked roles)
    (old : GeneralDictionaryAgreedEvidence174.RecordedExtensions state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.current.packets)
    (revision : GeneralNominalReobservationSteps.Revision state.current)
    (improved : GeneralNominalReobservationSteps.Improves revision) :
    ¬ GeneralDictionaryAgreedEvidence174.RecordedExtensions
      {state with current := revision.result} := by
  intro fresh
  exact historical_revision_not_extension (old packet member) revision improved (fresh packet member)

end Yulang.GeneralDictionaryAgreedHistoryObstruction174
