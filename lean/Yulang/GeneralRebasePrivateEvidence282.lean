import Yulang.GeneralRebasePrivateJournal282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePrivateEvidence282
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralRebasePrivateJournal282 (AgreeOutside Hidden)
open GeneralRebasePrivateTrace282 (frame_safe)
open GeneralRebasePrivatePacket282 (Safe sources_private)
open GeneralRebasePrivateClass282 (body_private)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence Instance)
open GeneralDictionaryDefaultEvidence204 (OutputWitness)
open GeneralDictionaryReadback (Payload)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem packet_iff (reach : Reachable registry root state) {q : Plan roles}
    (frame : Frame r state.core focus key q) {x y : Assignment}
    (agrees : AgreeOutside (raw state).seed x y) :
    GeneralNominalVersionedPlans231.Holds q x ↔ GeneralNominalVersionedPlans231.Holds q y := by
  apply GeneralNominalVersionedPacketFrame236.holds_iff
  intro name found
  apply agrees name
  rintro ⟨o,d,tag,rfl⟩
  have impossible := sources_private (frame_safe reach frame o d tag)
  have seed := congrArg (fun ctx : GeneralNominalCandidates.Context => ctx.state.seed) frame.context_eq
  exact impossible (seed.symm ▸ found)

theorem output_iff (reach : Reachable registry root state) {q : Plan roles}
    (frame : Frame r state.core focus key q) {x y : Assignment}
    (agrees : AgreeOutside (raw state).seed x y) (output : GeneralSourceState.Output)
    (listed : output ∈ focus.demand.outputs) :
    OutputWitness q x output ↔ OutputWitness q y output := by
  unfold OutputWitness
  apply exists_congr
  intro body
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply GeneralDictionaryDefault214ActualBodyFrame.body_iff
  intro name found
  apply agrees name
  rintro ⟨o,d,tag,rfl⟩
  have safe := frame_safe reach frame o d tag
  have seed := congrArg (fun ctx : GeneralNominalCandidates.Context => ctx.state.seed) frame.context_eq
  have same : output ∈ q.packet.site.occurrence.demand.outputs := frame.occurrence_eq.symm ▸ listed
  exact body_private safe (safe.outputs output same) body (seed.symm ▸ found)

theorem certificate_iff (reach : Reachable registry root state) {q : Plan roles}
    {x y : Assignment} (agrees : AgreeOutside (raw state).seed x y) :
    Certificate r state.core x focus key children q ↔ Certificate r state.core y focus key children q := by
  constructor
  · intro h
    exact ⟨h.frame,h.children_eq,(packet_iff reach h.frame agrees).mp h.packet,
      fun o listed => (output_iff reach h.frame agrees o listed).mp (h.outputs o listed)⟩
  · intro h
    exact ⟨h.frame,h.children_eq,(packet_iff reach h.frame agrees).mpr h.packet,
      fun o listed => (output_iff reach h.frame agrees o listed).mpr (h.outputs o listed)⟩

theorem evidence_iff (reach : Reachable registry root state) (r : Registry)
    {x y : Assignment} (agrees : AgreeOutside (raw state).seed x y)
    (focus : Occurrence roles) (payload : Payload) :
    Evidence r state.core x focus payload ↔ Evidence r state.core y focus payload := by
  have same : Instance r state.core x = Instance r state.core y := by
    funext whereAt key children
    apply propext
    exact exists_congr fun q => certificate_iff (q := q) reach agrees
  unfold GeneralNominalVersionedEvidence231.Evidence
  rw [same]

end Yulang.GeneralRebasePrivateEvidence282
