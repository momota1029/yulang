import Yulang.GeneralRebaseReceiptAliasControl289

/-! The child identity alone does not authenticate its demand. Both the
older and finite-catalogue gates accept an unmatched argument vector
when the caller preserves the same identity. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29200
set_option maxHeartbeats 19500000
namespace Yulang.GeneralRebaseReceiptIdentityCollision289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseReceiptFixture289 (wire request endpoint_decision)
open GeneralRebaseReceiptExtract289 (extract diagnostic rootRecorded)
open GeneralRebaseReceiptCatalogue289 (guarded boundedWire)
open GeneralRebaseReceiptCatalogueFixture289 (sealed_after)
open GeneralRebaseReceiptWire289 (check)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState (Generated)

def movedChild : Occurrence roles :=
  ⟨(child true).identity,⟨1,fun _ => (1,1),[],by intro _ no; cases no⟩⟩

theorem moved_not_root : movedChild ≠ root := by
  intro same
  have role := congrArg (fun o : Occurrence roles => o.demand.role) same
  change (1 : Nat) = 0 at role
  cases role

theorem moved_not_child : movedChild ≠ child true := by
  intro same
  have args := congrArg (fun o : Occurrence roles => List.ofFn o.demand.arguments) same
  change [(1,1)] = [(0,0)] at args
  cases args

theorem not_generated : ¬ Generated (after true).core.erased.current root movedChild :=
  fun seen => (GeneralRebaseRowClosure287.scope true seen).elim moved_not_root moved_not_child

theorem no_current_emitted_frame (key : Nat) (p : GeneralNominalCenters.Plan roles) :
    ¬ GeneralNominalVersionedEvidence231.Frame (registry true) (after true).core movedChild key p := by
  intro frame
  have present := frame.raw_recorded
  rw [GeneralRebaseRowParentEvidence287.raw_sites true] at present
  rcases List.mem_cons.mp present with parent | pending
  · exact moved_not_root (frame.occurrence_eq.symm.trans (congrArg GeneralNominalDemandMerging.Site.occurrence parent))
  · have expected := List.mem_singleton.mp pending
    exact moved_not_child (frame.occurrence_eq.symm.trans (congrArg GeneralNominalDemandMerging.Site.occurrence expected))

theorem wire_collision : extract (registry true) (after true) movedChild = wire true (after true) := by
  have seen : rootRecorded (current true) movedChild = rootRecorded (current true) (child true) := by decide +kernel
  have report : diagnostic (current true) movedChild opaqueChild =
      diagnostic (current true) (child true) opaqueChild := by decide +kernel
  unfold wire
  unfold extract
  rw [show GeneralRebaseReceiptExtract289.candidates (registry true) movedChild = [opaqueChild] from rfl,
      show GeneralRebaseReceiptExtract289.candidates (registry true) (child true) = [opaqueChild] from rfl]
  change GeneralRebaseReceiptWire289.Wire.mk _ _ _ _ _ _
      (rootRecorded (current true) movedChild) (diagnostic (current true) movedChild opaqueChild) =
    GeneralRebaseReceiptWire289.Wire.mk _ _ _ _ _ _
      (rootRecorded (current true) (child true)) (diagnostic (current true) (child true) opaqueChild)
  rw [seen,report]
  rfl

theorem registry_guard_still_collides :
    guarded (registry true) (after true) movedChild (request true) = .ready := by
  have sealed : boundedWire (registry true) (after true) movedChild =
      boundedWire (registry true) (after true) (child true) := by
    unfold boundedWire
    rw [wire_collision]
    rfl
  unfold guarded
  rw [sealed,sealed_after]
  exact endpoint_decision true

end Yulang.GeneralRebaseReceiptIdentityCollision289
