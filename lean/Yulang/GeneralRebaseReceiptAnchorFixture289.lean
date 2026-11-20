import Yulang.GeneralRebaseReceiptExactLink289

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29400
set_option maxHeartbeats 20000000
namespace Yulang.GeneralRebaseReceiptAnchorFixture289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child sole_child)
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseReceiptFixture289 (wire request producer_exact producer_matches wire_exact)
open GeneralRebaseReceiptCatalogue289 (boundedWire)
open GeneralRebaseReceiptCatalogueFixture289 (sealed_before sealed_after outside_agrees finite_footprint_not_global)
open GeneralRebaseReceiptIdentityCollision289 (movedChild not_generated wire_collision)
open GeneralRebaseReceiptCollision289 (removed)
open GeneralRebaseReceiptExactLink289
open GeneralNominalVersionedJournal232 (State)

theorem anchored_after (choice : Bool) :
    Anchored (registry choice) (after choice) root (child choice) (request choice) := by
  refine ⟨?_,effect choice,List.mem_singleton_self _,rfl,?_,?_,fun _ _ => rfl⟩
  · rw [GeneralRebaseRowClosure287.edges]
    exact List.mem_singleton_self _
  · rw [show (effect choice).plan = GeneralRebaseRowParentPacket287.plan choice from rfl,sole_child]
    exact List.mem_singleton_self _
  · rw [producer_exact]
    exact producer_matches choice

theorem before_anchor_wire (choice : Bool) :
    anchoredWire (registry choice) before root (child choice) (request choice) = some (wire choice before) := by
  unfold anchoredWire
  rw [sealed_before]
  have empty : anchors (registry choice) before root (child choice) (request choice) = false := by
    apply Bool.eq_false_iff.mpr
    intro seen
    have claim := (anchors_exact ..).mp seen
    exact List.not_mem_nil claim.1
  rw [Option.map_some,empty]
  rfl

theorem after_anchor_wire (choice : Bool) :
    anchoredWire (registry choice) (after choice) root (child choice) (request choice) =
      some (wire choice (after choice)) := by
  unfold anchoredWire
  rw [sealed_after]
  have good := (anchors_exact ..).mpr (anchored_after choice)
  rw [Option.map_some,ite_eq_left good]

theorem displaced_rejected :
    boundedDecision (registry true) (after true) root movedChild (request true) = .detached := by
  have guardedSame : boundedWire (registry true) (after true) movedChild = some (wire true (after true)) := by
    have same : boundedWire (registry true) (after true) movedChild =
        boundedWire (registry true) (after true) (child true) := by
      unfold boundedWire
      rw [wire_collision]
      rfl
    rw [same,sealed_after]
  have no : ¬ anchors (registry true) (after true) root movedChild (request true) = true := by
    intro flag
    have semantic := (anchors_exact ..).mp flag
    exact not_generated (.child .root semantic.1)
  unfold boundedDecision anchoredWire
  rw [guardedSame,Option.map_some,ite_eq_right no,wire_exact]
  exact GeneralRebaseReceiptControls289.detached_rejected

theorem still_finite_metadata :
    boundedDecision (removed 8) (after true) root (child true) (request true) = .ready ∧
      ∀ key p, ¬ GeneralNominalVersionedEvidence231.Frame (removed 8) (after true).core (child true) key p := by
  have evidence := finite_footprint_not_global
  have same : Anchored (removed 8) (after true) root (child true) (request true) := by
    obtain ⟨edge,e,present,rooted,dd,matchOffer,_⟩ := anchored_after true
    have eEq : e = effect true := List.mem_singleton.mp present
    subst e
    exact ⟨edge,effect true,present,rooted,dd,matchOffer,
      (GeneralRebaseReceiptCatalogue289.agreement_exact ..).mp outside_agrees⟩
  refine ⟨?_,evidence.2.2⟩
  unfold boundedDecision anchoredWire
  cases h : boundedWire (removed 8) (after true) (child true) with
  | none =>
    have good := evidence.2.1
    unfold GeneralRebaseReceiptCatalogue289.guarded at good
    rw [h] at good
    cases good
  | some w =>
    have good := evidence.2.1
    unfold GeneralRebaseReceiptCatalogue289.guarded at good
    rw [h] at good
    rw [Option.map_some,ite_eq_left ((anchors_exact ..).mpr same)]
    exact good

end Yulang.GeneralRebaseReceiptAnchorFixture289
