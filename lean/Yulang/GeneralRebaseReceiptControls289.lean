import Yulang.GeneralRebaseReceiptWitness289

/-! Replay controls include the actual foreign-plan ledger and synthetic
wire mutations. A diagnostic of a synthetic wire is not a source execution. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptControls289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseForeignLeaf288 (unscoped)
open GeneralRebaseReceiptWire289
open GeneralRebaseReceiptExtract289
open GeneralRebaseReceiptFixture289

theorem world_disagrees : (registry false).declarations ≠ (registry true).declarations := by decide +kernel

theorem not_using_plans (r : GeneralDeclarations.Registry)
    (s : GeneralNominalVersionedJournal232.State roles) (p : GeneralNominalCenters.Plan roles)
    (focus : GeneralSourceDictionaries.Occurrence roles) :
    extract r (GeneralRebaseLeafLedger288.record s p) focus = extract r s focus := rfl

theorem foreign_stays_unfinished :
    check (wire false unscoped) (request false) = .unfinished :=
  endpoint_decision false

theorem stale_offer_rejected :
    check (wire false unscoped) (request true) = .wrongWorld := by
  change check (wire false (after false)) (request true) = _
  rw [wire_exact]
  unfold check
  exact ite_eq_left world_disagrees

theorem override_registry_catches_producer :
    check (extract (registry true) unscoped (child false)) (request true) = .missingProducer := by
  let w := extract (registry true) unscoped (child false)
  have same : w.world = (request true).world := rfl
  have list : w.producers = [producer false] := by
    change [effectSummary (effect false)] = _
    rw [producer_exact]
  have cannot : (producer false).matches (request true) = false := by
    apply Bool.eq_false_iff.mpr
    intro compare
    exact world_disagrees ((matching_producer _ _).mp compare).1
  have never : w.producers.any (·.matches (request true)) = false := by
    rw [list]
    simp [cannot]
  change check w (request true) = _
  simp [check,same,never]

def wrongTarget : Offer := { request true with output := 3 }
def detached : Wire := { expectedWire true with edges := [] }
def effectiveChild : Wire := { expectedWire true with childTargets := [3] }

theorem wrong_target : check (expectedWire true) wrongTarget = .missingProducer := by
  have same : (expectedWire true).world = wrongTarget.world := rfl
  have producerList : (expectedWire true).producers = [producer true] := rfl
  have no : (producer true).matches wrongTarget = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have num := List.mem_singleton.mp ((matching_producer _ _).mp h).2.2.2.2
    cases num
  unfold check
  simp only [same,ne_eq,not_true_eq_false,ite_false,producerList,List.any_cons,no,List.any_nil,
    Bool.false_or,Bool.not_false,ite_true]

theorem detached_rejected : check detached (request true) = .detached := by
  have producerList : detached.producers = [producer true] := rfl
  have same : detached.world = (request true).world := rfl
  have noEdge : detached.edges = [] := rfl
  unfold check
  simp only [producerList,List.any_cons,producer_matches,Bool.true_or,Bool.not_true,ite_false,
    same,ne_eq,not_true_eq_false,noEdge,List.not_mem_nil,not_false_eq_true,or_true,ite_true]
  rfl

theorem live_request_rejected : check effectiveChild (request true) = .nonInert := by
  have producerList : effectiveChild.producers = [producer true] := rfl
  have same : effectiveChild.world = (request true).world := rfl
  have actualChild : effectiveChild.child = (request true).child := rfl
  have edges : ((request true).parent,(request true).child) ∈ effectiveChild.edges := List.mem_singleton_self _
  unfold check
  simp only [producerList,List.any_cons,producer_matches,Bool.true_or,Bool.not_true,ite_false,
    same,ne_eq,not_true_eq_false,actualChild,edges,or_self]
  rfl

end Yulang.GeneralRebaseReceiptControls289
