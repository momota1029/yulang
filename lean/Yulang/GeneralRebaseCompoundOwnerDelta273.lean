import Yulang.GeneralRebaseCompoundOwnerBoundary273

set_option maxRecDepth 14000
set_option maxHeartbeats 3600000
namespace Yulang.GeneralRebaseCompoundOwnerDelta273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCompoundObstruction238 (oldPlan currentPlan)
open GeneralRebaseCompoundOwnerCapture273 (low high)
open GeneralRebaseCompoundReplacement273 (lower upper center)
open GeneralRebaseCompoundOwnerExpressions273 (physical)
open GeneralRebaseCompoundOwnerMeaning273 (Sound)
open GeneralRebaseCompoundOwnerBlock273 (Block Slot eval loose)
open GeneralRebaseCompoundOwnerStep273 (PublicMeaning)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

abbrev pointed := GeneralRebaseCompoundOwnerBlock273.point

/-- Shape of the two physical layouts used to evaluate the same five
logical slots; the new branch does not inherit the old aggregate addresses. -/
def addresses (plan : GeneralNominalCenters.Plan GeneralDictionaryJournalRefinement228Source.roles) : List Nat :=
 [physical plan .captureLo,physical plan .captureHi,physical plan .childLo,
  physical plan .childHi,physical plan .childCenter]

theorem old_distinct : (addresses oldPlan).Nodup := by decide +kernel
theorem current_distinct : (addresses currentPlan).Nodup := by decide +kernel

theorem old_private : (addresses oldPlan).all (fun id => 4 < id) = true := by decide +kernel
theorem current_private : (addresses currentPlan).all (fun id => 4 < id) = true := by decide +kernel

theorem aggregate_addresses_change :
 physical oldPlan .captureLo ≠ physical currentPlan .captureLo ∧
 physical oldPlan .captureHi ≠ physical currentPlan .captureHi := by decide +kernel

theorem children_addresses_stable :
 physical oldPlan .childLo = physical currentPlan .childLo ∧
 physical oldPlan .childHi = physical currentPlan .childHi ∧
 physical oldPlan .childCenter = physical currentPlan .childCenter := ⟨rfl,rfl,rfl⟩

def stable (s : Slot) : Bool := decide (GeneralRebaseCompoundOwnerBlock273.read loose s = GeneralRebaseCompoundOwnerBlock273.read pointed s)

theorem known_delta :
 [Slot.captureLo,.captureHi,.childLo,.childHi,.childCenter].filter (fun s => !stable s) = [.captureLo,.childLo] := rfl

theorem equal_public_values {a b : Assignment} (same : Agrees a b) (id : Nat) (allowed : id ≤ 4) :
 Equivalent (a id).1 (b id).1 := by
 rw [same.1 id allowed]
 exact ⟨subtype_refl _,subtype_refl _⟩

theorem same_hi {a b : Assignment} (same : Agrees a b)
 (old : Sound a oldPlan loose) (current : Sound b currentPlan pointed) :
 Equivalent (a (high oldPlan)).1 (b (high currentPlan)).1 :=
 equivalent_trans old.captureHi (equivalent_trans (equal_public_values same 2 (by decide))
   ⟨current.captureHi.2,current.captureHi.1⟩)

theorem same_child_hi {a b : Assignment} (same : Agrees a b)
 (old : Sound a oldPlan loose) (current : Sound b currentPlan pointed) :
 Equivalent (a upper).1 (b upper).1 :=
 equivalent_trans old.childHi (equivalent_trans
   (GeneralRebaseCompoundChildBoundary273.variant_equivalent _ _ (equal_public_values same 2 (by decide)))
   ⟨current.childHi.2,current.childHi.1⟩)

theorem same_center {a b : Assignment} (same : Agrees a b)
 (old : Sound a oldPlan loose) (current : Sound b currentPlan pointed) :
 Equivalent (a center).1 (b center).1 :=
 equivalent_trans old.childCenter (equivalent_trans
   (GeneralRebaseCompoundChildBoundary273.variant_equivalent _ _ (equal_public_values same 2 (by decide)))
   ⟨current.childCenter.2,current.childCenter.1⟩)

end Yulang.GeneralRebaseCompoundOwnerDelta273
