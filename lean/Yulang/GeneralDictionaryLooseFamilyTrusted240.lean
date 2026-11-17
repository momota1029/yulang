import Yulang.GeneralDictionaryLooseFamilyHistory240
import Yulang.GeneralNominalVersionedSupport233
set_option backward.isDefEq.respectTransparency false
/-! Actual versioned Trusted constructor, for an arbitrary journal containing
the indexed family plans and retaining the original source. No existence of
such reachable journals for all n is assumed or claimed. This isolates the
historical-input cache induction needed by the still-unfinished path family. -/
namespace Yulang.GeneralDictionaryLooseFamilyTrusted240
open GeneralDictionaryLooseFamilyPacket240 GeneralDictionaryLooseFamilySnapshot240
open GeneralDictionaryLooseFamilyHistory240
open GeneralDictionaryLooseLoopSource240 (roles)
open GeneralNominalVersionedSupport233
open GeneralNominalCommonBridge (Assignment)
variable (allocations : Nat → List GeneralNominalIdentities.Origin)
 (reservations : Nat → List Nat) (atoms : Nat → List (PresenceNormalForm.Atom Nat))

def facts : Nat → List (Fact roles)
 | 0 => []
 | n+1 => .input (plan n (allocations n) (reservations n) (atoms n)) :: facts n

theorem member (n index : Nat) (before : index < n) :
 .input (plan index (allocations index) (reservations index) (atoms index)) ∈ facts allocations reservations atoms n := by
 induction n with
 | zero => omega
 | succ n ih =>
   by_cases last : index=n
   · subst index; exact List.mem_cons_self
   · exact List.mem_cons_of_mem _ (ih (by omega))

theorem slice_history (journal : GeneralNominalVersionedJournal232.State roles) (n : Nat) (m : Assignment)
 (valid : SliceModels journal (facts allocations reservations atoms n) m) : History allocations reservations atoms n m :=
 fun index before => valid.2.2 _ (member allocations reservations atoms n index before)

theorem recorded_sound (n : Nat) (allocated reserved ordinary) (m : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot m)
 (history : History allocations reservations atoms n m)
 (recorded : GeneralCanonicalObservations.Recorded (snapshot n allocated reserved ordinary) observation) : observation.Holds m := by
 have raw := GeneralDictionaryLooseFamilyHistory240.raw_models allocations reservations atoms n allocated reserved [] m source history
   (by intro _ h; cases h)
 apply GeneralCanonicalObservations.recorded_sound (snapshot n allocated reserved []) m raw
 cases recorded with
 | scalar slot scalar found => cases found
 | structural slot kind children found => cases found
 | nominal slot descriptor found => exact GeneralCanonicalObservations.Recorded.nominal (snapshot := snapshot n allocated reserved []) slot descriptor found

theorem readback (journal : GeneralNominalVersionedJournal232.State roles) (n : Nat)
 (source : journal.core.erased.source.state = GeneralDictionaryLooseLoopSource240.snapshot) :
 Readback journal (facts allocations reservations atoms n) (plan n (allocations n) (reservations n) (atoms n)) := by
 intro slot visited test observation head m valid
 apply recorded_sound allocations reservations atoms n (allocations n) (reservations n) (atoms n) m
   (source ▸ valid.1) (slice_history allocations reservations atoms journal n m valid)
 exact GeneralNominalSupport.head_recorded head

theorem trusted (journal : GeneralNominalVersionedJournal232.State roles) (n : Nat)
 (source : journal.core.erased.source.state = GeneralDictionaryLooseLoopSource240.snapshot)
 (recorded : ∀ index < n, plan index (allocations index) (reservations index) (atoms index) ∈ journal.plans) :
 Trusted journal (facts allocations reservations atoms n) := by
 induction n with
 | zero => exact .source
 | succ n ih =>
   exact .input _ (ih (fun index before => recorded index (by omega))) (recorded n (by omega))
     (readback allocations reservations atoms journal n source)
end Yulang.GeneralDictionaryLooseFamilyTrusted240
