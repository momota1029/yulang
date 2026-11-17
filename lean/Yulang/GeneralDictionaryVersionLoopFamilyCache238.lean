import Yulang.GeneralDictionaryVersionLoopFamilyTrusted238
import Yulang.GeneralDictionaryVersionLoopFamilyExpose238
import Yulang.GeneralNominalVersionedMixedObservations233
set_option backward.isDefEq.respectTransparency false
/-! Uniform mixed-cache producers from finite recorded input history. They do
not assert reachable journals containing such histories at every stage. -/
namespace Yulang.GeneralDictionaryVersionLoopFamilyCache238
open GeneralDictionaryVersionLoopFamilyPacket238 GeneralDictionaryVersionLoopFamilySnapshot238
open GeneralDictionaryVersionLoopFamilyHistory238 GeneralDictionaryVersionLoopFamilyTrusted238
open GeneralDictionaryVersionLoopNames238 (lower)
open GeneralNominalVersionedSupport233
open GeneralNominalCommonBridge (Assignment)
variable (allocations : Nat → List GeneralNominalIdentities.Origin)
 (reservations : Nat → List Nat) (atoms : Nat → List (PresenceNormalForm.Atom Nat))
variable (journal : GeneralNominalVersionedJournal232.State GeneralDictionaryVersionLoopSource237.roles)

theorem point_cache (n : Nat) (allocated reserved ordinary)
 (source : journal.core.erased.source.state = GeneralDictionaryVersionLoopSource237.snapshot)
 (recorded : ∀ index < n, plan index (allocations index) (reservations index) (atoms index) ∈ journal.plans) :
 GeneralNominalVersionedMixedObservations233.CacheSound journal (snapshot n allocated reserved ordinary) := by
 apply GeneralNominalVersionedMixedObservations233.versioned_cache
 intro observation found
 refine ⟨facts allocations reservations atoms n,trusted allocations reservations atoms journal n source recorded,?_⟩
 intro m valid
 exact GeneralDictionaryVersionLoopFamilyTrusted238.recorded_sound allocations reservations atoms n allocated reserved ordinary m
   (source ▸ valid.1) (slice_history allocations reservations atoms journal n m valid) found

theorem loose_sound (n : Nat) (allocated reserved ordinary) (m : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryVersionLoopSource237.snapshot m)
 (history : History allocations reservations atoms (n+1) m)
 (recorded : GeneralCanonicalObservations.Recorded
   (GeneralDictionaryVersionLoopFamilyRefines238.state n allocated reserved ordinary) observation) : observation.Holds m := by
 let equations := GeneralNominalAllocation.equations (lower (n+1))
   (.union (.var (lower n)) (.var (lower n)))
 have held : PresenceNormalForm.All CommonNominalFullCarrier.model m equations := by
   intro atom member
   exact (history n (by omega)).1.2.1 atom
     (GeneralDictionaryVersionLoopFamilyInstallation238.lower_in_merges n (allocations n) (reservations n) (atoms n) member)
 have rawPoint := GeneralDictionaryVersionLoopFamilyHistory238.raw_models allocations reservations atoms (n+1)
   allocated reserved equations m source history held
 have rawLoose := GeneralDictionaryVersionLoopFamilyBack238.raw_back n allocated reserved equations
   (fun _ member => member) m rawPoint
 apply GeneralCanonicalObservations.recorded_sound
   (GeneralDictionaryVersionLoopFamilyRefines238.state n allocated reserved equations) m rawLoose
 cases recorded with
 | scalar slot scalar found => cases found
 | structural slot kind children found => cases found
 | nominal slot descriptor found =>
   exact GeneralCanonicalObservations.Recorded.nominal
     (snapshot := GeneralDictionaryVersionLoopFamilyRefines238.state n allocated reserved equations) slot descriptor found

theorem loose_cache (n : Nat) (allocated reserved ordinary)
 (source : journal.core.erased.source.state = GeneralDictionaryVersionLoopSource237.snapshot)
 (recorded : ∀ index < n+1, plan index (allocations index) (reservations index) (atoms index) ∈ journal.plans) :
 GeneralNominalVersionedMixedObservations233.CacheSound journal
   (GeneralDictionaryVersionLoopFamilyRefines238.state n allocated reserved ordinary) := by
 apply GeneralNominalVersionedMixedObservations233.versioned_cache
 intro observation found
 refine ⟨facts allocations reservations atoms (n+1),trusted allocations reservations atoms journal (n+1) source recorded,?_⟩
 intro m valid
 exact loose_sound allocations reservations atoms n allocated reserved ordinary m
   (source ▸ valid.1) (slice_history allocations reservations atoms journal (n+1) m valid) found
end Yulang.GeneralDictionaryVersionLoopFamilyCache238
