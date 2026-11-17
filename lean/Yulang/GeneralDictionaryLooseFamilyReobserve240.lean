import Yulang.GeneralNominalPointKernel240
import Yulang.GeneralDictionaryLooseFamilyRefresh240
set_option backward.isDefEq.respectTransparency false
/-! Uniform certified reobservation after the indexed Refresh. Structural
journal/source/history hypotheses remain explicit; no all-index reachable
journal family or infinite execution is asserted. -/
namespace Yulang.GeneralDictionaryLooseFamilyReobserve240
open GeneralDictionaryLooseFamilyPacket240 GeneralDictionaryLooseFamilyExpose240
open GeneralDictionaryLooseLoopSource240 (roles registry root)
variable (allocations : Nat → List GeneralNominalIdentities.Origin)
 (reservations : Nat → List Nat) (atoms : Nat → List (PresenceNormalForm.Atom Nat))
variable (journal : GeneralNominalVersionedJournal232.State roles) (n : Nat)
variable (source : journal.core.erased.source.state = GeneralDictionaryLooseLoopSource240.snapshot)
variable (recorded : ∀ index < n+1, plan index (allocations index) (reservations index) (atoms index) ∈ journal.plans)
noncomputable abbrev refreshed := GeneralNominalVersionedRefresh232.refresh journal
 (exposed n (allocations n) (reservations n) (atoms n))
noncomputable abbrev revision : GeneralNominalReobservationSteps.Revision
 (refreshed allocations reservations atoms journal n).core.erased.current :=
 GeneralDictionaryLooseFamilyRevision240.revision n
   (replay n (allocations n) (reservations n) (atoms n)).packet.context.state.allocated
   (replay n (allocations n) (reservations n) (atoms n)).packet.context.state.reserved
   (replay n (allocations n) (reservations n) (atoms n)).packet.context.state.ordinary
   (refreshed allocations reservations atoms journal n).core.erased.current

include source recorded in
theorem certificate : GeneralNominalVersionedMixedObservations233.Reobserve
 (refreshed allocations reservations atoms journal n) (revision allocations reservations atoms journal n) := by
 constructor
 · intro m valid
   exact GeneralDictionaryLooseFamilyBack240.raw_back n _ _ _
     (GeneralDictionaryLooseFamilyInstallation240.replay_lower n (allocations n) (reservations n) (atoms n)) m valid
 · exact GeneralDictionaryLooseFamilyCache240.point_cache allocations reservations atoms
     (refreshed allocations reservations atoms journal n) (n+1) _ _ _ source recorded

include source recorded in
theorem step : GeneralNominalPointKernel240.Step registry root
 (refreshed allocations reservations atoms journal n)
 (GeneralNominalVersionedRefresh232.reobserve (refreshed allocations reservations atoms journal n)
   (revision allocations reservations atoms journal n)) := by
 refine ⟨root,.root,.administrative (.reobserve root _
   (certificate allocations reservations atoms journal n source recorded) ?_ ?_)⟩
 · exact GeneralDictionaryLooseFamilyRevision240.improved n _ _ _ _
 · exact GeneralDictionaryLooseFamilyRevision240.preserves n _ _ _ _

include source recorded in
theorem two_steps
 (current : journal.core.erased.current.context = (replay n (allocations n) (reservations n) (atoms n)).packet.context) :
 B4Target.Steps (GeneralNominalPointKernel240.Step registry root) journal
 (GeneralNominalVersionedRefresh232.reobserve (refreshed allocations reservations atoms journal n)
   (revision allocations reservations atoms journal n)) :=
 .tail (.tail .refl (GeneralDictionaryLooseFamilyRefresh240.step allocations reservations atoms journal n source current recorded))
   (step allocations reservations atoms journal n source recorded)
end Yulang.GeneralDictionaryLooseFamilyReobserve240
