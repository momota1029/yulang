import Yulang.GeneralDictionaryVersionLoopFamilyRefresh238
set_option backward.isDefEq.respectTransparency false
/-! Uniform certified reobservation after the indexed Refresh. Structural
journal/source/history hypotheses remain explicit; no all-index reachable
journal family or infinite execution is asserted. -/
namespace Yulang.GeneralDictionaryVersionLoopFamilyReobserve238
open GeneralDictionaryVersionLoopFamilyPacket238 GeneralDictionaryVersionLoopFamilyExpose238
open GeneralDictionaryVersionLoopSource237 (roles registry root)
variable (allocations : Nat → List GeneralNominalIdentities.Origin)
 (reservations : Nat → List Nat) (atoms : Nat → List (PresenceNormalForm.Atom Nat))
variable (journal : GeneralNominalVersionedJournal232.State roles) (n : Nat)
variable (source : journal.core.erased.source.state = GeneralDictionaryVersionLoopSource237.snapshot)
variable (recorded : ∀ index < n+1, plan index (allocations index) (reservations index) (atoms index) ∈ journal.plans)
noncomputable abbrev refreshed := GeneralNominalVersionedRefresh232.refresh journal
 (exposed n (allocations n) (reservations n) (atoms n))
noncomputable abbrev revision : GeneralNominalReobservationSteps.Revision
 (refreshed allocations reservations atoms journal n).core.erased.current :=
 GeneralDictionaryVersionLoopFamilyRevision238.revision n
   (replay n (allocations n) (reservations n) (atoms n)).packet.context.state.allocated
   (replay n (allocations n) (reservations n) (atoms n)).packet.context.state.reserved
   (replay n (allocations n) (reservations n) (atoms n)).packet.context.state.ordinary
   (refreshed allocations reservations atoms journal n).core.erased.current

include source recorded in
theorem certificate : GeneralNominalVersionedMixedObservations233.Reobserve
 (refreshed allocations reservations atoms journal n) (revision allocations reservations atoms journal n) := by
 constructor
 · intro m valid
   exact GeneralDictionaryVersionLoopFamilyBack238.raw_back n _ _ _
     (GeneralDictionaryVersionLoopFamilyInstallation238.replay_lower n (allocations n) (reservations n) (atoms n)) m valid
 · exact GeneralDictionaryVersionLoopFamilyCache238.point_cache allocations reservations atoms
     (refreshed allocations reservations atoms journal n) (n+1) _ _ _ source recorded

include source recorded in
theorem step : GeneralNominalVersionedMixedKernel234.Step registry root
 (refreshed allocations reservations atoms journal n)
 (GeneralNominalVersionedRefresh232.reobserve (refreshed allocations reservations atoms journal n)
   (revision allocations reservations atoms journal n)) := by
 refine ⟨root,.root,.administrative (.reobserve root _
   (certificate allocations reservations atoms journal n source recorded) ?_)⟩
 exact GeneralDictionaryVersionLoopFamilyRevision238.improved n _ _ _ _

include source recorded in
theorem two_steps
 (current : journal.core.erased.current.context = (replay n (allocations n) (reservations n) (atoms n)).packet.context) :
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) journal
 (GeneralNominalVersionedRefresh232.reobserve (refreshed allocations reservations atoms journal n)
   (revision allocations reservations atoms journal n)) :=
 .tail (.tail .refl (GeneralDictionaryVersionLoopFamilyRefresh238.step allocations reservations atoms journal n source current recorded))
   (step allocations reservations atoms journal n source recorded)
end Yulang.GeneralDictionaryVersionLoopFamilyReobserve238
