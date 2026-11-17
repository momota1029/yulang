import Yulang.GeneralDictionaryVersionLoopFamilyCache238
import Yulang.GeneralNominalVersionedMixedKernel234
set_option backward.isDefEq.respectTransparency false
/-! A complete mixed Refresh certificate and actual kernel step at every
indexed shape, assuming the journal has the specified installed current
context, original source and recorded family plans. This does not construct
such journals or subsequent reobservations/installations for all indices. -/
namespace Yulang.GeneralDictionaryVersionLoopFamilyRefresh238
open GeneralDictionaryVersionLoopFamilyPacket238 GeneralDictionaryVersionLoopFamilyExpose238
open GeneralDictionaryVersionLoopSource237 (roles registry root)
open GeneralDictionaryVersionLoopNames238 (lower)
variable (allocations : Nat → List GeneralNominalIdentities.Origin)
 (reservations : Nat → List Nat) (atoms : Nat → List (PresenceNormalForm.Atom Nat))
variable (journal : GeneralNominalVersionedJournal232.State roles) (n : Nat)
variable (source : journal.core.erased.source.state = GeneralDictionaryVersionLoopSource237.snapshot)
variable (current : journal.core.erased.current.context = (replay n (allocations n) (reservations n) (atoms n)).packet.context)
variable (recorded : ∀ index < n+1, plan index (allocations index) (reservations index) (atoms index) ∈ journal.plans)

noncomputable def certificate : GeneralNominalVersionedMixedObservations233.Refresh journal
 (exposed n (allocations n) (reservations n) (atoms n)) where
 refines := by rw [current]; exact refines n _ _ _
 interpretation := by rw [current]; rfl
 support := by rw [current]; exact support n _ _ _
 constraints := by
   intro m valid
   refine ⟨GeneralDictionaryVersionLoopFamilyHistory238.base_models (n+1) m (source ▸ valid.1.2.1),?_⟩
   have present := valid.1.1.2.2
   rw [current] at present
   exact present
 cache := GeneralDictionaryVersionLoopFamilyCache238.loose_cache allocations reservations atoms journal n _ _ _ source recorded

include source current recorded
theorem step : GeneralNominalVersionedMixedKernel234.Step registry root journal
 (GeneralNominalVersionedRefresh232.refresh journal (exposed n (allocations n) (reservations n) (atoms n))) := by
 refine ⟨root,.root,.refresh root _ (certificate allocations reservations atoms journal n source current recorded)
   (lower (n+1)) ?_ ?_ (lower_known n _ _ _)⟩
 · rw [current]; exact lower_supported n _ _ _
 · rw [current]; exact lower_unknown n _ _ _
end Yulang.GeneralDictionaryVersionLoopFamilyRefresh238
