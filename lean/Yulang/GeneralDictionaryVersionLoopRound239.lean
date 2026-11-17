import Yulang.GeneralDictionaryVersionLoopInstall239
set_option backward.isDefEq.respectTransparency false
/-! Actual one-install/two-observation round with structural preservation.
Novelty is explicit here; a later producer must discharge it before claiming
an indexed reachable execution. Arbitrary-assignment model transport is exact
enough to preserve future novelty witnesses. -/
namespace Yulang.GeneralDictionaryVersionLoopRound239
open GeneralDictionaryVersionLoopSource237 (roles registry root model)
open GeneralDictionaryVersionLoopBook239 GeneralDictionaryVersionLoopFrame239
open GeneralDictionaryVersionLoopInstall239
open GeneralNominalVersionedJournal232

noncomputable abbrev refreshed (shape : Shape journal n) :=
 GeneralDictionaryVersionLoopFamilyReobserve238.refreshed allocations reservations atoms (installed shape) n
noncomputable abbrev revision (shape : Shape journal n) :=
 GeneralDictionaryVersionLoopFamilyReobserve238.revision allocations reservations atoms (installed shape) n
noncomputable abbrev next (shape : Shape journal n) := GeneralNominalVersionedRefresh232.reobserve (refreshed shape) (revision shape)

theorem next_shape (shape : Shape journal n) : Shape (next shape) (n+1) where
 current := after_reobserve_context (installed shape) n
 source := shape.source
 rawSites := by
   change journal.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites (plan n) = _
   rw [shape.rawSites,raw_children_empty]; rfl
 centers := by
   change journal.core.sites ++ GeneralNominalVersionedChildren232.emitted (plan n) = _
   rw [shape.centers,emitted_empty]; rfl
 choice := by
   intro prior member
   change prior ∈ (packet n) :: journal.core.erased.current.packets at member
   rcases List.mem_cons.mp member with rfl | member
   · rfl
   · exact shape.choice prior member

theorem next_recorded (shape : Shape journal n) (recorded : ∀ index < n, plan index ∈ journal.plans) :
 ∀ index < n+1, plan index ∈ (next shape).plans := installed_recorded shape recorded

theorem models_general (shape : Shape journal n) (recorded : ∀ index < n, plan index ∈ journal.plans)
 (assignment) (valid : Models journal assignment) (packetValid : GeneralNominalVersionedPlans231.Holds (plan n) assignment) :
 Models (next shape) assignment := by
 have installedValid : Models (installed shape) assignment :=
   (GeneralNominalVersionedInstall232.install_models rfl).mpr (common_general shape assignment valid packetValid)
 have refreshedValid : Models (refreshed shape) assignment :=
   (GeneralNominalVersionedMixedObservations233.refresh_models
     (GeneralDictionaryVersionLoopFamilyRefresh238.certificate allocations reservations atoms (installed shape) n
       shape.source rfl (installed_recorded shape recorded))).mpr installedValid
 exact (GeneralNominalVersionedMixedObservations233.reobserve_models
   (GeneralDictionaryVersionLoopFamilyReobserve238.certificate allocations reservations atoms (installed shape) n
     shape.source (installed_recorded shape recorded))).mpr refreshedValid

theorem models (shape : Shape journal n) (recorded : ∀ index < n, plan index ∈ journal.plans)
 (valid : Models journal model) : Models (next shape) model := models_general shape recorded model valid (packet_holds n)

theorem path (shape : Shape journal n) (valid : Models journal model)
 (recorded : ∀ index < n, plan index ∈ journal.plans)
 (novel : ¬ GeneralNominalVersionedMixedKernel234.Committed journal (plan n)) :
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) journal (next shape) :=
 .tail (.tail (.tail .refl (GeneralDictionaryVersionLoopInstall239.step shape valid recorded novel))
   (GeneralDictionaryVersionLoopFamilyRefresh238.step allocations reservations atoms (installed shape) n
     shape.source rfl (installed_recorded shape recorded)))
   (GeneralDictionaryVersionLoopFamilyReobserve238.step allocations reservations atoms (installed shape) n
     shape.source (installed_recorded shape recorded))
end Yulang.GeneralDictionaryVersionLoopRound239
