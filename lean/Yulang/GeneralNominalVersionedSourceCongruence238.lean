import Yulang.GeneralNominalVersionedEffectCongruence238
import Yulang.GeneralNominalVersionedMixedRegistry234
import Yulang.GeneralNominalVersionedHistoryNormalization238
set_option backward.isDefEq.respectTransparency false
/-! Full journal semantic congruence on the actual mixed-source domain.
Historical normalization therefore preserves an existing full Models witness.
No common model for a new prospective plan is constructed. -/
namespace Yulang.GeneralNominalVersionedSourceCongruence238
open GeneralNominalAssignmentCongruence238 (Same)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232
variable {roles : Roles.RoleDecls} {first last : Assignment}

theorem raw_site (same : Same first last)
 (valid : GeneralNominalSaturationState.SiteHolds site first) :
 GeneralNominalSaturationState.SiteHolds site last := by
 intro index origin found
 have old := valid index origin found
 refine ⟨(GeneralNominalOriginCongruence238.inhabited_iff same _).mp old.1,?_⟩
 intro value seen
 obtain ⟨before,observed,equal⟩ := GeneralNominalOriginCongruence238.observes
   (GeneralNominalAssignmentCongruence238.symm same) seen
 exact (GeneralNominalSchemaCongruence238.fits_iff same ⟨equal.2,equal.1⟩ _).mp (old.2 before observed)

theorem raw_site_iff (same : Same first last) (site : GeneralNominalDemandMerging.Site roles) :
 GeneralNominalSaturationState.SiteHolds site first ↔ GeneralNominalSaturationState.SiteHolds site last :=
 ⟨raw_site same,raw_site (GeneralNominalAssignmentCongruence238.symm same)⟩

theorem legacy_iff (same : Same first last) (state : State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state) :
 Legacy.Models state.legacy first ↔ Legacy.Models state.legacy last := by
 unfold Legacy.Models GeneralNominalCenteredHeadMatStepJournal.Models
 rw [empty.1,empty.2]
 simp only [List.not_mem_nil,false_implies]
 apply and_congr (GeneralNominalRawCongruence238.models_iff _ same)
 apply and_congr (GeneralNominalRawCongruence238.models_iff _ same)
 apply and_congr
 · exact forall_congr' fun site => forall_congr' fun _ => raw_site_iff same site
 · exact and_congr (forall_congr' fun site => forall_congr' fun _ => GeneralNominalSchemaCongruence238.site_iff same site) Iff.rfl

theorem models_iff (same : Same first last) (state : State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state) :
 Models state first ↔ Models state last := by
 apply and_congr (legacy_iff same state empty)
 apply and_congr
 · exact forall_congr' fun plan => forall_congr' fun _ => GeneralNominalVersionedPacketCongruence238.holds_iff same plan
 · exact forall_congr' fun effect => forall_congr' fun _ => GeneralNominalVersionedEffectCongruence238.effect_iff same state effect

theorem source_models_iff (same : Same first last)
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
 Models state first ↔ Models state last :=
 models_iff same state (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty path)

theorem normalized_full_model
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (valid : Models state first) : Models state (GeneralNominalVersionedHistoryEquations237.solution state first) :=
 (source_models_iff (GeneralNominalVersionedHistoryNormalization238.source_equivalent path valid) path).mpr valid
end Yulang.GeneralNominalVersionedSourceCongruence238
