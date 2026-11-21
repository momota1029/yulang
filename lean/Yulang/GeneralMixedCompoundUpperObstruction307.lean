import Yulang.GeneralMixedCompoundUpperRoot307
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedCompoundUpperObstruction307
open GeneralDictionaryJournalRefinement228Source GeneralDictionaryCompoundSource238
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralDictionaryCompoundObstruction238 (oldPlan old_lower associated_value)
open GeneralNominalVersionedPlans231 GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
noncomputable abbrev currentPlan := GeneralMixedCompoundUpperRoot307.plan
private theorem union_same {a b : Ty} (equal : Equivalent a (.union b b)) : Equivalent a b :=
  ⟨subtype_trans equal.1 ((common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩),
    subtype_trans ((common_union_is_join _ _ _).mp (subtype_refl (.union b b))).1 equal.2⟩
theorem current_lower (model : Assignment) (valid : Holds currentPlan model) :
    Equivalent (model ((GeneralNominalVersionedFrame231.capture currentPlan.packet).inputs 0).1).1 (model 2).1 := by
  have merges := valid.2.1.1.2.1
  rw [GeneralMixedCompoundUpperRoot307.bindings_exact] at merges
  change PresenceNormalForm.All CommonNominalFullCarrier.model model
    ((GeneralNominalAllocation.equations
      (GeneralNominalAggregateVersion231.slot snapshot.seed root.identity declaration.id 0 0 [(0,2,2),(0,2,2)])
      (.union (.var 2) (.var 2)) ++ _) ++ _) at merges
  have lower := (PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merges).1 |>.1
  have equal := (GeneralNominalCaptureMerges.equations_exact ..).mp lower
  have capture : ((GeneralNominalVersionedFrame231.capture currentPlan.packet).inputs 0).1 =
      GeneralNominalAggregateVersion231.slot snapshot.seed root.identity declaration.id 0 0 [(0,2,2),(0,2,2)] := by
    change ((GeneralNominalVersionedAllocation231.capture _ _ _ _ currentPlan.packet.bindings).inputs 0).1 = _
    rw [GeneralMixedCompoundUpperRoot307.bindings_exact]
    rfl
  rw [capture]
  exact union_same equal

theorem no_current_packet (model : Assignment) (valid : GeneralNominalVersionedJournal232.Models upperState model) :
    ¬ Holds currentPlan model := by
  intro current
  have old := valid.2.1 oldPlan GeneralDictionaryCompoundPoint238.original_plan_retained
  have fixed := GeneralNominalVersionedCompoundEndpoint237.simultaneous_lower_equivalent oldPlan currentPlan model child
    (List.mem_singleton_self _) (List.mem_singleton_self _) (by exact ⟨rfl,by intro _ h; cases h⟩) 0 rfl
    (by decide +kernel) (by decide +kernel) rfl rfl rfl old.2.2 current.2.2
  have lo := old_lower model old
  have hi := current_lower model current
  have associated := associated_value model old
  have width := width_two model old.1
  exact GeneralDictionaryOptionalOutput229.not_width
    ⟨subtype_trans associated.2 (subtype_trans lo.2 (subtype_trans fixed.1 (subtype_trans hi.1 width.1))),
      subtype_trans width.2 (subtype_trans hi.2 (subtype_trans fixed.2 (subtype_trans lo.1 associated.1)))⟩

theorem no_common : ¬ ∃ model, GeneralNominalVersionedJournal232.Models upperState model ∧ Holds currentPlan model := by
  rintro ⟨model,valid,held⟩
  exact no_current_packet model valid held

theorem no_install_root (e : GeneralNominalVersionedJournal232.Effect roles)
    (enabled : GeneralNominalVersionedMixedKernel234.Installable registry upperState e)
    (he : e.plan.packet.site.occurrence = root) : False := by
  have frame := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,he] at frame
  have chosen := GeneralMixedCompoundUpperRoot307.frame_plan frame
  obtain ⟨m,before,packet,_⟩ := enabled.common
  rw [chosen] at packet
  exact no_current_packet m before packet

theorem no_install_child (e : GeneralNominalVersionedJournal232.Effect roles)
    (enabled : GeneralNominalVersionedMixedKernel234.Installable registry upperState e)
    (he : e.plan.packet.site.occurrence = GeneralDictionaryCompoundSites238.childSite.occurrence) : False := by
  have frame := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,he] at frame
  exact GeneralMixedCompoundUpperChild307.no_frame _ _ frame

end Yulang.GeneralMixedCompoundUpperObstruction307
