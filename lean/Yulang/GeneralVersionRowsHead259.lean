import Yulang.GeneralVersionRowsRaw259
import Yulang.GeneralDictionaryVersionLoopFamilyHead238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionRowsHead259
open GeneralDictionaryVersionLoopFamilyBase238
open GeneralDictionaryVersionLoopFamilySnapshot238 (snapshot context)
open GeneralDictionaryVersionLoopFamilyPacket238
open GeneralDictionaryVersionLoopSource237 (roles registry declaration root F)
open GeneralDictionaryVersionLoopNames238 (lower upper)
open GeneralDictionaryVersionLoopPacket237 (above_value)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralVersionRowsRaw259
variable (rows : Nat → Common.Row)

theorem observed_value {value : Ty} (index : Nat) (small : index < 2)
 (seen : Observes (withRows rows) (.nominal (.source 3) 5 index) value) : Equivalent value F :=
 GeneralDictionaryVersionLoopPacket237.observed_value index small
   (GeneralNominalTypeObservation259.observes (withRows rows) GeneralDictionaryVersionLoopSource237.model (fun _ => rfl) seen)

theorem seen0 : Observes (withRows rows) GeneralDictionaryVersionLoopPacket237.origin0 F :=
 GeneralNominalTypeObservation259.observes GeneralDictionaryVersionLoopSource237.model (withRows rows) (fun _ => rfl) GeneralDictionaryVersionLoopPacket237.seen0

theorem seen1 : Observes (withRows rows) GeneralDictionaryVersionLoopPacket237.origin1 F :=
 GeneralNominalTypeObservation259.observes GeneralDictionaryVersionLoopSource237.model (withRows rows) (fun _ => rfl) GeneralDictionaryVersionLoopPacket237.seen1

variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
theorem model_lower (n) : ((withRows rows) (lower n)).1 = F := by
 exact GeneralDictionaryVersionLoopFamilyHead238.model_lower n
theorem model_upper (n) : ((withRows rows) (upper n)).1 = F := GeneralDictionaryVersionLoopFamilyHead238.model_upper n
theorem fit_observed {value : Ty} (index : Nat) (small : index < 2) (seen : Observes (withRows rows) (.nominal (.source 3) 5 index) value) :
    Fits (snapshot n allocated reserved ordinary) (withRows rows) (anchor n,anchor n) value := by
  have equal := observed_value rows index small seen
  change Subtype ((withRows rows) (source n (anchor n))).1 value ∧ Subtype value ((withRows rows) (source n (anchor n))).1
  dsimp only [withRows]
  rw [model_anchor n]
  exact ⟨equal.2,equal.1⟩

theorem raw_projection : ProjectionModels (snapshot n allocated reserved ordinary) (report (context n allocated reserved ordinary) declaration [(original n 3,original n 3)]) (withRows rows) := by
  rw [report_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨_,seen0 rows⟩,fun _ seen => fit_observed rows n allocated reserved ordinary 0 (by decide) seen⟩
    · cases List.mem_singleton.mp member
      exact ⟨⟨_,seen1 rows⟩,fun _ seen => fit_observed rows n allocated reserved ordinary 1 (by decide) seen⟩
  · intro test member; cases member
  · intro first one last two _ origin located value seen
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj located
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals first | exact fit_observed rows n allocated reserved ordinary 0 (by decide) seen | exact fit_observed rows n allocated reserved ordinary 1 (by decide) seen
  · intro first one last two _ a b firstOrigin lastOrigin x y seenX seenY
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj firstOrigin
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals cases Option.some.inj lastOrigin
    all_goals
      have ex : Equivalent x F := by first | exact observed_value rows 0 (by decide) seenX | exact observed_value rows 1 (by decide) seenX
      have ey : Equivalent y F := by first | exact observed_value rows 0 (by decide) seenY | exact observed_value rows 1 (by decide) seenY
      exact ⟨subtype_trans ex.1 ey.2,subtype_trans ey.1 ex.2⟩

theorem merge_model : PresenceNormalForm.All CommonNominalFullCarrier.model (withRows rows)
    (GeneralNominalVersionedAllocation231.merges (snapshot n allocated reserved ordinary) registry root.identity declaration (packet n allocated reserved ordinary).bindings) := by
  rw [bindings_exact]
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model (withRows rows)
      (GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ++
        GeneralNominalAllocation.equations (upper n) (.inter (.var (lower n)) (.var (lower n)))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent ((withRows rows) (lower (n+1))).1 (.union ((withRows rows) (lower n)).1 ((withRows rows) (lower n)).1) ∧
      Equivalent ((withRows rows) (upper n)).1 (.inter ((withRows rows) (lower n)).1 ((withRows rows) (lower n)).1)
    rw [model_lower rows,model_lower rows,model_upper rows]
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model (withRows rows) (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩

theorem head_model (atoms : PresenceNormalForm.All CommonNominalFullCarrier.model (withRows rows) ordinary) : GeneralNominalVersionedCandidates231.HeadModels registry (context n allocated reserved ordinary) root declaration [(original n 3,original n 3)] (withRows rows) := by
  refine ⟨?_,raw_projection rows n allocated reserved ordinary⟩
  unfold GeneralNominalVersionedCandidates231.privateState
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalVersionedAllocation231.propagate_models ..).mpr ⟨raw_models rows n allocated reserved ordinary atoms,?_,merge_model rows n allocated reserved ordinary⟩,?_⟩
  · change GeneralNominalAllocation.Compatible (packet n allocated reserved ordinary).bindings (withRows rows)
    rw [bindings_exact]
    intro first one last two _
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals exact subtype_refl _
  · rw [report_exact]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals first | exact subtype_refl _ | exact subtype_refl _

end Yulang.GeneralVersionRowsHead259
