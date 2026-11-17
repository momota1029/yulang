import Yulang.GeneralDictionaryLooseFamilyPacket240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseFamilyHead240
open GeneralDictionaryLooseFamilyBase240 GeneralDictionaryLooseFamilySnapshot240 GeneralDictionaryLooseFamilyPacket240
open GeneralDictionaryLooseLoopSource240 (roles registry declaration root model F)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryLooseLoopPacket240 (seen0 seen1 observed_value above_value)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
theorem model_lower (n) : (model (lower n)).1 = F := by
 cases n with
 | zero => rfl
 | succ n => exact above_value _ (GeneralDictionaryLooseFamilyNames240.lower_above n)
theorem model_upper (n) : (model (upper n)).1 = F := above_value _ (GeneralDictionaryLooseFamilyNames240.upper_above n)
theorem fit_observed {value : Ty} (index : Nat) (small : index < 2) (seen : Observes model (.nominal (.source 3) 5 index) value) :
    Fits (snapshot n allocated reserved ordinary) model (anchor n,original n 4) value := by
  have equal := observed_value index small seen
  change Subtype (model (source n (anchor n))).1 value ∧ Subtype value (model (source n (original n 4))).1
  rw [model_anchor n]
  change Subtype F value ∧ Subtype value F
  exact ⟨equal.2,equal.1⟩

theorem raw_projection : ProjectionModels (snapshot n allocated reserved ordinary) (report (context n allocated reserved ordinary) declaration [(original n 3,original n 3)]) model := by
  rw [report_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨_,seen0⟩,fun _ seen => fit_observed n allocated reserved ordinary 0 (by decide) seen⟩
    · cases List.mem_singleton.mp member
      exact ⟨⟨_,seen1⟩,fun _ seen => fit_observed n allocated reserved ordinary 1 (by decide) seen⟩
  · intro test member; cases member
  · intro first one last two _ origin located value seen
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj located
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals first | exact fit_observed n allocated reserved ordinary 0 (by decide) seen | exact fit_observed n allocated reserved ordinary 1 (by decide) seen
  · intro first one last two _ a b firstOrigin lastOrigin x y seenX seenY
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj firstOrigin
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals cases Option.some.inj lastOrigin
    all_goals
      have ex : Equivalent x F := by first | exact observed_value 0 (by decide) seenX | exact observed_value 1 (by decide) seenX
      have ey : Equivalent y F := by first | exact observed_value 0 (by decide) seenY | exact observed_value 1 (by decide) seenY
      exact ⟨subtype_trans ex.1 ey.2,subtype_trans ey.1 ex.2⟩

theorem merge_model : PresenceNormalForm.All CommonNominalFullCarrier.model model
    (GeneralNominalVersionedAllocation231.merges (snapshot n allocated reserved ordinary) registry root.identity declaration (packet n allocated reserved ordinary).bindings) := by
  rw [bindings_exact]
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ++
        GeneralNominalAllocation.equations (upper n) (.inter (.var 4) (.var 4))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent (model (lower (n+1))).1 (.union (model (lower n)).1 (model (lower n)).1) ∧
      Equivalent (model (upper n)).1 (.inter (model 4).1 (model 4).1)
    rw [model_lower,model_lower,model_upper]
    change Equivalent F (.union F F) ∧ Equivalent F (.inter F F)
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model model (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩

theorem head_model (atoms : PresenceNormalForm.All CommonNominalFullCarrier.model model ordinary) : GeneralNominalVersionedCandidates231.HeadModels registry (context n allocated reserved ordinary) root declaration [(original n 3,original n 3)] model := by
  refine ⟨?_,raw_projection n allocated reserved ordinary⟩
  unfold GeneralNominalVersionedCandidates231.privateState
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalVersionedAllocation231.propagate_models ..).mpr ⟨raw_models n allocated reserved ordinary atoms,?_,merge_model n allocated reserved ordinary⟩,?_⟩
  · change GeneralNominalAllocation.Compatible (packet n allocated reserved ordinary).bindings model
    rw [bindings_exact]
    intro first one last two _
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals
      change Subtype (model (lower n)).1 F
      rw [model_lower]
      exact subtype_refl _
  · rw [report_exact]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals
      first
      | exact subtype_refl _
      | change Subtype (model (source n (anchor n))).1 F
        rw [model_anchor]
        exact subtype_refl _

end Yulang.GeneralDictionaryLooseFamilyHead240
