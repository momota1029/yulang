import Yulang.GeneralMixedCompoundPointSpine307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
namespace Yulang.GeneralMixedCompoundPointEquality307
open GeneralDictionaryJournalRefinement228Source (snapshot alias_zero)
open GeneralDictionaryCompoundObstruction238 (oldPlan)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralMixedCompoundUpperSupport307 (lower support_subset)
open GeneralMixedCompoundUpperTypes307 (kind entailed_kind)
open GeneralMixedCompoundUpperEqClosed307 (Related classify)
open GeneralMixedCompoundRefreshBound307 (Run support models)
open GeneralMixedCompoundPointSpine307 (raw_base)
open GeneralNominalVersionedMixedKernel234 (Equal)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem source_restrict {m : Assignment} (valid : GeneralNominalState.Models point.core.erased.current.context.state m) :
    GeneralNominalState.Models snapshot m := by
  exact (GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mp
    ⟨valid.1,valid.2.1,fun _ impossible => nomatch impossible⟩

theorem lower_raw (m : Assignment) (valid : GeneralNominalState.Models point.core.erased.current.context.state m) :
    Equivalent (m lower).1 (m 4).1 := by
  have atoms := valid.2.2
  change PresenceNormalForm.All CommonNominalFullCarrier.model m
    (GeneralNominalVersionedInstallation231.atoms oldPlan.packet) at atoms
  unfold GeneralNominalVersionedInstallation231.atoms at atoms
  have merge := ((PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp atoms).1).2
  rw [GeneralDictionaryCompoundPacket238.bindings_exact] at merge
  change PresenceNormalForm.All CommonNominalFullCarrier.model m
    ((GeneralNominalAllocation.equations lower (.union (.var 4) (.var 4)) ++ _) ++ _) at merge
  have pair := ((PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merge).1).1
  have eq := (GeneralNominalCaptureMerges.equations_exact ..).mp pair
  change Equivalent (m lower).1 (.union (m 4).1 (m 4).1) at eq
  exact ⟨subtype_trans eq.1 ((common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩),
    subtype_trans ((common_union_is_join _ _ _).mp (subtype_refl _)).1 eq.2⟩

theorem upper_raw (m : Assignment) (valid : GeneralNominalState.Models point.core.erased.current.context.state m) :
    Equivalent (m upper).1 (m 2).1 := by
  have atoms := valid.2.2
  change PresenceNormalForm.All CommonNominalFullCarrier.model m
    (GeneralNominalVersionedInstallation231.atoms oldPlan.packet) at atoms
  unfold GeneralNominalVersionedInstallation231.atoms at atoms
  have merge := ((PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp atoms).1).2
  rw [GeneralDictionaryCompoundPacket238.bindings_exact] at merge
  change PresenceNormalForm.All CommonNominalFullCarrier.model m
    ((_ ++ GeneralNominalAllocation.equations upper (.inter (.var 2) (.var 2))) ++ _) at merge
  have pair := ((PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merge).1).2
  have eq := (GeneralNominalCaptureMerges.equations_exact ..).mp pair
  change Equivalent (m upper).1 (.inter (m 2).1 (m 2).1) at eq
  exact ⟨subtype_trans eq.1 ((common_inter_is_meet _ _ _).mp (subtype_refl _)).1,
    subtype_trans ((common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩) eq.2⟩

theorem related_raw (h : Related a b) :
    GeneralNominalFeedbackSteps.RawEqual point.core.erased.current a b := by
  intro m valid
  rcases h with rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact alias_zero m (source_restrict valid)
  · have h := alias_zero m (source_restrict valid); exact ⟨h.2,h.1⟩
  · have h := upper_raw m valid; exact ⟨h.2,h.1⟩
  · exact upper_raw m valid
  · have h := lower_raw m valid; exact ⟨h.2,h.1⟩
  · exact lower_raw m valid


theorem closed (p : Run n s) : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed s := by
  intro a b one two equal m raw
  have x := support p one
  have y := support p two
  have same := entailed_kind x y (fun z valid => equal z ((models p z).mpr valid))
  exact related_raw (classify a (support_subset x) b (support_subset y) same) m (raw_base p m raw)

/-- On every supported pair of every state on the actual point suffix, the
seven finite tags decide both raw and full semantic equality exactly. -/
theorem exact_pair (p : Run n s)
    (one : a ∈ GeneralMixedCompoundRefreshBound307.pool s)
    (two : b ∈ GeneralMixedCompoundRefreshBound307.pool s) :
    (GeneralNominalFeedbackSteps.RawEqual s.core.erased.current a b ↔ kind a = kind b) ∧
    (Equal s a b ↔ kind a = kind b) := by
  have x := support p one
  have y := support p two
  have raw_to_full (h : GeneralNominalFeedbackSteps.RawEqual s.core.erased.current a b) : Equal s a b :=
    fun m valid => h m valid.1.1
  have match_kind (h : Equal s a b) : kind a = kind b :=
    entailed_kind x y (fun m valid => h m ((models p m).mpr valid))
  have to_raw (h : kind a = kind b) : GeneralNominalFeedbackSteps.RawEqual s.core.erased.current a b :=
    fun m valid => related_raw (classify a (support_subset x) b (support_subset y) h) m (raw_base p m valid)
  exact ⟨⟨fun h => match_kind (raw_to_full h),to_raw⟩,⟨match_kind,fun h => raw_to_full (to_raw h)⟩⟩

end Yulang.GeneralMixedCompoundPointEquality307
