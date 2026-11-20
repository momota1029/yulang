import Yulang.GeneralMixedCompoundUpperTypes307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralMixedCompoundUpperEqClosed307
open GeneralDictionaryJournalRefinement228Source (snapshot alias_zero width_two root)
open GeneralDictionaryCompoundSource238 (registry declaration)
open GeneralDictionaryCompoundObstruction238 (oldPlan)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundUpperBase307 (upper base)
open GeneralMixedCompoundUpperSnapshot307 (snap refineRaw)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundUpperSupport307 (lower identity support_subset)
open GeneralMixedCompoundUpperTypes307 (kind entailed_kind)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFeedbackSteps (RawEqual)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open CommonNominalFullCarrier

def Related (a b : Nat) : Prop :=
  a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
    (a = 2 ∧ b = upper) ∨ (a = upper ∧ b = 2) ∨
    (a = 4 ∧ b = lower) ∨ (a = lower ∧ b = 4)

instance (a b : Nat) : Decidable (Related a b) :=
  inferInstanceAs (Decidable (_ = _ ∨ (_ = _ ∧ _ = _) ∨ (_ = _ ∧ _ = _) ∨
    (_ = _ ∧ _ = _) ∨ (_ = _ ∧ _ = _) ∨ (_ = _ ∧ _ = _) ∨ (_ = _ ∧ _ = _)))

theorem classify :
  ∀ a ∈ [0,1,2,3,4,lower,upper,identity,lo,hi], ∀ b ∈ [0,1,2,3,4,lower,upper,identity,lo,hi],
    kind a = kind b → Related a b := by decide +kernel

theorem source_restrict {m : Assignment} (valid : GeneralNominalState.Models snap m) :
    GeneralNominalState.Models snapshot m := by
  have current := GeneralNominalRefinements.models GeneralDictionaryCompoundSnapshot239.refines m
    (GeneralNominalRefinements.models refineRaw m valid)
  exact (GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mp
    ⟨current.1,current.2.1,fun _ impossible => nomatch impossible⟩

theorem upper_raw (m : Assignment) (valid : GeneralNominalState.Models snap m) :
    Equivalent (m upper).1 (m 2).1 := by
  have read : Equivalent (m upper).1 .emptyRecord :=
    valid.1.2.1 (7 : Fin 8) .emptyRecord rfl
  have w := width_two m (source_restrict valid)
  exact equivalent_trans read ⟨w.2,w.1⟩

theorem lower_raw (m : Assignment) (valid : GeneralNominalState.Models snap m) :
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

theorem related_raw (h : Related a b) :
    RawEqual upperState.core.erased.current a b := by
  intro m valid
  rcases h with rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact alias_zero m (source_restrict valid)
  · have h := alias_zero m (source_restrict valid); exact ⟨h.2,h.1⟩
  · have h := upper_raw m valid; exact ⟨h.2,h.1⟩
  · exact upper_raw m valid
  · have h := lower_raw m valid; exact ⟨h.2,h.1⟩
  · exact lower_raw m valid

theorem equality_closed : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed upperState :=
  fun a b one two eq => related_raw (classify a (support_subset one) b (support_subset two)
    (entailed_kind one two eq))

end Yulang.GeneralMixedCompoundUpperEqClosed307
