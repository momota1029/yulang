import Yulang.GeneralMixedCompoundAnyChild307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
namespace Yulang.GeneralMixedCompoundTailEq307
open GeneralDictionaryJournalRefinement228Source (snapshot alias_zero width_two)
open GeneralDictionaryCompoundObstruction238 (oldPlan)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralMixedCompoundUpperSnapshot307 (snap refineRaw)
open GeneralMixedCompoundUpperRefresh307 (upperState models_iff)
open GeneralMixedCompoundUpperSupport307 (lower support_subset)
open GeneralMixedCompoundUpperTypes307 (entailed_kind)
open GeneralMixedCompoundUpperEqClosed307 (Related classify)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedKernel234 (Equal)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open CommonNominalFullCarrier

theorem source_restrict {m : Assignment} (valid : GeneralNominalState.Models extendedSnapshot m) :
    GeneralNominalState.Models snapshot m := by
  have current := GeneralNominalRefinements.models GeneralDictionaryCompoundSnapshot239.refines m valid
  exact (GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mp
    ⟨current.1,current.2.1,fun _ impossible => nomatch impossible⟩

theorem lower_raw (m : Assignment) (valid : GeneralNominalState.Models extendedSnapshot m) :
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

theorem upper_raw (m : Assignment) (valid : GeneralNominalState.Models extendedSnapshot m) :
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
    GeneralNominalFeedbackSteps.RawEqual refreshed.core.erased.current a b := by
  intro m valid
  rcases h with rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact alias_zero m (source_restrict valid)
  · have h := alias_zero m (source_restrict valid); exact ⟨h.2,h.1⟩
  · have h := upper_raw m valid; exact ⟨h.2,h.1⟩
  · exact upper_raw m valid
  · have h := lower_raw m valid; exact ⟨h.2,h.1⟩
  · exact lower_raw m valid

theorem at_anchor : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed refreshed := by
  intro a b one two equal
  have as := GeneralNominalRefinements.sources refineRaw _ one
  have bs := GeneralNominalRefinements.sources refineRaw _ two
  have semantic : Equal upperState a b := fun m valid => equal m ((models_iff m).mp valid)
  exact related_raw (classify a (support_subset as) b (support_subset bs) (entailed_kind as bs semantic))

theorem at_refresh {ctx : GeneralNominalCandidates.Context} (cert : Refresh refreshed ctx) :
    GeneralNominalVersionedMixedTerminalStable234.EqualityClosed (refresh refreshed ctx) := by
  intro a b one two equal
  have needed := at_anchor a b (cert.support _ one) (cert.support _ two)
    (fun m valid => equal m ((refresh_models cert).mpr valid))
  intro m raw
  exact needed m (GeneralNominalRefinements.models cert.refines m raw)

end Yulang.GeneralMixedCompoundTailEq307
