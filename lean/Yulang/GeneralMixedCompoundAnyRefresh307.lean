import Yulang.GeneralMixedCompoundUpperHalt307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralMixedCompoundAnyRefresh307
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot pointDesc)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralMixedCompoundUpperSnapshot307 (snap refineRaw)
open GeneralMixedCompoundUpperRefresh307 (upperState models_iff)
open GeneralMixedCompoundUpperSupport307 (lower identity unknown_cases headless known_0 known_1 known_2 known_lo known_hi)
open GeneralMixedCompoundUpperTypes307 (kind tag meaning tagged top_tag_conflict classifierModel classifier_model model_class)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known sources)
open GeneralNominalRefinements (Refines)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryInspectionHeads215 (Tagged tag_subtype tagged_equivalent nominal_slot)
open CommonNominalFullCarrier

abbrev Ctx := GeneralNominalCandidates.Context

theorem known_origin :
    ∀ n, Known snap n → n = upper ∨ Known extendedSnapshot n := by
  have oldSlot : ∀ i : Fin 7, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by decide +kernel
  rintro n ⟨i,eq,known⟩
  revert eq known
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro eq _
    exact Or.inl (eq.symm.trans GeneralMixedCompoundUpperBase307.source_new)
  · intro eq flags
    have original := GeneralMixedCompoundUpperBase307.source_old j
    rcases oldSlot j with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact Or.inr ⟨0,original.symm.trans eq,Or.inr ⟨_,rfl⟩⟩
    · exact Or.inr ⟨1,original.symm.trans eq,Or.inr ⟨_,rfl⟩⟩
    · exact Or.inr ⟨2,original.symm.trans eq,Or.inl (by decide +kernel)⟩
    · rcases flags with bad|⟨_,bad⟩
      · exact False.elim (bad rfl)
      · cases bad
    · rcases flags with bad|⟨_,bad⟩
      · exact False.elim (bad rfl)
      · cases bad
    · exact Or.inr ⟨5,original.symm.trans eq,Or.inl (by decide +kernel)⟩
    · exact Or.inr ⟨6,original.symm.trans eq,Or.inl (by decide +kernel)⟩

theorem can_gain_only_upper (ctx : Ctx) (cert : Refresh refreshed ctx)
    (n : Nat) (was : ¬ Known extendedSnapshot n) (now : Known ctx.state n) :
    n = upper := by
  by_cases gain : Known snap n
  · exact (known_origin n gain).elim id (fun h => (was h).elim)
  · have located := now
    obtain ⟨s,eq,_⟩ := located
    have member := cert.support _ (eq ▸ GeneralNominalAllocationSupport.slot_source ctx.state s)
    have inside := GeneralNominalRefinements.sources refineRaw _ member
    obtain ⟨m,valid,nohead⟩ := headless
    have ready := (refresh_models cert).mpr ((models_iff m).mp valid)
    obtain ⟨test,obs,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head now
    have held := GeneralCanonicalObservations.recorded_sound ctx.state m ready.1.1
      (GeneralNominalSupport.head_recorded head)
    exact (nohead n inside gain test (GeneralDictionaryGroundCopy218Refresh.head_holds head held)).elim

theorem all_known_covered (ctx : Ctx) (cert : Refresh refreshed ctx) (gain : Known ctx.state upper)
    (n : Nat) (hn : Known snap n) : Known ctx.state n := by
  rcases known_origin n hn with rfl|old
  · exact gain
  · exact cert.refines.known n old

theorem no_further_refresh (ctx : Ctx) (cert : Refresh refreshed ctx) (gain : Known ctx.state upper)
    (next : Ctx) (again : Refresh (refresh refreshed ctx) next)
    (n : Nat) (present : n ∈ sources ctx.state) (was : ¬ Known ctx.state n) : ¬ Known next.state n := by
  intro now
  have inside := GeneralNominalRefinements.sources refineRaw _ (cert.support _ present)
  have missing : ¬ Known snap n := fun h => was (all_known_covered ctx cert gain n h)
  obtain ⟨m,valid,nohead⟩ := headless
  have moved := (refresh_models again).mpr ((refresh_models cert).mpr ((models_iff _).mp valid))
  obtain ⟨test,obs,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head now
  have holds := GeneralCanonicalObservations.recorded_sound next.state m moved.1.1
    (GeneralNominalSupport.head_recorded head)
  exact nohead n inside missing test (GeneralDictionaryGroundCopy218Refresh.head_holds head holds)

theorem nominal_class (n : Nat) (_present : n ∈ sources snap)
    (classified : Tagged (meaning (kind n)) (.nominal name arity)) : n = 0 ∨ n = 1 := by
  cases k : kind n with
  | nominal =>
    unfold kind at k
    by_cases first : n = 0 ∨ n = 1
    · exact first
    · simp only [ite_eq_right first] at k
      split at k <;> (try split at k) <;> (try split at k) <;> (try split at k) <;>
        (try split at k) <;> cases k
  | top =>
    rw [k] at classified
    exact False.elim (top_tag_conflict classified (subtype_refl _))
  | width | optional | variantOptional | variantWidth | index =>
    rw [k] at classified
    first
      | cases tag_subtype classified (tagged .width (t := .records) rfl) (subtype_refl _)
      | cases tag_subtype classified (tagged .optional (t := .records) rfl) (subtype_refl _)
      | cases tag_subtype classified (tagged .variantOptional (t := .variant 0) rfl) (subtype_refl _)
      | cases tag_subtype classified (tagged .variantWidth (t := .variant 0) rfl) (subtype_refl _)
      | cases tag_subtype classified (tagged .index (t := .base .int) rfl) (subtype_refl _)

theorem nominal_read (ctx : Ctx) (cert : Refresh refreshed ctx) (slot : Fin ctx.state.base.slots)
    (descriptor) (present : ctx.state.nominals slot = some descriptor) :
    ctx.state.base.source slot = 0 ∨ ctx.state.base.source slot = 1 := by
  let n := ctx.state.base.source slot
  have mem := GeneralNominalRefinements.sources refineRaw n
    (cert.support n (GeneralNominalAllocationSupport.slot_source ctx.state slot))
  have raw := (refresh_models cert).mpr ((models_iff _).mp classifier_model)
  have nTag := nominal_slot raw.1.1 present
  have shape := model_class n mem
  exact nominal_class n mem (tagged_equivalent ⟨shape.2,shape.1⟩ nTag)

theorem point_closed (ctx : Ctx) (cert : Refresh refreshed ctx) :
    GeneralNominalReobservationSteps.PointClosed ctx.state := by
  intro slot descriptor present
  let n := ctx.state.base.source slot
  have nClass := nominal_read ctx cert slot descriptor present
  have inherited (old : Fin 7) (eq : GeneralDictionaryCompoundBase239.source old = n)
      (d : extendedSnapshot.nominals old = some pointDesc) :
      descriptor = GeneralNominalRefinements.renameDescriptor cert.refines.base.embed pointDesc := by
    have name := (cert.refines.base.source old).trans eq
    have slotEq := ctx.state.base.source_injective name
    have same := cert.refines.nominals old pointDesc d
    rw [slotEq,present] at same
    exact Option.some.inj same
  have exactDesc : descriptor = GeneralNominalRefinements.renameDescriptor cert.refines.base.embed pointDesc := by
    rcases nClass with zero|one
    · exact inherited 0 zero.symm rfl
    · exact inherited 1 one.symm rfl
  subst descriptor
  intro param member
  change param ∈ [.type ((cert.refines.base.embed (2 : Fin 7)),(cert.refines.base.embed (2 : Fin 7))),
    .type ((cert.refines.base.embed (2 : Fin 7)),(cert.refines.base.embed (2 : Fin 7)))] at member
  rcases List.mem_cons.mp member with same|rest
  · subst param; rfl
  · cases List.mem_singleton.mp rest; rfl

end Yulang.GeneralMixedCompoundAnyRefresh307
