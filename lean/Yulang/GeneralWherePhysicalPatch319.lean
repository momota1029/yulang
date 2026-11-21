import Yulang.GeneralWherePhysicalTicket319
import Yulang.GeneralWhereOriginSupport318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 27000000
namespace Yulang.GeneralWherePhysicalPatch319
open GeneralWhereOriginSingleSource318 (older oldPlan declaration)
open GeneralWhereOriginSingleModel318 (presentLo patched patched_outside older_absent previousLo previousHi new_lo_ne_hi)
open GeneralWhereOriginSingleCells318 (loNow loOld hi oldChild exact_old lower_moves)
open GeneralWherePhysicalOldModel319 (m)
open GeneralWherePhysicalReobserve319 (updated updated_model)
open GeneralWherePhysicalPast319 (point)
open GeneralWherePhysicalFresh319 (fresh_sources)
open GeneralDictionaryJournalRefinement228Source (snapshot root)
open GeneralWhereVersionInstall317 (Models)
open GeneralWhereOriginSupport318 (journalSources journal_models planSources childrenSupport)
open GeneralNominalState (sources)
open GeneralNominalIdentities (source)
open GeneralNominalVersionedFrame231 (binder)
open GeneralWherePhysicalOldValues319 (old_binder)
open GeneralNominalCenteredFrame179 (siteSources)
open GeneralNominalCenteredEmptyFrame179 (rawSiteSources)

noncomputable abbrev n := patched m

theorem different_small (key : GeneralNominalIdentities.Origin) (small : key.2.2.1 ≤ 9) :
    loNow ≠ source snapshot.seed key := by
  obtain ⟨k,large,eq⟩ := presentLo.high (t := snapshot) rfl
  change loNow = source snapshot.seed k at eq
  rw [eq]
  exact GeneralVersionedHighOrigins315.distinct (a := k) (b := key) (by omega) snapshot.seed

theorem different_ordinary (k : Nat) (small : k ≤ 4) : loNow ≠ k := by
  intro eq
  apply older_absent loNow (presentLo.high rfl)
  let j : Fin 5 := ⟨k,by omega⟩
  have raw := GeneralNominalAllocationSupport.slot_source snapshot j
  change k ∈ sources snapshot at raw
  exact eq ▸ raw

theorem different_binder (i) (known : i = 0 ∨ i = 1) : loNow ≠ binder oldPlan i := by
  rw [old_binder i known]
  exact different_small _ (by change (8 : Nat) ≤ 9; decide)

theorem different_mid : loNow ≠ GeneralMixedCompoundChildEquality307.mid :=
  different_small (GeneralNominalAllocation.origin root.identity declaration.id 9 GeneralLiveCompoundRegistry316.otherChild.id 0) (by decide)

theorem child_site : siteSources oldChild = [loOld,hi,GeneralMixedCompoundChildEquality307.mid] := by
  unfold siteSources
  rw [List.ofFn_succ]
  change [ (oldChild.occurrence.demand.arguments 0).1,
    (oldChild.occurrence.demand.arguments 0).2,oldChild.center 0] = _
  rw [exact_old]
  rfl

theorem old_capture_sources :
    GeneralNominalVersionedPacketFrame236.captureSources oldPlan = [4,2,binder oldPlan 0,4,2,binder oldPlan 1,4,2,binder oldPlan 0] := by
  rw [GeneralNominalVersionedPacketFrame236.captureSources]
  change (List.flatMap (fun name => [((GeneralNominalVersionedFrame231.capture older).inputs name).1,
    ((GeneralNominalVersionedFrame231.capture older).inputs name).2,binder oldPlan name]) [0,1,0]) = _
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,
    GeneralWherePhysicalOldValues319.old_capture 0 (.inl rfl),GeneralWherePhysicalOldValues319.old_capture 1 (.inr rfl)]
  rfl

theorem exclude_plan : loNow ∉ planSources oldPlan := by
  intro hit
  unfold planSources at hit
  simp only [List.mem_append] at hit
  rcases hit with ((((head|input)|cap)|tests)|rows)|kids
  · exact GeneralWhereOriginHeadAgree318.head_not_written (p := oldPlan) List.mem_cons_self
      (presentLo.high rfl) (older_absent _ (presentLo.high rfl)) head
  · change loNow ∈ [0,0,0] at input
    simp [different_ordinary 0 (by decide)] at input
  · rw [old_capture_sources] at cap
    simp [different_ordinary 4 (by decide),different_ordinary 2 (by decide),
      different_binder 0 (.inl rfl),different_binder 1 (.inr rfl)] at cap
  · rw [GeneralWherePhysicalOldHead319.schema_code] at tests
    change loNow ∈ [0,0,binder oldPlan 0,0,binder oldPlan 1] at tests
    simp [different_ordinary 0 (by decide),different_binder 0 (.inl rfl),different_binder 1 (.inr rfl)] at tests
  · unfold GeneralNominalVersionedExpressionFrame236.schemaSources at rows
    rw [GeneralWherePhysicalOldModel319.emitted_rows] at rows
    change loNow ∈ [4,loOld,GeneralNominalVersionedExpressionFrame236.variableSource oldPlan .lower 0,
      hi,GeneralNominalVersionedExpressionFrame236.variableSource oldPlan .upper 0] at rows
    rw [GeneralWhereOriginSingleRead318.old_reads.1,GeneralWhereOriginSingleRead318.old_reads.2] at rows
    simp [different_ordinary 4 (by decide),different_ordinary 2 (by decide),lower_moves.symm,new_lo_ne_hi] at rows
  · obtain ⟨a,_,used⟩ := List.mem_flatMap.mp kids
    rcases a with ⟨c,member⟩
    cases List.mem_singleton.mp member
    change loNow ∈ siteSources oldChild ++ GeneralNominalVersionedExpressionFrame236.schemaSources oldPlan
      (GeneralNominalVersionedPlans231.childSchema oldPlan GeneralLiveCompoundRegistry316.otherChild GeneralWhereOriginSingleCells318.sig) at used
    rw [child_site,GeneralWherePhysicalOldModel319.child_row] at used
    change loNow ∈ [loOld,hi,GeneralMixedCompoundChildEquality307.mid,GeneralMixedCompoundChildEquality307.mid,binder oldPlan 0] at used
    simp [lower_moves.symm,new_lo_ne_hi,different_mid,different_binder 0 (.inl rfl)] at used


theorem patch_preserves (k : Nat) (none : loNow ≠ k) : m k = n k :=
  patched_outside m k none

theorem ordinary_same (k : Nat) (small : k ≤ 4) : m k = n k :=
  patch_preserves k (different_ordinary k small)

theorem old_holds : GeneralWhereVersionSemantics317.Holds oldPlan n := by
  apply (GeneralWhereOriginSupport318.plan_holds oldPlan (first := m) (last := n) ?_).mp
    GeneralWherePhysicalOldModel319.full
  intro k found
  exact patch_preserves k (fun same => exclude_plan (same.symm ▸ found))

theorem prior_raw : GeneralNominalState.Models snapshot n := by
  have original := GeneralWherePhysicalOldInstall319.prior_model.1.1.1
  apply GeneralNominalCenteredModelExtension.source_models_same snapshot ?_ original
  intro k used
  exact patch_preserves k (fun same => (older_absent loNow (presentLo.high rfl)) (same.symm ▸ used))

theorem physical_raw : GeneralNominalState.Models point n := by
  have original := updated_model.1.1.1
  apply GeneralNominalCenteredModelExtension.source_models_same point ?_ original
  intro k used
  exact patch_preserves k (fun same => fresh_sources (same.symm ▸ used))

theorem prior_model : Models GeneralWherePhysicalOldHead319.before n := by
  refine ⟨(GeneralNominalVersionedJournal232.initial_models _ root n).mpr
    ⟨prior_raw,GeneralNominalCenters.point_root_holds _ _ GeneralDictionaryJournalRefinement228Source.root_point n⟩,?_⟩
  intro _ impossible
  cases impossible

theorem prior_class : GeneralNominalVersionedEffects231.ClassEffects
    GeneralWherePhysicalOldHead319.start.core root oldPlan n := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro out used body resolved
    cases GeneralWherePhysicalOldPick319.all_requests root out used
    have expected : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ :=
      Option.some.inj resolved |>.symm
    subst body
    intro row member
    cases List.mem_singleton.mp member
    change CommonNominalFullCarrier.Equivalent (n 4).1 GeneralDictionaryOptionalOutput229.value
    rw [show (n 4).1 = (m 4).1 from congrArg Prod.fst (ordinary_same 4 (by decide)).symm]
    exact GeneralWherePhysicalOldModel319.actual_m
  · intro a h b i _
    cases GeneralWherePhysicalOldPick319.all_requests root a h
    cases GeneralWherePhysicalOldPick319.all_requests root b i
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem compatible_update : Models updated n := by
  apply (GeneralWherePhysicalReobserve319.models_unchanged n).mpr
  exact GeneralWhereOriginSuccessor318.with_parent prior_model
    ((GeneralWherePhysicalPast319.point_models n).mp physical_raw)
    old_holds prior_class GeneralWherePhysicalOldInstall319.silent

end Yulang.GeneralWherePhysicalPatch319
