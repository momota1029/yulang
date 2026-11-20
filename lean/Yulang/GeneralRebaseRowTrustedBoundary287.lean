import Yulang.GeneralRebaseRowSettlement287

/-! Until the actual emitted child is ledger-discharged, the finite support
slices of this journal validate under the original source condition. The full
journal nevertheless constrains the parent output. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowTrustedBoundary287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowChildRaw287 (SourceCheck exact_source)
open GeneralRebaseRowParentPacket287 (plan packet child)
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseRowParentInputs287 (ordinary inputs_hold)
open GeneralRebaseRowSettlement287 (parent_not_settled)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedMixedObservations233 (CacheSound)
open CommonNominalFullCarrier (Equivalent)

theorem raw_after (choice : Bool) (m : Assignment) :
    GeneralNominalState.Models (current choice).state m ↔ SourceCheck m := by
  change GeneralNominalState.Models (GeneralNominalVersionedInstallation231.replayPlan (plan choice)).packet.context.state m ↔ _
  rw [GeneralNominalVersionedInstallation231.replay_private_models,
    GeneralNominalVersionedPlans231.private_models_iff]
  exact (and_iff_left (ordinary choice m)).trans (exact_source m)

theorem source_sites (choice : Bool) (m : Assignment) :
    ∀ site ∈ (after choice).core.sourceSites, site.Holds m := by
  intro site found
  change site ∈ [GeneralNominalCenters.rootSite raw.seed root] at found
  cases List.mem_singleton.mp found
  exact GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _

theorem legacy_slice (choice : Bool) (m : Assignment) (rawValid : SourceCheck m)
    {facts} (good : GeneralNominalCenteredHeadMatStepSupport.Trusted (after choice).legacy facts) :
    GeneralNominalCenteredHeadMatStepSupport.Models (after choice).legacy facts m := by
  refine ⟨(exact_source m).mpr rawValid,source_sites choice m,?_⟩
  induction good with
  | source => intro _ member; cases member
  | input _ _ recorded _ _ => cases recorded
  | output _ _ recorded _ _ _ _ _ => cases recorded
  | merge a b _ _ _ _ present _ _ ih =>
    intro fact member
    rcases List.mem_cons.mp member with rfl|member
    · exact fun atom inAtoms => ((raw_after choice m).mpr rawValid).2.2 atom (present atom inAtoms)
    · exact ih fact member

theorem versioned_slice (choice : Bool) (m : Assignment) (rawValid : SourceCheck m)
    {facts} (good : GeneralNominalVersionedSupport233.Trusted (after choice) facts) :
    GeneralNominalVersionedSupport233.SliceModels (after choice) facts m := by
  refine ⟨(exact_source m).mpr rawValid,source_sites choice m,?_⟩
  induction good with
  | source => intro _ member; cases member
  | input p _ recorded _ ih =>
    change p ∈ [plan choice] at recorded
    cases List.mem_singleton.mp recorded
    intro fact member
    rcases List.mem_cons.mp member with rfl|member
    · exact inputs_hold choice m ((exact_source m).mpr rawValid)
    · exact ih fact member
  | output e _ recorded _ _ _ settled _ =>
    change e ∈ [effect choice] at recorded
    cases List.mem_singleton.mp recorded
    exact (parent_not_settled choice settled).elim
  | merge a b _ _ _ _ present _ _ ih =>
    intro fact member
    rcases List.mem_cons.mp member with rfl|member
    · exact fun atom inAtoms => ((raw_after choice m).mpr rawValid).2.2 atom (present atom inAtoms)
    · exact ih fact member

theorem cache_only_source (choice : Bool) (snap : GeneralNominalState.State)
    (cache : CacheSound (after choice) snap) (observation : GeneralCanonicalObservations.Observation)
    (read : GeneralCanonicalObservations.Recorded snap observation)
    (m : Assignment) (sourceValid : SourceCheck m) : observation.Holds m := by
  obtain ⟨old,new,oldTrust,newTrust,prove⟩ := cache observation read
  exact prove m (legacy_slice choice m sourceValid oldTrust) (versioned_slice choice m sourceValid newTrust)

def putTop (m : Assignment) (k : Nat) : Assignment :=
  fun n => (if n = k then .top else (m n).1,(m n).2)

theorem outside_source (m : Assignment) {k : Nat} (high : 2 ≤ k) :
    SourceCheck (putTop m k) ↔ SourceCheck m := by
  have zero : (0 : Nat) ≠ k := by omega
  have one : (1 : Nat) ≠ k := by omega
  simp [putTop,SourceCheck,zero,one]

theorem forbidden_known (choice : Bool) (snap : GeneralNominalState.State)
    (cache : CacheSound (after choice) snap) (n : Nat) (high : 2 ≤ n) :
    ¬ GeneralNominalState.Known snap n := by
  intro recognized
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head recognized
  have check := (outside_source (model Common.rowEmpty) high).mpr
    ((exact_source _).mp (raw_model Common.rowEmpty))
  have witnessed := cache_only_source choice snap cache observation
    (GeneralNominalSupport.head_recorded head) _ check
  have tested := GeneralDictionaryGroundCopy218Refresh.head_holds head witnessed
  simp only [putTop,ite_true] at tested
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test tested

end Yulang.GeneralRebaseRowTrustedBoundary287
