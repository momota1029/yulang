import Yulang.GeneralRebaseStableMerge261
namespace Yulang.GeneralRebaseMergeObservation261
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadAllocMergeState
open GeneralNominalCenteredHeadAllocMergeConflict (focus)
open GeneralRebaseMergeRequests261 (candidate outputs)
open GeneralRebaseStep258

theorem effects_reordered (plan : GeneralNominalCenters.Plan roles) (first last : List GeneralSourceState.Output)
 (same : ∀ output, output ∈ first ↔ output ∈ last) (assignment : Assignment) :
 GeneralRebaseClassTable261.Effects plan first assignment ↔ GeneralRebaseClassTable261.Effects plan last assignment := by
 constructor
 · rintro ⟨bodies,pairs⟩
   exact ⟨fun o h => bodies o ((same o).mpr h),
    fun a ha b hb => pairs a ((same a).mpr ha) b ((same b).mpr hb)⟩
 · rintro ⟨bodies,pairs⟩
   exact ⟨fun o h => bodies o ((same o).mp h),
    fun a ha b hb => pairs a ((same a).mp ha) b ((same b).mp hb)⟩

/-- The actual leaf bodies are Int in every atoms-stage of this concrete
family. This justifies using its fixed-plan table across those observations;
it is not an invariance theorem for arbitrary changing plans. -/
theorem changing_plan (fixed observed) (assignment : Assignment) :
 GeneralRebaseClassTable261.Effects (candidate fixed)
 (GeneralNominalCenteredHeadOutputs.requests (stage observed).core focus) assignment ↔
 GeneralNominalVersionedEffects231.ClassEffects (stage observed).core focus (candidate observed) assignment := by
 rw [effects_reordered (candidate fixed) _ outputs (GeneralRebaseMergeRequests261.requests_exact observed)]
 rw [GeneralRebaseMergeMeaning261.effects_exact]
 exact (GeneralRebaseMergeMeaning261.effects_exact observed assignment).symm.trans
   (GeneralRebaseMergeRequests261.effects_exact observed assignment)

theorem actual_write (base : Assignment → Prop) (fixed observed)
 (state : State (GeneralRebaseStableMerge261.facts fixed)) (assignment : Assignment) :
 GeneralRebaseStableClass261.Models base (candidate fixed) 38
 (write state (GeneralRebaseStableClass261.facts (candidate fixed) 38
 (GeneralNominalCenteredHeadOutputs.requests (stage observed).core focus))) assignment ↔
 GeneralRebaseStableClass261.Models base (candidate fixed) 38 state assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (stage observed).core focus (candidate observed) assignment :=
 (GeneralRebaseStableClass261.write_exact base (candidate fixed) 38 outputs _
 (GeneralRebaseStableMerge261.requests_covered observed) state assignment).trans
 (and_congr Iff.rfl (changing_plan fixed observed assignment))

/-- Coverage alone does not manufacture Frame or current raw models; those
are the explicit conditions for the real packet/leaf evidence bridge. -/
theorem packet_evidence (fixed observed)
 (good : Good observed) (supported : GeneralNominalCenteredHeadAllocMergeStable.Supported observed)
 (assignment : Assignment)
 (raw : GeneralNominalState.Models (GeneralNominalCenteredHeadAllocMergeConflict.current observed).state assignment)
 (effects : GeneralRebaseClassTable261.Effects (candidate fixed)
 (GeneralNominalCenteredHeadOutputs.requests (stage observed).core focus) assignment) :
 GeneralNominalVersionedPlans231.Holds (candidate observed) assignment ∧
 GeneralNominalVersionedEvidence231.Evidence GeneralNominalCenteredHeadAllocMergeSource.registry
 (stage observed).core assignment focus (.node 38 []) := by
 have actual := (GeneralRebaseMergeRequests261.effects_exact observed assignment).mpr
   ((changing_plan fixed observed assignment).mp effects)
 exact ⟨GeneralRebaseMergePacket261.packet_holds observed assignment raw actual,
   GeneralRebaseMergePacket261.evidence observed good supported assignment raw actual⟩
end Yulang.GeneralRebaseMergeObservation261
