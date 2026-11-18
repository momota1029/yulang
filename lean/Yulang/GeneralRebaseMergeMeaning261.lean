import Yulang.GeneralRebaseMergeRequests261
namespace Yulang.GeneralRebaseMergeMeaning261
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadAllocMergeSource
open GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadAllocMergeState
open GeneralNominalCenteredHeadAllocMergeConflict (focus)
open GeneralRebaseMergeRequests261 (candidate body outputs)

theorem body_meaning (atoms) (target : Nat) (assignment : Assignment) :
 GeneralNominalVersionedEffects231.BodyHolds (candidate atoms) target assignment body ↔
 Equivalent (assignment target).1 (.base .int) :=
 (GeneralNominalVersionedEffects231.body_holds_iff ..).trans
  (GeneralNominalCenteredHeadMatEffects.body_equation (show
   GeneralNominalCenteredHeadMatEffects.compileBody (candidate atoms) body = some (.primitive (.scalar .int) []) from rfl))

theorem effects_exact (atoms) (assignment : Assignment) :
 GeneralRebaseClassTable261.Effects (candidate atoms) outputs assignment ↔
 Equivalent (assignment aTarget).1 (.base .int) ∧ Equivalent (assignment bTarget).1 (.base .int) := by
 constructor
 · intro valid
   exact ⟨(body_meaning atoms aTarget assignment).mp
     (valid.1 ⟨0,aTarget⟩ List.mem_cons_self body (GeneralRebaseMergeRequests261.lookup_exact atoms)),
    (body_meaning atoms bTarget assignment).mp
     (valid.1 ⟨0,bTarget⟩ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) body
      (GeneralRebaseMergeRequests261.lookup_exact atoms))⟩
 · rintro ⟨one,two⟩
   have every (output : GeneralSourceState.Output) (member : output ∈ outputs) :
     Equivalent (assignment output.target).1 (.base .int) := by
     rcases List.mem_cons.mp member with rfl | member
     · exact one
     · cases List.mem_singleton.mp member
       exact two
   constructor
   · intro output member chosen found
     have name : output.name = 0 := by
       rcases List.mem_cons.mp member with rfl | member
       · rfl
       · cases List.mem_singleton.mp member
         rfl
     rw [name,GeneralRebaseMergeRequests261.lookup_exact atoms] at found
     cases Option.some.inj found
     exact (body_meaning atoms output.target assignment).mpr (every output member)
   · intro first one last two _
     have left := every first one
     have right := every last two
     exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩

theorem history_outputs (atoms) (assignment : Assignment)
 (history : GeneralNominalCenteredHeadAllocMergedConflict.HistoryModels (stage atoms) assignment) :
 Equivalent (assignment aTarget).1 (.base .int) ∧ Equivalent (assignment bTarget).1 (variant 0 (.base .int)) := by
 have emitted := (history.2.2.1 plan (List.mem_singleton_self _)).2.2
 unfold GeneralNominalCenteredHeadMatStepPackets.Outputs at emitted
 rw [GeneralNominalCenteredHeadAllocMergeInstall.schema_exact] at emitted
 exact ⟨emitted _ List.mem_cons_self,emitted _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

theorem history_equal_impossible (atoms) (assignment : Assignment)
 (history : GeneralNominalCenteredHeadAllocMergedConflict.HistoryModels (stage atoms) assignment)
 (equal : Equivalent (assignment aTarget).1 (assignment bTarget).1) : False := by
 obtain ⟨one,two⟩ := history_outputs atoms assignment history
 exact GeneralNominalCenteredHeadMatCompletionCollisionPackets.int_not_variant
  ⟨subtype_trans one.2 (subtype_trans equal.1 two.1),subtype_trans two.2 (subtype_trans equal.2 one.1)⟩

theorem history_effects_impossible (atoms) : ¬ ∃ assignment,
 GeneralNominalCenteredHeadAllocMergedConflict.HistoryModels (stage atoms) assignment ∧
 GeneralRebaseClassTable261.Effects (candidate atoms) outputs assignment := by
 rintro ⟨assignment,history,effects⟩
 exact history_equal_impossible atoms assignment history
  (effects.2 ⟨0,aTarget⟩ List.mem_cons_self ⟨0,bTarget⟩ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) rfl)

theorem uniform_effects (atoms) : GeneralRebaseClassTable261.Effects (candidate atoms) outputs uniform :=
 (effects_exact atoms uniform).mpr ⟨⟨subtype_refl _,subtype_refl _⟩,⟨subtype_refl _,subtype_refl _⟩⟩
end Yulang.GeneralRebaseMergeMeaning261
