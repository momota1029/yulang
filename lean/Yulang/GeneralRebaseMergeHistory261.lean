import Yulang.GeneralRebaseMergePacket261
namespace Yulang.GeneralRebaseMergeHistory261
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadAllocMergeSource
open GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadAllocMergeState
open GeneralNominalCenters

/-- Fixed initial source and two literal parent output constraints; no replay
of an evolving journal is hidden in this predicate. -/
def Base (assignment : Assignment) : Prop :=
 GeneralNominalState.Models snapshot assignment ∧
 CommonNominalFullCarrier.Equivalent (assignment aTarget).1 (.base .int) ∧
 CommonNominalFullCarrier.Equivalent (assignment bTarget).1 (CommonNominalFullCarrier.variant 0 (.base .int))

theorem history_exact (atoms) (assignment : Assignment) :
 GeneralNominalCenteredHeadAllocMergedConflict.HistoryModels (stage atoms) assignment ↔ Base assignment := by
 constructor
 · intro history
   exact ⟨history.1,GeneralRebaseMergeMeaning261.history_outputs atoms assignment history⟩
 · rintro ⟨source,one,two⟩
   refine ⟨source,?_,?_,?_⟩
   · intro site member
     cases List.mem_singleton.mp member
     exact point_root_holds snapshot.seed root (fun _ => rfl) assignment
   · intro candidate member
     cases List.mem_singleton.mp member
     refine ⟨source,inputs source,?_⟩
     unfold GeneralNominalCenteredHeadMatStepPackets.Outputs
     change (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds
       (GeneralNominalCenteredHeadMatEffects.variables plan assignment) assignment
     rw [schema_exact]
     intro equation member
     rcases List.mem_cons.mp member with rfl | member
     · exact one
     · cases List.mem_singleton.mp member
       exact two
   · intro effect member
     cases List.mem_singleton.mp member
     exact ⟨head_equations source,effects assignment⟩

abbrev Models (atoms) := GeneralRebaseClassTable261.Models Base
 (GeneralRebaseMergeRequests261.candidate atoms) 38 GeneralRebaseMergeRequests261.outputs

theorem models_exact (atoms) (state : GeneralRebaseStep258.State (GeneralRebaseMergeRun261.facts atoms)) (assignment : Assignment) :
 GeneralRebaseMergeRun261.Models atoms state assignment ↔ Models atoms state assignment :=
 and_congr (history_exact atoms assignment) Iff.rfl

theorem initial_inhabited (atoms) : Models atoms (GeneralRebaseMergeRun261.initialState atoms) witness :=
 (models_exact atoms _ witness).mp (GeneralRebaseMergeRun261.initial_inhabited atoms)

theorem final_uninhabited (atoms) : ¬ ∃ assignment, Models atoms (GeneralRebaseMergeRun261.finalState atoms) assignment := by
 rintro ⟨assignment,valid⟩
 exact GeneralRebaseMergeRun261.final_uninhabited atoms ⟨assignment,(models_exact atoms _ assignment).mpr valid⟩

/-- A raw-only candidate evidence can exist at uniform, but that assignment
violates the fixed historical output constraints. -/
theorem uniform_not_base : ¬ Base uniform := by
 rintro ⟨_,_,two⟩
 exact GeneralNominalCenteredHeadMatCompletionCollisionPackets.int_not_variant two
end Yulang.GeneralRebaseMergeHistory261
