import Yulang.GeneralDeclarativeReplayCompile348

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 29000000
namespace Yulang.GeneralDeclarativeReplayModels348
open GeneralDeclarativeReplayStage348 (phase capture chosen_bound actual_modes)
open GeneralDeclarativeNativeRepeatStage347 (spans fallback)
open GeneralDeclarativeReplayCompile348 (protect inputs output logicalArg child translated)
open GeneralDeclarativeLogicalChild343 (value jobs)
open GeneralDeclarativeNativeRoot347 (starting_model output_holds)
open GeneralDeclarativeFreshInputs325 (whole_input_projection names_observed)
open GeneralDeclarativeClauseOrigins325 (origin_reads)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeClauseBatch327 (make_grows)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralLiveCompoundRegistry316 (declaration declaration_checked otherChild)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent variant)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm variant_congr)

theorem cap_ranges (keep : List Nat) : ∀ n ∈ declaration.inputNames, Bounds (phase keep) (capture keep n) := by
  intro n present
  change n ∈ ([0,0] : List Nat) at present
  have eq : n = 0 := (List.mem_cons.mp present).elim id List.mem_singleton.mp
  subst n
  exact chosen_bound keep

theorem model_extension (keep : List Nat) (preservedTarget : 4 ∈ keep) (m : Assignment)
    (source : GeneralDeclarativeHead320.Models GeneralDeclarativeVersionedRootGuard342.observedRoot m)
    (body : GeneralDeclarativeEntailment320.Holds m ownerOutput) :
    ∃ n, GeneralDeclarativeHead320.Models (output keep) n ∧ ∀ k ∈ keep,n k = m k := by
  obtain ⟨u,typed,held⟩ := GeneralDeclarativeReplayStage348.common keep m source
  have allocator := whole_input_projection declaration_checked
    (show otherChild ∈ declaration.requirements from List.mem_cons_self)
    translated (cap_ranges keep) (protect keep) u
  obtain ⟨n,done,agrees⟩ := allocator.mp typed
  have agree : ∀ k ∈ keep, n k = m k := by
    intro k used
    exact (agrees k (List.mem_append_right _ (List.mem_append_right _ used))).trans (held k used)
  refine ⟨n,(model_append n).mpr ⟨done,?_⟩,agree⟩
  intro row present
  cases List.mem_singleton.mp present
  change Equivalent (n 4).1 GeneralDictionaryOptionalOutput229.value
  rw [agree 4 preservedTarget]
  exact body

theorem where_values (keep : List Nat) (m : Assignment) (typed : GeneralDeclarativeHead320.Models (output keep) m) :
    Equivalent (m (logicalArg keep).lower).1 (variant 0 (m 2).1) ∧
    Equivalent (m (logicalArg keep).center).1 (variant 0 (m 2).1) ∧
    Equivalent (m (logicalArg keep).upper).1 (variant 0 (m 2).1) := by
  have prepared : GeneralDeclarativeHead320.Models (inputs keep) m := ((model_append m).mp typed).1
  have state := GeneralDeclarativeGrowth327.restrict (make_grows (phase keep) (protect keep) (capture keep) jobs) m prepared
  have observed := names_observed (s := phase keep) (protect := protect keep) (cap := capture keep)
    GeneralDeclarativeFreshValues343.present
  obtain ⟨loVal,center,hiVal⟩ := actual_modes keep m state
  have lo := semantic (origin_reads observed.1) m prepared
  have mid := semantic (origin_reads observed.2.1) m prepared
  have hi := semantic (origin_reads observed.2.2) m prepared
  change Equivalent (m (logicalArg keep).lower).1 (variant 0 (m (capture keep 0).lower).1) at lo
  change Equivalent (m (logicalArg keep).center).1 (variant 0 (m (capture keep 0).center).1) at mid
  change Equivalent (m (logicalArg keep).upper).1 (variant 0 (m (capture keep 0).upper).1) at hi
  rw [center] at mid
  exact ⟨eqv_trans lo (variant_congr 0 loVal),mid,eqv_trans hi (variant_congr 0 hiVal)⟩

end Yulang.GeneralDeclarativeReplayModels348
