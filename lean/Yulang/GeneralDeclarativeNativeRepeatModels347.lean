import Yulang.GeneralDeclarativeNativeRepeatInput347

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 29000000
namespace Yulang.GeneralDeclarativeNativeRepeatModels347
open GeneralDeclarativeNativeRepeatStage347 (spans fallback phase capture chosen_bound actual_modes)
open GeneralDeclarativeNativeRepeatCompile347 (protect inputs output logicalArg child translated)
open GeneralDeclarativeNativeReplay347 (keep preserves)
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

theorem cap_ranges : ∀ n ∈ declaration.inputNames, Bounds phase (capture n) := by
  intro n present
  change n ∈ ([0,0] : List Nat) at present
  have eq : n = 0 := (List.mem_cons.mp present).elim id List.mem_singleton.mp
  subst n
  exact chosen_bound

theorem for_every_native_model (m : Assignment) (prior : Models after m) :
    ∃ n, Models after n ∧ GeneralDeclarativeHead320.Models output n ∧ ∀ k ∈ keep,n k = m k := by
  obtain ⟨u,typed,held⟩ := GeneralDeclarativeNativeRepeatStage347.common m (starting_model m prior)
  have allocator := whole_input_projection declaration_checked
    (show otherChild ∈ declaration.requirements from List.mem_cons_self)
    translated cap_ranges protect u
  obtain ⟨n,done,agrees⟩ := allocator.mp typed
  have agree : ∀ k ∈ keep, n k = m k := by
    intro k used
    exact (agrees k (List.mem_append_right _ (List.mem_append_right _ used))).trans (held k used)
  have native := (preserves agree).mp prior
  refine ⟨n,native,(model_append n).mpr ⟨done,?_⟩,agree⟩
  intro row present
  cases List.mem_singleton.mp present
  exact output_holds n native

theorem where_values (m : Assignment) (typed : GeneralDeclarativeHead320.Models output m) :
    Equivalent (m logicalArg.lower).1 (variant 0 (m 2).1) ∧
    Equivalent (m logicalArg.center).1 (variant 0 (m 2).1) ∧
    Equivalent (m logicalArg.upper).1 (variant 0 (m 2).1) := by
  have prepared : GeneralDeclarativeHead320.Models inputs m := ((model_append m).mp typed).1
  have state := GeneralDeclarativeGrowth327.restrict (make_grows phase protect capture jobs) m prepared
  have observed := names_observed (s := phase) (protect := protect) (cap := capture)
    GeneralDeclarativeFreshValues343.present
  obtain ⟨loVal,center,hiVal⟩ := actual_modes m state
  have lo := semantic (origin_reads observed.1) m prepared
  have mid := semantic (origin_reads observed.2.1) m prepared
  have hi := semantic (origin_reads observed.2.2) m prepared
  change Equivalent (m logicalArg.lower).1 (variant 0 (m (capture 0).lower).1) at lo
  change Equivalent (m logicalArg.center).1 (variant 0 (m (capture 0).center).1) at mid
  change Equivalent (m logicalArg.upper).1 (variant 0 (m (capture 0).upper).1) at hi
  rw [center] at mid
  exact ⟨eqv_trans lo (variant_congr 0 loVal),mid,eqv_trans hi (variant_congr 0 hiVal)⟩

theorem exact_placement_cut {s : GeneralDeclarativeHead320.State}
    (extension : GeneralDeclarativeGrowth327.Extends output s)
    (m : Assignment) (native : Models after m) (fit : GeneralDeclarativeHead320.Models s m) :
    ¬ GeneralDeclarativeStoppedPaired341.Placement after s GeneralLiveCompoundChildSite316.child child := by
  intro relates
  obtain ⟨low,high⟩ := GeneralDeclarativeNativePlacement347.endpoints_of_placement fit relates
  obtain ⟨readLo,_,readHi⟩ := where_values m (GeneralDeclarativeGrowth327.restrict extension m fit)
  exact GeneralDeclarativeNativeRead347.genuinely_nonpoint m native
    (eqv_trans low (eqv_trans readLo (eqv_symm (eqv_trans high readHi))))

end Yulang.GeneralDeclarativeNativeRepeatModels347
