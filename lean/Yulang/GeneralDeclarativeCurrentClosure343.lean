import Yulang.GeneralDeclarativeCurrentChild343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17200
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeCurrentClosure343
open GeneralDeclarativeCurrentWorld343 (now grows current_rank stays)
open GeneralDeclarativeCurrentOrigins343 (support)
open GeneralDeclarativePlacement343 (view actual_place)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativeLogicalChild343 (child output)
open GeneralDeclarativeVersionedRootGuard342 (actualDemand)
open GeneralDeclarativeVersionedChildWitness342 (waiting coverage)
open GeneralDeclarativeVersionedRootCompiler342 (declared)
open GeneralDeclarativeVersionedTree342 (CurrentInstance modern_raw_tree)
open GeneralDeclarativeTaggedDictionary340 (Rule dictionary_sound)
open GeneralDeclarativeStoppedPaired341 (Placement)
open GeneralWhereOriginSingleSource318 (sourceRegistry declaration checked)
open GeneralDictionaryJournalRefinement228Source (interpretation root)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralWherePhysicalCommit319 (final newChild)
open GeneralWhereVersionInstall317 (Models)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify Resolves Summarizes Dictionary Tree)

noncomputable abbrev rules := Rule (support grows) [] sourceRegistry interpretation waiting
abbrev tree : Tree := .selected declaration.id [.selected leaf.id []]
abbrev dict : Dictionary := .node declaration.id [.node leaf.id []]

theorem resolves : Resolves rules actualDemand tree :=
  .selected (GeneralDeclarativeCurrentRoot343.rule grows current_rank)
    (.cons (.selected GeneralDeclarativeCurrentChild343.rule .nil) .nil)

theorem summarizes : Summarizes tree (.selected dict) :=
  .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)

theorem selected : Classify rules actualDemand (.selected dict) :=
  ⟨tree,resolves,summarizes⟩

theorem dictionary (n : Assignment) (fit : GeneralDeclarativeHead320.Models now n) :
    GeneralDeclarativeExactDictionary337.Evidence sourceRegistry interpretation n actualDemand dict :=
  dictionary_sound checked coverage declared selected ⟨fit,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩

private theorem lift_args {xs ys : List GeneralDeclarativeWhere319.Capture}
    (placed : CommonRoleOutermostResolver.All₂ (GeneralStoppedPlacement335.SameCapture view) xs ys) :
    CommonRoleOutermostResolver.All₂ (GeneralStoppedPlacement335.SameCapture now) xs ys := by
  induction placed with
  | nil => exact .nil
  | cons visible _ next =>
    exact .cons ⟨GeneralDeclarativeGrowth327.aliases grows visible.lower,
      GeneralDeclarativeGrowth327.aliases grows visible.center,
      GeneralDeclarativeGrowth327.aliases grows visible.upper⟩ next

theorem current_place : Placement final.mixed now newChild.occurrence (child kept) := by
  obtain ⟨site,registered,same,placed⟩ := actual_place
  exact ⟨site,registered,same,placed.role,lift_args placed.arguments,placed.outputs⟩

/-- Actual C319 transaction, actual ordinary compiler and latest
witness-backed root/child tree close in one footprint-preserving
assignment. This scope is the isolated versioned fixture; the original
C316 solver is not being retagged as a successful solver. -/
theorem one_model (m : Assignment) (fit : Models final m) :
    ∃ n, Models final n ∧ (∀ k ∈ journalSources final, n k = m k) ∧
      GeneralDeclarativeHead320.Models now n ∧
      GeneralSourceDictionaries.ErasedEvidence (CurrentInstance n) root dict ∧
      Classify rules actualDemand (.selected dict) ∧
      GeneralDeclarativeExactDictionary337.Evidence sourceRegistry interpretation n actualDemand dict ∧
      Placement final.mixed now newChild.occurrence (child kept) := by
  obtain ⟨n,current,same,raw⟩ := stays m fit
  exact ⟨n,raw,fun k h => same k (List.mem_append_right _ h),current,
    modern_raw_tree n raw,selected,dictionary n current,current_place⟩

end Yulang.GeneralDeclarativeCurrentClosure343
