import Yulang.GeneralDeclarativeRepeatedChild348

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 39000
set_option maxHeartbeats 65000000
namespace Yulang.GeneralDeclarativeRepeatedDictionary348
open GeneralDeclarativeRepeatedWorld348 (now grows current_rank stays)
open GeneralDeclarativeRepeatedOrigins348 (support)
open GeneralDeclarativeRepeatedPlacement348 (placedView actual_placement keep requested)
open GeneralDeclarativeVersionedRootGuard342 (actualDemand original_targets)
open GeneralDeclarativeVersionedChildWitness342 (waiting)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeRepeatedClosure348 (Instance physical_tree)
open GeneralDeclarativeTaggedDictionary340 (Rule dictionary_sound)
open GeneralDeclarativeStoppedPaired341 (Placement)
open GeneralLiveCompoundRegistry316 (sourceRegistry declaration checked coverage)
open GeneralDictionaryJournalRefinement228Source (interpretation root)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralWhereVersionInstall317 (fixed)
open GeneralWhereVersionCase317 (occ)
open GeneralWhereVersionInstall317 (Models)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify Resolves Summarizes Dictionary Tree)

noncomputable abbrev rules := Rule (support grows) [] sourceRegistry interpretation waiting
abbrev tree : Tree := .selected declaration.id [.selected leaf.id []]
abbrev dict : Dictionary := .node declaration.id [.node leaf.id []]

theorem resolves : Resolves rules actualDemand tree :=
  .selected (GeneralDeclarativeRepeatedRoot348.rule grows current_rank)
    (.cons (.selected GeneralDeclarativeRepeatedChild348.rule .nil) .nil)

theorem summarizes : Summarizes tree (.selected dict) :=
  .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)

theorem selected : Classify rules actualDemand (.selected dict) :=
  ⟨tree,resolves,summarizes⟩

theorem declared : Declared sourceRegistry actualDemand := by
  intro out h
  rw [original_targets] at h
  cases List.mem_singleton.mp h
  exact ⟨_,rfl⟩

theorem dictionary (n : Assignment) (fit : GeneralDeclarativeHead320.Models now n) :
    GeneralDeclarativeExactDictionary337.Evidence sourceRegistry interpretation n actualDemand dict :=
  dictionary_sound checked coverage declared selected ⟨fit,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩

private theorem lift_args {xs ys : List GeneralDeclarativeWhere319.Capture}
    (placed : CommonRoleOutermostResolver.All₂ (GeneralStoppedPlacement335.SameCapture placedView) xs ys) :
    CommonRoleOutermostResolver.All₂ (GeneralStoppedPlacement335.SameCapture now) xs ys := by
  induction placed with
  | nil => exact .nil
  | cons visible _ next =>
    exact .cons ⟨GeneralDeclarativeGrowth327.aliases grows visible.lower,
      GeneralDeclarativeGrowth327.aliases grows visible.center,
      GeneralDeclarativeGrowth327.aliases grows visible.upper⟩ next

theorem current_place (m : Assignment) (fit : Models fixed m) : Placement fixed.mixed now occ requested := by
  obtain ⟨site,registered,same,placed⟩ := actual_placement m fit
  exact ⟨site,registered,same,placed.role,lift_args placed.arguments,placed.outputs⟩

/-- Actual isolated C317 transaction on the literal C316 repeated declaration,
actual ordinary compiler and latest
witness-backed root/child tree close in one footprint-preserving
assignment. This scope is the isolated versioned fixture; the original
C316 solver is not being retagged as a successful solver. -/
theorem one_model (m : Assignment) (fit : Models fixed m) :
    ∃ n, Models fixed n ∧ (∀ k ∈ journalSources fixed, n k = m k) ∧
      GeneralDeclarativeHead320.Models now n ∧
      GeneralSourceDictionaries.ErasedEvidence (Instance n) root dict ∧
      Classify rules actualDemand (.selected dict) ∧
      GeneralDeclarativeExactDictionary337.Evidence sourceRegistry interpretation n actualDemand dict ∧
      Placement fixed.mixed now occ requested := by
  obtain ⟨n,current,same,raw⟩ := stays m fit
  exact ⟨n,raw,fun k h => same k (List.mem_append_right _ h),current,
    physical_tree n raw,selected,dictionary n current,current_place n raw⟩

end Yulang.GeneralDeclarativeRepeatedDictionary348
