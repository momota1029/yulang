import Yulang.GeneralDeclarativeNativeRepeatModels347
import Yulang.GeneralLiveCompoundFullResult316
import Yulang.GeneralDeclarativeStoredRecordBody347
import Yulang.GeneralDeclarativeRepairedEvidence347

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 31000000
namespace Yulang.GeneralDeclarativeNativeCut347
open GeneralLiveCompoundLeafInstall316 (after after_model)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundRegistry316 (sourceRegistry declaration registry)
open GeneralDictionaryJournalRefinement228Source (root roles interpretation)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundChildSite316 (child)
open GeneralDeclarativeCurrentBarrier345 (view)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDeclarativeNativeReplay347 (keep)
open GeneralDeclarativeNativeRepeatStage347 (spans fallback)
open GeneralDeclarativeNativeRepeatCompile347 (output)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot)
open GeneralDeclarativeRootReplay344 (actualDemand)
open GeneralDeclarativeLogicalChild343 (targets)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeStoppedPaired341 (Placement)
open GeneralNominalCommonBridge (Assignment)

noncomputable abbrev logical := GeneralDeclarativeNativeRepeatCompile347.child
abbrev dict := GeneralLiveCompoundFullResult316.dictionary

/-- On a real native reachable halt with a selected dictionary in
the native relation, the independently grounded current compiler
for the same literal declaration and demand builds one different
child interval. In one model of both states, no mode-by-mode sound
placement of that ordered child at the real old site exists. This
does not assert that a chosen executable scheduler returns this
state or prove any global termination / equivalence theorem. -/
theorem verified :
    (∀ next, ¬ Step registry root after next) ∧
    B4TargetV8.Classify (boundary roles) sourceRegistry after root (.selected dict) ∧
    compileBody sourceRegistry interpretation (actualDemand rootPlan view)
      declaration observedRoot spans keep fallback targets = some (output,[logical]) ∧
    ∃ n : Assignment, Models after n ∧ GeneralDeclarativeHead320.Models output n ∧
      (∀ k ∈ keep,n k = w k) ∧ ¬ Placement after output child logical := by
  obtain ⟨n,native,ordinary,agrees⟩ := GeneralDeclarativeNativeRepeatModels347.for_every_native_model w after_model
  exact ⟨GeneralLiveCompoundStable316.halted,GeneralLiveCompoundFullResult316.classified,
    GeneralDeclarativeNativeRepeatCompile347.actual,n,native,ordinary,agrees,
    GeneralDeclarativeNativeRepeatModels347.exact_placement_cut
      (GeneralDeclarativeClauseBatch327.reflexive _) n native ordinary⟩

end Yulang.GeneralDeclarativeNativeCut347
