import Yulang.GeneralRebaseStableMerge261
namespace Cycle261Usage
open Yulang
example (atoms) (output : GeneralSourceState.Output) : output ∈ GeneralNominalCenteredHeadOutputs.requests (GeneralNominalCenteredHeadAllocMergeState.stage atoms).core GeneralNominalCenteredHeadAllocMergeConflict.focus ↔ output ∈ GeneralRebaseMergeRequests261.outputs := GeneralRebaseMergeRequests261.requests_exact ..
example (atoms) : GeneralRebaseClassCheck261.Ready (GeneralRebaseMergeRequests261.candidate atoms) GeneralRebaseMergeRequests261.outputs := GeneralRebaseMergeRequests261.ready atoms
example (atoms) (assignment : GeneralNominalCommonBridge.Assignment) : GeneralRebaseClassTable261.Effects (GeneralRebaseMergeRequests261.candidate atoms) GeneralRebaseMergeRequests261.outputs assignment ↔ GeneralNominalVersionedEffects231.ClassEffects (GeneralNominalCenteredHeadAllocMergeState.stage atoms).core GeneralNominalCenteredHeadAllocMergeConflict.focus (GeneralRebaseMergeRequests261.candidate atoms) assignment := GeneralRebaseMergeRequests261.effects_exact ..
example (atoms) : ¬ ∃ assignment, GeneralRebaseMergeRun261.Models atoms (GeneralRebaseMergeRun261.finalState atoms) assignment := GeneralRebaseMergeRun261.final_uninhabited atoms
example (atoms) (assignment : GeneralNominalCommonBridge.Assignment) : GeneralNominalCenteredHeadAllocMergedConflict.HistoryModels (GeneralNominalCenteredHeadAllocMergeState.stage atoms) assignment ↔ GeneralRebaseMergeHistory261.Base assignment := GeneralRebaseMergeHistory261.history_exact ..
example (owner : Nat) (first last : GeneralSourceState.Output) (assignment : GeneralNominalCommonBridge.Assignment) : GeneralRebasePairKeys261.Holds owner assignment (GeneralRebasePairKeys261.key owner first last) ↔ CommonNominalFullCarrier.Equivalent (assignment first.target).1 (assignment last.target).1 := GeneralRebasePairKeys261.at_key ..
example (atoms) : ¬ ∃ assignment, GeneralRebaseStableMerge261.Models atoms (GeneralRebaseStableMerge261.finalState atoms) assignment := GeneralRebaseStableMerge261.final_uninhabited atoms
end Cycle261Usage
