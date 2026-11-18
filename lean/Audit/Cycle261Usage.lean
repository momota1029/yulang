import Yulang.GeneralRebaseMergeRequests261
namespace Cycle261Usage
open Yulang
example (atoms) (output : GeneralSourceState.Output) : output ∈ GeneralNominalCenteredHeadOutputs.requests (GeneralNominalCenteredHeadAllocMergeState.stage atoms).core GeneralNominalCenteredHeadAllocMergeConflict.focus ↔ output ∈ GeneralRebaseMergeRequests261.outputs := GeneralRebaseMergeRequests261.requests_exact ..
example (atoms) : GeneralRebaseClassCheck261.Ready (GeneralRebaseMergeRequests261.candidate atoms) GeneralRebaseMergeRequests261.outputs := GeneralRebaseMergeRequests261.ready atoms
example (atoms) (assignment : GeneralNominalCommonBridge.Assignment) : GeneralRebaseClassTable261.Effects (GeneralRebaseMergeRequests261.candidate atoms) GeneralRebaseMergeRequests261.outputs assignment ↔ GeneralNominalVersionedEffects231.ClassEffects (GeneralNominalCenteredHeadAllocMergeState.stage atoms).core GeneralNominalCenteredHeadAllocMergeConflict.focus (GeneralRebaseMergeRequests261.candidate atoms) assignment := GeneralRebaseMergeRequests261.effects_exact ..
end Cycle261Usage
