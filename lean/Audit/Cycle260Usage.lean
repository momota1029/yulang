import Yulang.GeneralOutputRebasePublic260
namespace Cycle260Usage
open Yulang
example (offset : Nat) (schema : GeneralNominalCenteredHeadMatSchemas.Schema) (variables)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 (∀ fact ∈ GeneralRebaseOutputKeys260.keys offset schema,
 GeneralRebaseOutputKeys260.Holds offset schema variables assignment fact) ↔ schema.Holds variables assignment :=
 GeneralRebaseOutputKeys260.all_exact ..
example : GeneralOutputRebaseSource260.proposal = .ok GeneralOutputRebaseSource260.facts :=
 GeneralOutputRebaseSource260.proposal_exact
example (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralOutputRebaseModels260.Models GeneralOutputRebaseSource260.finalState assignment ↔
 GeneralNominalVersionedPlans231.Holds GeneralDictionaryOutputDepth252.plan assignment :=
 GeneralOutputRebaseModels260.final_packet ..
example (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralOutputRebaseModels260.Models GeneralOutputRebaseSource260.finalState assignment ↔
 GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepthInstall252.installed assignment :=
 GeneralOutputRebaseInstalled260.same_assignment ..
example : GeneralOutputRebaseRun260.run GeneralOutputRebaseSource260.initialState =
 .ok (some GeneralOutputRebaseSource260.finalState) := GeneralOutputRebaseRun260.first
example : GeneralOutputRebaseRun260.run GeneralOutputRebaseSource260.finalState = .ok none :=
 GeneralOutputRebaseRun260.stop
example : GeneralRebaseSettle259.settle GeneralOutputRebaseSource260.observe GeneralOutputRebaseSource260.initialState =
 .ok GeneralOutputRebaseSource260.finalState := GeneralOutputRebaseRun260.settle_initial
example (boundary : GeneralNominalCommonBridge.Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryOutputDepth252.snapshot boundary) :
 GeneralOutputRebasePublic260.Certificate boundary := GeneralOutputRebasePublic260.certificate boundary source
example (output : CommonNominalFullCarrier.Ty) :
 GeneralOutputRebaseModels260.Models GeneralOutputRebaseSource260.finalState (GeneralDictionaryPendingOutput258.replace output) ↔
 CommonNominalFullCarrier.Equivalent output GeneralDictionaryOutputDepth252.P :=
 GeneralOutputRebasePublic260.requested_output_exact output
end Cycle260Usage
