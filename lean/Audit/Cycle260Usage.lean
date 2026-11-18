import Yulang.GeneralRebaseEqualOutputs260
import Yulang.GeneralRebaseNamedRequest260
import Yulang.GeneralRebaseRequestBodyKeys260
import Yulang.GeneralRebaseBodyActual260
import Yulang.GeneralDefaultRebasePublic260
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
example (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralDefaultRebaseModels260.Models GeneralDefaultRebaseSource260.finalState assignment ↔
 GeneralNominalVersionedJournal232.Models GeneralDictionaryVersionedGap206Install233.installed assignment :=
 GeneralDefaultRebaseInstalled260.same_assignment assignment
example : GeneralDefaultRebaseRun260.run GeneralDefaultRebaseSource260.initialState =
 .ok (some GeneralDefaultRebaseSource260.finalState) := GeneralDefaultRebaseRun260.first
example (boundary : GeneralNominalCommonBridge.Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryDefaultGap206Source.snapshot boundary) :
 GeneralDefaultRebasePublic260.Certificate boundary := GeneralDefaultRebasePublic260.certificate boundary source
example : GeneralRebaseBodyActual260.explicitProposal = some GeneralOutputRebaseSource260.facts := GeneralRebaseBodyActual260.explicit_exact
example : GeneralReflexiveDefaultRun260.run GeneralReflexiveDefaultSource260.initialState = .ok (some GeneralReflexiveDefaultSource260.finalState) := GeneralReflexiveDefaultRun260.first
example (assignment : GeneralNominalCommonBridge.Assignment) : GeneralReflexiveDefaultModels260.Models GeneralReflexiveDefaultSource260.initialState assignment ↔ GeneralReflexiveDefaultModels260.Models GeneralReflexiveDefaultSource260.finalState assignment := GeneralReflexiveDefaultModels260.same_assignment ..
example : GeneralRebaseRequestBodyKeys260.compile GeneralDictionaryDefaultGap206Source.plan 37 2 0 ⟨0,0⟩ ≠ GeneralRebaseRequestBodyKeys260.compile GeneralDictionaryDefaultGap206Source.plan 37 2 1 ⟨0,1⟩ := GeneralRebaseRequestBodyKeys260.probe_repaired
example : GeneralRebaseNamedRequest260.compile GeneralDictionaryDefaultGap206Source.plan 37 2 ⟨0,0⟩ ≠ GeneralRebaseNamedRequest260.compile GeneralDictionaryDefaultGap206Source.plan 37 2 ⟨0,1⟩ := GeneralRebaseNamedRequest260.probe_repaired
example (outputs : List GeneralSourceState.Output) (assignment : GeneralNominalCommonBridge.Assignment) : (GeneralRebaseEqualOutputs260.schema outputs).Holds (GeneralRebaseEqualOutputs260.variables assignment) assignment ↔ ∀ first ∈ outputs, ∀ last ∈ outputs, first.name = last.name → CommonNominalFullCarrier.Equivalent (assignment first.target).1 (assignment last.target).1 := GeneralRebaseEqualOutputs260.holds_exact ..
end Cycle260Usage
