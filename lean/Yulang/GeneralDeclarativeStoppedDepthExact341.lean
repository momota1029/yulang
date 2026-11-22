import Yulang.GeneralDeclarativeStoppedDepthProjection341
import Yulang.GeneralDeclarativeStoppedFreshCut341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDeclarativeStoppedDepthExact341
open GeneralDictionaryOutputDepth252 (snapshot)
open GeneralRebaseDepthScalar285 (target refreshed)
open GeneralRebaseDepthTerminalFrame285 (raw_source)
open GeneralRebaseDepthGroundModels285 (source_inputs close_ground)
open GeneralRebaseDepthHaltEvidence285 (final_models)
open GeneralDeclarativeStoppedDepthView341 (final before exact_before outRow current_model)
open GeneralDeclarativeStoppedDepthWitness341 (compiled expanded_grows)
open GeneralDeclarativeStoppedDepthProjection341 (extend source_same preserve_raw extends_ordinary)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeStoppedLower339 (exact_models)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralNominalVersionedJournalFrame236 (sources models_iff)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_trans)

/-- No name extension is needed for the exact source projection with its
genuine output row. This converse recovers the *entire* C285 journal
model, not just the current raw interval state. -/
theorem base_exact (m : Assignment) :
    Models final m ↔ GeneralNominalVersionedJournal232.Models refreshed m := by
  refine ⟨?_,current_model m⟩
  intro known
  obtain ⟨view,out⟩ := (model_append m).mp known
  have raw := (exact_models target.state m exact_before).mp view
  have input := (source_inputs m).mp ((raw_source m).mp raw)
  have wrote := out outRow List.mem_cons_self
  change Equivalent (m 3).1 (GeneralRebaseDepthReads285.valueFromInput m) at wrote
  have read := close_ground m input.2.2
  exact (final_models m).mpr ⟨input,subtype_trans wrote.1 read.1,subtype_trans read.2 wrote.2⟩

/-- The actual compiler may add fresh bounds. Those extra names have a
conservative extension, with all raw semantic support fixed exactly. -/
theorem compiled_exact (m : Assignment) :
    GeneralNominalVersionedJournal232.Models refreshed m ↔
      ∃ n, Models compiled n ∧ ∀ id ∈ sources refreshed, n id = m id := by
  refine ⟨fun fit => ⟨extend m,extends_ordinary fit,source_same m⟩,?_⟩
  rintro ⟨n,compiledFit,same⟩
  have raw := (base_exact n).mp (GeneralDeclarativeGrowth327.restrict expanded_grows n compiledFit)
  exact (models_iff refreshed same).mp raw

end Yulang.GeneralDeclarativeStoppedDepthExact341
