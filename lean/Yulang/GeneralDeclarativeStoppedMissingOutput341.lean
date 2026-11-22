import Yulang.GeneralDeclarativeStoppedDepthExact341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33500
set_option maxHeartbeats 15300000
namespace Yulang.GeneralDeclarativeStoppedMissingOutput341
open GeneralDictionaryOutputDepth252 (S F P)
open GeneralDictionaryOutputDepthInstall252 (smallModel small_source)
open GeneralRebaseDepthScalar285 (refreshed target)
open GeneralRebaseDepthGroundModels285 (FinalTypeCheck)
open GeneralRebaseDepthHaltEvidence285 (final_models)
open GeneralRebaseDepthTerminalFrame285 (raw_source)
open GeneralDeclarativeStoppedDepthView341 (before final exact_before outRow)
open GeneralDeclarativeStoppedDepthExact341 (base_exact)
open GeneralDeclarativeStoppedLower339 (exact_models)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEntailment320 (Holds model_append)
open CommonNominalFullCarrier (Equivalent nominal)

/-- A genuine countermodel to omitting the fixed output row from the
normal current presentation. Every input/context obligation holds
on this assignment; the full stopped journal does not. -/
theorem before_only :
    Models before smallModel ∧
    ¬ GeneralNominalVersionedJournal232.Models refreshed smallModel := by
  refine ⟨(exact_models target.state smallModel exact_before).mpr ((raw_source smallModel).mpr small_source),?_⟩
  intro fits
  have mismatch := ((final_models smallModel).mp fits).2
  change Equivalent S P at mismatch
  have tag := GeneralDictionaryInspectionHeads215.tag_subtype
    (GeneralDictionaryInspectionHeads215.tagged_scalar .int)
    (GeneralDictionaryInspectionHeads215.tagged_nominal 0 [.inl (nominal 0 [.inl F])]) mismatch.1
  cases tag

theorem cannot_omit :
    Models before smallModel ∧ ¬ Holds smallModel outRow := by
  refine ⟨before_only.1,?_⟩
  intro assume
  have withOutput : Models final smallModel := (model_append smallModel).mpr
    ⟨before_only.1,fun row found => List.mem_singleton.mp found ▸ ?_⟩
  · exact before_only.2 ((base_exact _).mp withOutput)
  · exact assume

end Yulang.GeneralDeclarativeStoppedMissingOutput341
