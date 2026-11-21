import Yulang.GeneralDeclarativePlainCapture323
import Yulang.GeneralDeclarativeClauseOrigins325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeGroupedProducer325
open GeneralDeclarativeHead320 (State environment)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeWhere319 (variables)
open GeneralDeclarativeClauseOrigins325 (Origin origin_reads)
open GeneralDeclarativeEqualities322 (entails)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativePlainCapture323 (whole)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeExactWalk323 (variant_exact)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralDeclarationPatterns (normalize)
open GeneralCandidateInspection (plainNames)

/-- The actual source rule captures the entire payload at every plain
variable in the normalized group, through ordinary alias origins.
This neither divides the payload nor tests whether a hypothetical
partition would have reconstituted its join. -/
theorem merged_tag {s : State}
    (normal : normalize p = .variant tag payload)
    (visible : plainNames payload = some binders)
    (compiled : translate c i payload = some code)
    (origin : Origin s arg.center (.variant tag (.variable payloadName)))
    (captures : ∀ n ∈ binders, Alias s (cap n).center payloadName) :
    Result s (fact c i cap arg p) := by
  have got : translate c i (normalize p) = some (.variant tag code) := by
    simp [normal,translate,compiled]
  refine ⟨[⟨arg.center,logical cap .actual (.variant tag code)⟩],by simp [fact,got],?_⟩
  intro row chosen m valid
  cases List.mem_singleton.mp chosen
  simp only [Holds,logical_value]
  have wholePayload := whole (m := m) (cap := cap) (entire := (m payloadName).1) visible compiled
    (fun name used => alias_sound (captures name used) m valid)
  have exactTag := (variant_exact tag _ _).mpr (eqv_symm wholePayload)
  exact eqv_trans (entails (origin_reads origin) m valid) exactTag

end Yulang.GeneralDeclarativeGroupedProducer325
