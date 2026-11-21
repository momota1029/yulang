import Yulang.GeneralDeclarativeForwardHead325
import Yulang.GeneralDeclarativeRecordProducer325
import Yulang.GeneralDeclarativeGroupedProducer325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHeadFrame325
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeTraceTransfer325 (ordinary)
open GeneralDeclarativeTraceExpand323 (convert expands)
open GeneralDeclarativeTermWalk322 (Binds Walk)
open GeneralDeclarativeClauseOrigins325 (Origin)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeForwardHead325 (by_walk)
open GeneralDeclarativeNominalTrace323 (lower_nominal_sits invariant_use_tag)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordWalk323 (substFields)
open GeneralDeclarativeRecordProducer325 (FieldDerives normalized_tail)
open GeneralDeclarativeGroupedProducer325 (merged_tag)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value values)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralCandidateInspection (plainNames)
open CommonRoleCanonicalRows (Row selected residual)
open CommonRoleOutermostResolver (All₂)

/-- Positive structural source derivations used in this slice. The
constructors retain real ordinary data from source observation rather
than a flag from the checker or the desired compiler/evidence result. -/
inductive FromSource (s : State) (c : Constructors) (i : Interpretation)
    {complete : Nat → Prop} (support : Supported s complete)
    (cap : Nat → Capture) (arg : Capture) (pat : Pattern) : Prop where
  | actual : translate c i (normalize pat) = some code →
      Trace (restriction support) .actual arg.center code raw →
      Binds s cap (raw.map convert) → FromSource s c i support cap arg pat
  | nominal : translate c i (normalize pat) = some (.nominal k forms) →
      Trace (restriction support) .lower arg.lower (.nominal k forms) raw →
      Derives s (.variable arg.upper) (.nominal j upperForms) →
      Binds s cap (raw.map convert) → FromSource s c i support cap arg pat
  | record : (actual.map Prod.fst).Nodup →
      translate c i (normalize pat) = some (withTail written (.variable binder)) →
      Origin s arg.center (withTail actual terminal) →
      Origin s (cap binder).center (withTail (residual (written.map Prod.fst) actual) terminal) →
      (selected (written.map Prod.fst) actual).Perm inSourceOrder →
      All₂ (FieldDerives s) inSourceOrder (substFields cap .actual written) →
      FromSource s c i support cap arg pat
  | grouped : normalize pat = .variant tag payload →
      plainNames payload = some binders → translate c i payload = some code →
      Origin s arg.center (.variant tag (.variable payloadName)) →
      (∀ n ∈ binders, Alias s (cap n).center payloadName) →
      FromSource s c i support cap arg pat

theorem each {s : State} {support : Supported s complete}
    (bounds : Bounds s arg) (real : FromSource s c i support cap arg pat) :
    Result s (fact c i cap arg pat) := by
  cases real with
  | actual written row binds =>
    obtain ⟨exp,linked,walk⟩ := expands (ordinary support row)
    exact by_walk written (entails linked) walk binds
  | nominal written lower upper binds =>
    let tr := ordinary support lower
    obtain ⟨head,read⟩ := lower_nominal_sits tr
    obtain ⟨term,opened,walk⟩ := expands (invariant_use_tag tr)
    refine by_walk written ?_ walk binds
    intro m valid
    have lo := entails read m valid
    have hi := entails upper m valid
    have group := GeneralDeclarativeDemand320.bounds_sound bounds m valid
    have linked := (GeneralNominalIntervalLaws.nominal_sandwich _ _
      ((values (GeneralDeclarativeHead320.environment m) .actual head).map Sum.inl)
      ((values (GeneralDeclarativeHead320.environment m) .actual _).map Sum.inl) (m arg.center).1
      (CommonNominalFullCarrier.subtype_trans lo.2 group.1)
      (CommonNominalFullCarrier.subtype_trans group.2 hi.1)).1
    exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans linked
      (GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_symm lo) (entails opened m valid))
  | record unique normal center tail order fields => exact normalized_tail unique normal center tail order fields
  | grouped norm names code center captures => exact merged_tag norm names code center captures

theorem ordered {s : State} {support : Supported s complete}
    (observed : All₂ (fun a p => Bounds s a ∧ FromSource s c i support cap a p) args patterns) :
    All₂ (fun a p => Bounds s a ∧ Result s (fact c i cap a p)) args patterns := by
  induction observed with
  | nil => exact .nil
  | cons h _ ih => exact .cons ⟨h.1,each h.1 h.2⟩ ih

end Yulang.GeneralDeclarativeHeadFrame325
