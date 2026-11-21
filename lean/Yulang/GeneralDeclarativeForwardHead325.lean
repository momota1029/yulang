import Yulang.GeneralDeclarativeEndpointHead325
import Yulang.GeneralDeclarativeTraceTransfer325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeForwardHead325
open GeneralDeclarativeHead320 (State Models Equation environment)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives entails semantic)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeTraceExpand323 (convert expands)
open GeneralDeclarativeTraceTransfer325 (ordinary)
open GeneralDeclarativeTermWalk322 (Walk Occurrence Binds actual_head_eq substitute)
open GeneralDeclarativeTermCapture322 (Shared KnownNames named named_binds)
open GeneralDeclarativeNominalTrace323 (lower_nominal_sits invariant_use_tag)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value values)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalIntervalLaws (nominal_sandwich)
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralDeclarationPatterns (normalize)

/-- The forward head equation uses congruence, not cancellation. This
covers the actual normalized traced constructors including record,
variant and join, without pretending that joins can be inverted. -/
theorem by_walk {s : State}
    (written : translate c i (normalize p) = some code)
    (center : Entails s ⟨arg.center,exp⟩)
    (walk : Walk .actual exp code links)
    (same : Binds s cap links) : Result s (fact c i cap arg p) := by
  refine ⟨[⟨arg.center,logical cap .actual code⟩],by simp [fact,written],?_⟩
  intro row has m valid
  cases List.mem_singleton.mp has
  exact eqv_trans (center m valid) (semantic (substitute walk same) m valid)

theorem actual_trace {s : State} {support : Supported s complete}
    (written : translate c i (normalize p) = some code)
    (center : Trace (restriction support) .actual arg.center code raw)
    (included : raw.map convert ⊆ all) (shared : Shared s all) (poolKnown : KnownNames s all pool)
    (base : Nat → Capture) : Result s (fact c i (named s all pool base) arg p) := by
  obtain ⟨exp,shown,walk⟩ := expands (ordinary support center)
  exact by_walk written (entails shown) walk (named_binds included shared poolKnown walk)

theorem from_nominal_ends {s : State} {support : Supported s complete}
    (bounds : Bounds s arg) (written : translate c i (normalize p) = some (.nominal k forms))
    (lower : Trace (restriction support) .lower arg.lower (.nominal k forms) raw)
    (upper : Derives s (.variable arg.upper) (.nominal j upperForms))
    (included : raw.map convert ⊆ all) (shared : Shared s all) (poolKnown : KnownNames s all pool)
    (base : Nat → Capture) : Result s (fact c i (named s all pool base) arg p) := by
  let tr := ordinary support lower
  obtain ⟨head,read⟩ := lower_nominal_sits tr
  obtain ⟨term,opened,walk⟩ := expands (invariant_use_tag tr)
  refine by_walk written ?_ walk (named_binds included shared poolKnown walk)
  intro m valid
  have lo := semantic read m valid
  have hi := semantic upper m valid
  have group := bounds_sound bounds m valid
  have linked : Equivalent (m arg.center).1 (value (environment m) .actual (.nominal k head)) :=
    (nominal_sandwich k j ((values (environment m) .actual head).map Sum.inl)
      ((values (environment m) .actual upperForms).map Sum.inl) _
      (subtype_trans lo.2 group.1) (subtype_trans group.2 hi.1)).1
  exact eqv_trans linked (eqv_trans (eqv_symm lo) (semantic opened m valid))

end Yulang.GeneralDeclarativeForwardHead325
