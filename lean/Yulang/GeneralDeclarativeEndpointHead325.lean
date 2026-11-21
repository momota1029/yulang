import Yulang.GeneralDeclarativeNamedHead325
import Yulang.GeneralDeclarativeNominalTrace323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointHead325
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives entails semantic)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeTraceExpand323 (convert expands)
open GeneralDeclarativeTermCapture322 (Shared KnownNames named named_binds)
open GeneralDeclarativeNominalTrace323 (lower_nominal_sits invariant_use_tag)
open GeneralDeclarativeExactWalk323 (Exact of_rigid)
open GeneralDeclarativeRigidCode323 (Codes rigid_of_walk)
open GeneralDeclarativeNFHead324 (Scan fact produces)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value values)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalIntervalLaws (nominal_sandwich)
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralDeclarationPatterns (normalize)

/-- Neither raw interpreted syntax nor a preattached center is needed
for this invariant constructor. Supported lower positions supply the
real occurrence list; the ordinary upper row closes the sandwich. -/
theorem invariant_nominal {s : State} {support : Supported s complete}
    (bounds : Bounds s arg)
    (written : translate c i (normalize p) = some (.nominal k forms))
    (kind : Codes forms)
    (lower : Trace (restriction support) .lower arg.lower (.nominal k forms) raw)
    (upper : Derives s (.variable arg.upper) (.nominal j upperForms)) :
    Scan s c i arg p (raw.map convert) := by
  obtain ⟨head,known⟩ := lower_nominal_sits lower
  obtain ⟨term,really,walk⟩ := expands (invariant_use_tag lower)
  refine ⟨bounds,term,.nominal k forms,?_,written,of_rigid (rigid_of_walk walk (.nominal kind))⟩
  intro m valid
  have ends := bounds_sound bounds m valid
  have lowerView := entails known m (restrict_models support m valid)
  have upperView := semantic upper m valid
  have centerSame : Equivalent (m arg.center).1 (value (environment m) .actual (.nominal k head)) :=
    (nominal_sandwich k j ((values (environment m) .actual head).map Sum.inl)
      ((values (environment m) .actual upperForms).map Sum.inl) _
      (subtype_trans lowerView.2 ends.1) (subtype_trans ends.2 upperView.1)).1
  exact eqv_trans centerSame (eqv_trans (eqv_symm lowerView) (entails really m (restrict_models support m valid)))

theorem named_scan {s : State} (scanned : Scan s c i arg p actual)
    (included : actual ⊆ all) (sharing : Shared s all) (names : KnownNames s all pool)
    (ranges : Nat → Capture) : Bounds s arg ∧ Result s (fact c i (named s all pool ranges) arg p) := by
  obtain ⟨payload,code,center,printed,walked⟩ := scanned.observed
  have chosen := named_binds (initial := ranges) included sharing names walked.walked
  exact ⟨scanned.range,produces scanned (fun m valid o here => semantic (chosen o here) m valid)⟩

theorem positive_nominal {s : State} {support : Supported s complete}
    (bounds : Bounds s arg)
    (written : translate c i (normalize p) = some (.nominal k forms))
    (kind : Codes forms)
    (lower : Trace (restriction support) .lower arg.lower (.nominal k forms) raw)
    (upper : Derives s (.variable arg.upper) (.nominal j upperForms))
    (included : raw.map convert ⊆ all) (sharing : Shared s all) (names : KnownNames s all pool)
    (ranges : Nat → Capture) : Bounds s arg ∧ Result s (fact c i (named s all pool ranges) arg p) :=
  named_scan (invariant_nominal bounds written kind lower upper) included sharing names ranges

end Yulang.GeneralDeclarativeEndpointHead325
