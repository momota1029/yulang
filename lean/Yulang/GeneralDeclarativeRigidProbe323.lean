import Yulang.GeneralDeclarativeNominalTrace323
import Yulang.GeneralDeclarativeEndpointProbe321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRigidProbe323
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeEqualities322 (entails)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeTraceExpand323 (convert)
open GeneralDeclarativeRepeatedActual323 (Rigid)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeRigidCode323 (Code Codes actual_trace)
open GeneralDeclarativeRigidSource323 (Scanned Ordered)
open GeneralDeclarativeRigidObserve323 (from_expression)
open GeneralDeclarativeNominalTrace323 (from_lower_trace lower_nominal_sits)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadWFSource (PatternCovered)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (subtype_trans)

theorem direct_variable {s : State} {p : Pattern} (bounds : Bounds s arg)
    (metadata : PatternCovered c interp p)
    (spelling : translate c interp (normalize p) = some (.variable n)) :
    Scanned s c interp arg p [⟨n,.actual,.variable arg.center⟩] :=
  from_expression bounds metadata spelling .capture (fun m _ => eqv_refl (m arg.center).1)

theorem scalar_known {s : State} (observed : Trace s mode name (.primitive (.scalar b) []) raw) :
    Entails s ⟨name,.primitive (.scalar b) []⟩ := by
  cases observed with
  | primitive alias stored child =>
    cases child
    exact entails (.trans (.congruent (.variable alias)) (.row stored))

theorem scalar_probe {s : State} {support : Supported s completed}
    (metadata : PatternCovered c interp p)
    (form : translate c interp (normalize p) = some (.primitive (.scalar b) []))
    (probe : Matches (restriction support) c interp arg p) :
    Scanned s c interp arg p [] := by
  obtain ⟨bounds,code,lo,hi,known,lower,upper⟩ := probe
  have same : code = .primitive (.scalar b) [] := Option.some.inj (known.symm.trans form)
  subst code
  apply from_expression (s := s) bounds metadata form .scalar
  intro m valid
  have interval := bounds_sound bounds m (restrict_models support m valid)
  have earlier := scalar_known lower m (restrict_models support m valid)
  have later := scalar_known upper m (restrict_models support m valid)
  exact ⟨subtype_trans interval.2 later.1,subtype_trans earlier.2 interval.1⟩

theorem nominal_probe {s : State} {support : Supported s completed}
    (metadata : PatternCovered c interp p)
    (form : translate c interp (normalize p) = some (.nominal tag args))
    (contents : Codes args) (probe : Matches (restriction support) c interp arg p) :
    ∃ seen, Scanned s c interp arg p seen := by
  obtain ⟨bounds,code,lo,hi,known,lower,upper⟩ := probe
  have same : code = .nominal tag args := Option.some.inj (known.symm.trans form)
  subst code
  obtain ⟨rhs,existsUpper⟩ := lower_nominal_sits upper
  exact ⟨lo.map convert,from_lower_trace bounds metadata form contents lower
    (fun m valid => entails existsUpper m (restrict_models support m valid))⟩

end Yulang.GeneralDeclarativeRigidProbe323
