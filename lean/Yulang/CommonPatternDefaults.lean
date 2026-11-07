import Yulang.CommonPatternEnvironment
import Yulang.CommonOptionalBound

/-!
# Finite Common constraints for the optional input of a pattern default

Pattern defaults test the original record's optional payload. A strict record
extension is a different operation: it evaluates its fallback even when the
field is present. We use the independent `OptionalPayload` observation here,
and compile it to a finite disjunction of ordinary Common subtype constraints.
The unconstrained top-payload branch is necessary at constructor depth zero.
-/

namespace Yulang.CommonPatternDefaults

open Core.PresenceGeneration
open CommonDefaultRequired (OptionalPayload)

/-- No semantic predicate or source typing is embedded as a formula atom. -/
def optionalConstraints (label : Nat) (source payload : TyTerm α) : Formula α :=
  .or (.and (.tyLe .top payload) (.tyLe source .emptyRecord))
    (.tyLe source (.union .exactEmpty (.required label payload)))

/-- All shared slot assignments and all Common payloads are admitted, including
regular types and top. The result preserves the full optional observation,
without replacing the original record by its selected field. -/
theorem optional_constraints_exact (ρ : α → Comp Common.model)
    (label : Nat) (source payload : TyTerm α) :
    (optionalConstraints label source payload).Holds Common.model ρ ↔
      OptionalPayload label (source.eval Common.model ρ) (payload.eval Common.model ρ) := by
  simpa only [optionalConstraints, Formula.Holds, TyTerm.eval,
    Common.model, CommonOptionalBound.guardedOptional] using
    (CommonOptionalBound.optional_payload_branches_exact label
      (source.eval Common.model ρ) (payload.eval Common.model ρ)).symm

end Yulang.CommonPatternDefaults
