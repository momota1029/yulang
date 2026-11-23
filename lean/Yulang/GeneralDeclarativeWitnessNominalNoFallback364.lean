import Yulang.GeneralDeclarativeWitnessOrientedNativeRange364

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 93000
set_option maxHeartbeats 130000000
namespace Yulang.GeneralDeclarativeWitnessNominalNoFallback364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessNonpointPort362 (receiver)
open GeneralDeclarativeWitnessSelectedNonpointRoot363 (emit)
open GeneralDeclarativeWitnessOriginalEndpointProjection364 (project)
open GeneralDeclarativeWitnessCompoundCandidate364 (convert inspect scan)
open GeneralDeclarativeWitnessActualCompoundElection364 (source unsupported)
open GeneralDeclarativeWitnessBareCandidates363 (visible)
open GeneralDeclarativeWitnessModeCoverage357 (checkDecl)
open GeneralDeclarativeWitnessConstructorModes357 (readUse)

/-- The nullary alternative is authored, visible and well-formed in the
actual registry. The unary-only election returns no certificate; it
does not reject the declaration or give preference to the bare row. -/
def backedOutOfScope {contra} (x : Ordered contra) : Bool :=
  ((source [receiver,unsupported]).bind fun e =>
    (emit x e).bind fun r =>
      (project r).map fun p =>
        decide (visible e r.occurrence = [receiver,unsupported]) &&
        (readUse e 90 0).isSome && checkDecl e unsupported &&
        (convert e r.occurrence unsupported).isNone &&
        (inspect p unsupported).isNone &&
        (scan p (visible e r.occurrence)).isNone).getD false

theorem unsupported_authored_alternative_is_not_absent (contra : Bool) :
    ((run contra).map backedOutOfScope).getD false = true := by cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessNominalNoFallback364
