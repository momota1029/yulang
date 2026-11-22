import Yulang.GeneralStoppedCanonicalChoice335
import Yulang.GeneralStoppedDisplayOriginal335

open Yulang
open GeneralStoppedCanonicalChoice335 (SameWait election_exact)
open GeneralStoppedCanonical335 (sourceCanonical)
open GeneralStoppedDisplayExtended335 (expanded augmented)
open GeneralStoppedDisplayExtendedChoice335 (elect_parent)
open GeneralStoppedDisplayProjection335 (parentDemand)
open GeneralStoppedDisplayGuard335 (waiting)
open GeneralNominalExamples (registry interpretation)
open GeneralDeclarationExamples (display)
open GeneralCanonicalChildOrder (canonicalDeclaration)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeInlineEndpoint331 (candidates)

example (done : Nat → Prop) :
    Elected expanded (sourceCanonical registry) interpretation (augmented done)
      (candidates (augmented done) (sourceCanonical registry) interpretation waiting)
      parentDemand (canonicalDeclaration display) :=
  (election_exact (written := List.mem_cons_of_mem _ List.mem_cons_self) (same := fun _ _ => Iff.rfl)).mp
    (elect_parent done)

#print axioms Yulang.GeneralStoppedCanonicalChoice335.recurs_iff
#print axioms Yulang.GeneralStoppedCanonicalChoice335.blocked_iff
#print axioms Yulang.GeneralStoppedCanonicalChoice335.election_exact
