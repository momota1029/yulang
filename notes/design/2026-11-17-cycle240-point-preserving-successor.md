# Cycle240 — I45 point-preserving observation successor

Status: Draft implementation of explicit I45 decision at integration2a271030.
I45 adopts option2 of239 question, retaining I44 allocation/mixed cache. The
inbox attributes this to the owner. This integration contains the inbox change,
not the asserted spec6.5 edit; the implementation follows the explicit inbox
instruction and does not edit spec itself.

Preserves(revision) means: for every old slot and descriptor, if it is recorded
and every parameter's two endpoints are equal, the revision's entry at that
same slot equals that exact descriptor. No semantic-equivalence replacement,
canonicalization or observation weakening is introduced.

New240 modules only. Successor copies every old mixed-kernel constructor and
adds Preserves to reobserve; no unrestricted old-administrative injection.
Derive erasure to234, model restriction, closure, source adapter and reachable
transport. Retain versioned allocation, trusted cache, classifier/evidence.
Prove239's actual retarget revision violates Preserves at old root slot3.
Audit other historical revisions for admissibility explicitly, not via an
unrestricted embedding. Global Acc needs a real finite-source/version argument;
blocking239's path alone is not a termination proof. Stop on a closed
counterexample that descriptor preservation loses intended refinement.
