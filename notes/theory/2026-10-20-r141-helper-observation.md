# R141 helper observation: source mapping remains incomplete

Status: **UNFINISHED/OPEN**. No runtime trace or final review exists. This note
preserves the exact remaining source-to-native obligation and does not certify
the parent theorem.

## Fixed source and intended observation

The unchanged source is R138's `outer/loop/direct/helper` specimen. The target
is its completed helper Local/action25 state and the actual ordered action31
loop-Lambda histories for both the direct and helper checking occurrences.
The parent remains computation-forwarding preservation §§1, 6–7 with one shared
satisfying assignment, original current-formal identities and whole Name
arguments, arbitrary finite prefixes, repeated calls, simultaneous receiving
entries and independent foreign-continuation obligations. R72/R73, Simple-sub
A/B, inference/evaluator correspondence, source/native correspondence and
production remain OPEN.

## Evidence obtained

The rev3 proposal to collect `false,false` directly and construct a candidate
session was invalid: `CandidateInference::solve` calls
`collect_candidate_mode_scoped_v1(hir, true, true, false, false)`, and
`try_new_candidate` requires candidate graph effects. Rev4 prospectively repaired
the allowed route to public `CandidateInference::solve(hir)`.

The temporary implementation was revised toward that route and added source
mapping checks from action25's local `helper` Name occurrence and action31's
Lambda recipe occurrence to retained local-source syntax and the `loop` named
group. It also began recording replay products and relation-currentness checks.
These changes were never compiled or executed. They do not establish that the
fixed source reaches those cursors or that the records are semantically complete.

## Missing premises

No captured trace establishes the entire pending-parent snapshot and helper
capture/restoration boundaries; the authentic lineage of the direct and helper
checking occurrences through replay operation inputs and ancestry; ordered
worklist pops and replay products for each family; dispatch/currentness outcomes;
acknowledgement/return order; saved-prefix sweep order; or relevant allocator,
interner and evidence effects. Distinct replay input pairs alone do not prove
two source families. A final-state dump cannot reconstruct those temporal
transitions. Therefore the original mapped-admission premise remains open.

## Application and falsifiers

The R140 local replay-product and sweep derivations remain conditional local
lemmas only. Apply no observed fact to the parent because no runtime record was
produced. Closure requires a newly budgeted, prospectively reviewed exact
observer implementation that preserves joined ancestry, covers every required
transition, fails closed on missing events/overflow, and maps both family roots
to actual records. Any shared-only lineage, omitted transition changing a
family's selected operation, or incomplete capture falsifies the proposed
certificate. No semantic or production change follows.
