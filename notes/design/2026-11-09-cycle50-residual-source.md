# Cycle50: preserve unresolved source conditions

Status: Draft. 2026-11-09. Finite positive str/equality fragment only.

## Goal and boundary
Cycle49 proved that ordinary output atoms alone lose conditional requests whose
receiver is not forced. This cycle keeps those conditions as explicit residual
slot pairs, rather than changing the meaning of ordinary atoms or the int-only
diagnostic endpoint. This is an internal representation theorem, not a language
classification decision. The independent `SourceModel` remains unchanged.

## Data and executable construction
For any table T, seed slots S, equality links L, and named requests R, enumerate
all represented request occurrence pairs. Keep a pair exactly when its receiver
is absent from the existing finite saturation. Package the saturated State with
that residual list. A packet model satisfies its ordinary atoms and the positive
str implication for every residual pair. Reuse the existing endpoint scope check
for an outer checked constructor; malformed names are errors of this adapter,
not language-visible rejection.

## Theorem plan
For every T,S,L,R,i,j, residual membership iff the named request exists and the
actual checked Index producer returns none. For every assignment a, packet
models iff `SourceModel T S L R a`. Discharged requests hold because saturation
has already derived their targets. Remaining requests hold by the residual
condition. Thus all source models, not only str consequences, are preserved.
At the outer checked constructor, success is equivalent to represented endpoint
scope, and every successful packet has the same model class as the source.

## Incremental continuation
Retain original seeds, saturated receiver facts, equalities, and only residual
request names. On receiving extra str seeds, rerun the existing finite driver
over that retained input. Prove that its full packet models equal rebuilding
the original problem with those extra seeds. Discharged requests need not be
kept: their targets are already among the retained saturated facts. Prove that
all occurrence pairs of a retained name have the same pending status by source
alias closure. The checked producer's success and pending behavior then agree
with the full rebuild, including reactivation of previously pending chains.

## Evidence and exclusions
Spec 6.3 keeps pending obligations until sibling updates stabilize and carries
unresolved constraints onward. The existing audit x-oracle X13–X17 only covers
old-engine source examples; it does not validate this carrier or its semantics.
No new Yulang2 run is performed. General payloads, arbitrary initial State,
parser/lowering adequacy, four final language classes, dictionary equivalence,
and all five general B4 bridges remain outside this result.
