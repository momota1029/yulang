# Intrusion joint-use renaming review

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Scope: conditional same-member batch renaming theorem in the intrusion draft
Status: reviewed conditional lemma; Gate C remains open

## Change

The abstract-semantics draft now states the renaming result over a many-sorted
identity signature, including at least value and latent-effect identities. A
use-local renaming is sort-preserving, fixes the receiver namespace, and maps
the complete surviving member-local namespace into a fresh range disjoint
from both receiver identities and other use ranges. The well-formedness premise
requires every selected view, continuation, and observation read to be covered
by one of those namespaces.

The statement quantifies an arbitrary finite joint continuation `W`; it can
couple observations and constraints across independent uses. The product
renaming preserves the full joint relation, not only isolated per-use
continuations. Recursive rows remain inequalities with variable references
interpreted by assignment lookup. For each fixed admissible receiver
assignment, empty local fibers remain empty.

The statement is intentionally conditional on the endpoint carriers, semantic
equivariance, and an already selected complete member view. It does not prove
Oracle root projection, cross-member identity composition, principality,
source-lowering correspondence, or public observation parity. If evidence
payload validity is included in view selection, its evaluator must also be
equivariant; otherwise its validity remains a separate edge-selection
obligation. Handler hygiene remains outside this lemma.

## Independent review

An independent compiler-referee delta review closed the prior findings about
many-sorted type/effect identities and joint constraints between uses. It
confirmed that recursive inequalities and pointwise empty-fiber preservation
remain explicit. The referee raised one minor precision issue about evidence
payload validity; the draft now makes its equivariance premise explicit or
leaves validity to the separate selection proof.

An independent spec-auditor delta review found no remaining finding in the
theorem's contract scope. The candidate remains unselected and does not amend
the reviewed research charter or authorize implementation.

## Verification and next gate

`git diff --check` passed. No code, tests, Python model, or measurements were
used or changed. Next define the semantic carrier and public type normalizer
for the declared Oracle source envelope, then connect source lowering and
ordered root preparation to that semantics. The full Oracle-equivalence proof
and replacement implementation remain incomplete.
