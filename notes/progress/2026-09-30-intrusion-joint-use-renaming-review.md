# Intrusion joint-use renaming review

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Scope: conditional same-member batch renaming theorem in the intrusion draft
Status: reviewed conditional lemma; Gate C remains open

## Change

The abstract-semantics draft states the renaming result with one identity
namespace and occurrence roles on endpoints. A use-local renaming maps each
source identity exactly once, preserves its complete role profile, fixes the
receiver namespace, and maps the complete surviving member-local namespace
into a fresh range disjoint from both receiver identities and other use
ranges. One source identity that occurs in both value and latent-effect
positions keeps one semantic assignment package and one fresh image; role
carriers and their compatibility relation belong to the still-unselected
interpretation. The well-formedness premise requires every selected view,
continuation, and observation read to be covered by one of those namespaces.

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

An independent compiler-referee delta review first closed findings about
joint constraints between uses and recursive inequality/empty-fiber handling,
then identified that Oracle Function effects reuse ordinary TypeVar identities
and therefore can cross value/effect occurrence roles. The theorem was
revised to use one identity map and one role-profile package per source ID. A
follow-up semantic review confirmed that the inverse assignment remains
well-typed and bijective when an ID occurs in several roles. The referee also
raised a minor precision issue about evidence payload validity; the draft now
makes its equivariance premise explicit or leaves validity to the separate
selection proof.

An independent spec-auditor delta review found no remaining finding in the
theorem's contract scope, including after the identity-map correction. The
candidate remains unselected and does not amend the reviewed research charter
or authorize implementation.

## Verification and next gate

`git diff --check` passed. No code, tests, Python model, or measurements were
used or changed. Next define the semantic carrier and public type normalizer
for the declared Oracle source envelope, then connect source lowering and
ordered root preparation to that semantics. The full Oracle-equivalence proof
and replacement implementation remain incomplete.
