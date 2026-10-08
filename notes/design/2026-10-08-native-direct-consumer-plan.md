# Native ordinary Direct consumer: implementation design proposal

Status: Reviewed / non-authoritative; user approval required before implementation
Scope: finite proof-directed checking of ordinary `Direct(u,V)` certificates against supplied native public roots
Semantic change: none proposed; use the selected native projection contract
Production routing: none; F5 remains the only production inference implementation
Baseline: `6982402afa95f93552bdd5954d22c852b27b3f92`
Reviewed-by: independent compiler_referee, spec_auditor, performance_auditor; primary closed one minor accounting clarification
Review target: SHA-256 `f15e9e9b938ac067cd3159047a22617e329100b1fca562fb4081070c90f1b336` plus this minor-only primary clarification

## 1. Decision and boundary

This proposal defines a checker for an already supplied finite ordinary proof
term at the source-checking/resolution boundary. One proposed session belongs
to one source-checking compilation and validates every submitted `Direct`
obligation against its immutable root environment. No such successor caller
exists in production today. The checker does not search for proofs, construct
public roots, infer source types, or replace the F5 pipeline. A successful
check would produce a certificate bound to the exact submitted source and
target root instances. A failed or resource-limited check produces no
certificate.

The governing behavior is already selected by
[`native-projection-public-export-definition.md`](2026-10-08-native-projection-public-export-definition.md)
§3 and the independently reviewed
[`projection-public-export-construction.md`](../theory/2026-10-08-projection-public-export-construction.md)
§§6.1–6.3. This proposal adds no membership clause or new proof constructor.
It translates that finite judgment into a compiler responsibility. It remains
conditional on genuine root records, original scopes, and every cited local
law being supplied by its actual owner.

The decision request is whether to adopt this checker boundary and candidate
validation architecture, or to keep the reviewed theorem research-only until
the producer and consumer are designed together. Approval would authorize only
the selected checker gate. It would not authorize changing F5 routing, adding
source/application semantics, exposing a public API, claiming complete proof
search, or declaring type-inference cutover.

## 2. Selected contract

The checker receives two actual ordinary public roots `u` and `V`, their
complete original typed records, and a finite candidate proof term. It accepts
exactly the selected cases:

```text
Direct(u,V; Value(d_V))
Direct(u,V; Computation(d_T))
Direct(u,V; Function(d_D,d_P))
```

The roots are the submitted operands. A proof naming a different root,
substituting an F5 scheme row, or referring to a stale root epoch is rejected.
The consumer validates the submitted proof against the complete supplied
operand scopes and incidences; it does not resolve a hidden source root or
query the source body.

The local obligations are:

- `Value`: complete same-decorated-value membership implication, preserving
  the same value, provider, guards, hereditary obligations and full evidence
  tuple.
- `Computation`: the selected same-computation/carrier inclusion at the
  original designated interfaces, preserving every demand, observation,
  provider and dependent evidence field.
- `Function`: validate both whole Function interfaces and check
  `D_V(h) => D_u(h)` together with
  `D_V(h) and Complete_u(h,O,w) => Complete_V(h,O,w)` at their original
  joint telescope. Domain equality is not required. `Any` and ordinary union
  proofs use the Value case and acquire no fictitious Function equations.

The finite local proof tree is checked bottom-up. Whole-tuple substitutions,
branches, original binder congruence, and registered recursive equation
pairing retain their original operands and scopes. An arbitrary cycle is not
a proof. Executed conversions remain at their source boundary and are not
treated as proof-only inclusion nodes.

## 3. Candidate checker boundary

The proposed internal operation has a narrow shape:

```text
DirectCompileSession {
  one shared CompilationBudget,
  validated root environments,
  proof arenas,
  reusable flat scratch,
}

prepare_environment(
  session: &mut DirectCompileSession,
  complete_roots: CompletePublicRootPackage,
) -> Result<EnvironmentId, PreparationFailure>

build_proof_arena(
  session: &mut DirectCompileSession,
  proof_source: TypedDirectProofSource,
) -> Result<ProofArenaId, ProofBuildFailure>

check_direct(
  session: &mut DirectCompileSession,
  environment: EnvironmentId,
  proof: ProofArenaId,
) -> Result<BoundDirectCertificate<'env, 'proof>, CheckFailure>
```

The actual public-root owner supplies `CompletePublicRootPackage`, constructed
under the same compilation budget; the preparation routine validates and seals
it once, before queries, including its complete roots, scopes, typed laws and
source generation. One
`DirectCompileSession` belongs to one compilation and owns the common budget,
prepared environments, proof arenas and scratch. Environment preparation,
proof-arena construction and every checker attempt debit that same budget.
Rebuilt roots receive a new environment identity; no old certificate can
silently bind to them. Certificates borrow only the exact environment and
proof arena, so the session can continue checking other obligations while
their evidence remains alive.

`BoundDirectCertificate` is constructible only by successful validation and
borrows the exact environment and proof arena it validated. It contains the
exact source/target root slots and environment generation, plus the validated
proof reference. It cannot be forged from numeric F5 endpoints or from a
successful query. Aliases to the same root preserve its actual identity; fresh
public frames use their distinct root identity and original scope map.

The proposed representation is a flat, immutable arena, not recursively owned
proof trees, strings or arbitrary callbacks. Nodes refer to explicit
constructors, typed operands, original scope/context IDs and premise edges. A
node may be shared only when its full recorded sequent and context are the same;
reusing it under a different substitution or hypothesis context requires an
explicit checked transformation. Root and law references are dense slots
inside one immutable validated environment with a unique environment identity
and generation. Roots cannot be minted from caller-chosen F5 IDs.

Validation uses an iterative worklist and per-attempt visitation state. Ordinary
premise edges must be acyclic. The selected recursive-equation constructor is
represented separately: it contains its complete finite equation/alternative
table, original scoped recursive hypotheses and rule-specific justification.
Only references through that exact constructor are permitted as recursive
hypotheses; an arbitrary cycle is rejected. This preserves the selected
recursive-equation rule without treating all cyclic graphs as proofs. Worklist,
visitation and teardown are iterative, so proof depth does not consume the Rust
call stack.

Preparation validates root, scope, telescope, equation and law tables once,
before checking. It stores scope-tree ancestry intervals and every explicit
dependency edge. Each query borrows the same environment and proof arena; it
builds no root/scope index, clones no root payload and uses no cross-query proof
cache. A successful certificate is bound to and borrows that exact environment
and proof storage. Rebuilding an environment creates a new identity;
certificates for the old environment do not validate against it. The public
root owner is responsible for retention lifetime and generation changes.

Only closed, typed, rule-specific law constructors are accepted. A law name,
signature or registry entry alone is not evidence. Each law must be validated
by its owning constructor or supplied with its complete finite proof term and
scope. Unbounded callbacks are excluded. The complete production set of these
law owners is still an open implementation prerequisite.

The current Python checker is not this checker. It implements a conditional
same-inlet Function fragment with a much smaller proof language and externally
supplied whole-interface laws. It is not production conformance evidence.

## 4. Validation, rejection and resource boundary

For each immutable environment `e`, preparation work `P_e` charges every root,
scope, operand, dependency edge, telescope entry, equation alternative and law
table field, plus bytes examined and index initialization. Scope intervals are
built iteratively once for that environment. Each query `q` charges proof-node
visits, premise edges, operand incidences, substitution entries, telescope
checks, equation/alternative entries, local-law derivation steps, comparisons
and bytes examined. Every nested operation consumes budget before doing work.
There is no unmetered hash callback or pairwise alternative scan.

Aggregate work is:

```text
W = sum_e(r_e + P_e) + sum_q(w_q) + sum_a(g_a)
```

where `Q` includes every attempt, including failures, `r_e` is root-package
formation work for environment `e`, `P_e` is its validation/index-preparation
work, `w_q` is the actual charged checker work, and `g_a` is proof-arena
construction work for arena `a`. The environment and arena sums enumerate
every construction attempt, successful or failed; the checker sum likewise
includes every query attempt.
One `CompilationBudget` in `DirectCompileSession` is shared by root-package
formation, environment preparation, proof-arena construction and all checker
queries; it also tracks live retained bytes and transient peak bytes. Failed
root/environment builds, proof builds and queries do not refund consumed work.
The implementation must
state and enforce deterministic bounds for `W`, individual checked buffer
lengths and peak bytes before production admission. No assumption equates `Q`
with source nodes, roots or applications; `Q` is the actual number of
submitted proof attempts in the source-checking compilation. The current
repository has no selected successor source-checking caller from which to
derive a tighter query schedule. There is no cross-query proof cache; the
one-compilation session lifecycle and its single shared limit are part of the
contract. A later caller integration must account for every attempt and
cannot silently reset work or byte budgets for retries or environment rebuilds.

The proposed check is fail-closed and atomic: it publishes no
`BoundDirectCertificate` until every node and incidence validates. It uses
flat checked buffers and iterative reservation, traversal and teardown. All
length arithmetic is checked before allocation; scratch high-water capacity
and any temporary old-plus-new reservation peak are charged. Environment
preparation storage is retained once per environment, while attempt-local
worklists and visitation tables are discarded or reused by the serialized
compilation session. Concurrent compilation sessions each have their own
budget and multiply live/scratch storage by their actual concurrency; the
caller must include that concurrency in its compilation resource envelope.
It must distinguish at least:

- malformed proof or incompatible operands;
- stale/foreign root identity or scope;
- missing local-law supplier or unregistered rule;
- invalid/incomplete recursive equation group;
- deterministic size/depth/work-budget exhaustion;
- internal invariant failure.

The admitted node, edge, binder, telescope-depth, total-work and peak-byte
limits, exact error surface and caller fallback are not selected. Their exact
values must be tied to the production caller and documented supported source
envelope before implementation. If resource exhaustion is recoverable, every
attempt allocation must be discardable and the failure must remain distinct
from semantic rejection. A process-aborting OOM cannot be promised recoverable.
The proposed interface borrows the environment/proof; it does not add Arc
retention or a public API.

## 5. Alternatives still open

This draft proposes one bounded checker component with a flat arena and
borrowed immutable root environment. The separate alternative is to defer the
checker until the root producer and checker can be designed as one integration
gate. That keeps all compiler routing unchanged but also postpones the selected
ordinary Direct consumer. The arena, owner handoff, per-session budget and
borrowed certificate lifetime are proposals requiring explicit approval; the
precise numerical limits and full set of local-law owners remain later
implementation prerequisites.

## 6. Review and verification plan

This is a new internal checker architecture with soundness, scope, root-owner,
recursion and resource boundaries. Proposed review mode: M3, with up to three
independent reviewers on the frozen artifact:

- `compiler_referee`: root identity, joint scope, same-provider preservation,
  recursive proof validation and atomic certificate publication;
- `spec_auditor`: exact conformance to the selected Direct cases and no semantic
  expansion;
- `performance_auditor`: only if the selected representation has material
  traversal/allocation uncertainty; otherwise the primary records static cost
  bounds and omits this review.

No tests, builds or measurements are proposed for this design-only revision.
After an approved implementation exists, focused tests must cover all three
proof cases; whole-callable `Any`/union; actual-root substitution rejection;
rigid versus fresh scope; complete alternative/equation coverage; nonidentity
result widening; narrower domains; same-value/provider preservation; and
atomic failure at every bounded validation stage. A focused solver check comes
first; broader verification waits for the coherent cutover boundary and the
resource behavior of the selected suite.

## 7. Approval boundary and remaining gates

Before implementation, independently review the frozen proposal, resolve its
representation, rule-trust, root-minting and resource/failure choices, and
record the user's explicit approval. This checker gate alone does not discharge
the separately open public-root producer, actual F5/HIR bridge, natural source
inference, principality, full production extras, publication lifecycle or F5
replacement gates. The missing authentic Parameter telescope and the pending
flat-Application owner-family decision remain separate prerequisites for their
affected work; neither is assumed by this checker contract.

The checker gate stops if validation requires reconstructing an absent owner
fact from F5 rows, resolving a different root than the submitted public root,
dropping a licensed proof alternative, or trusting an unproved local-law tag.
