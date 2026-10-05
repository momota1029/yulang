# SCC generalized-boundary producer/consumer contract

Date: 2026-10-05
Status: source-grounded migration contract and exact open proof obligation; no successor semantics, carrier, or implementation authority
Baseline: `f65d68c5d43623f0d8a02194142828ec144755ab`
Review: architect audit, code-path explorer, and clean spec_auditor delta review; no theorem certification

## Result

The source-grounded obligations for a single SCC boundary can be stated
without choosing an SCC carrier or preserving F5's `Q/R` scheme. The current
code supplies a component schedule and one bounded consumer behavior, but it
does **not** establish that a successor producer is adequate for the source
language envelope. The exact missing prerequisite is **source-boundary
adequacy**: source generation must determine the complete component roots,
local-versus-fixed identity relation, directed/effect obligations, and
required evidence from source constraints plus the actual enclosing live
context. Consumer-extension preservation is a separate subsequent theorem
obligation, not part of the missing premise.

This is a local proof gate required by the larger soundness/principality goal;
it is not a premise that a regular solution exists, and it does not close
production conformance. The pending production-inlet context question is an
independent blocker for Function-context-dependent extensions.

## Governing authority

- The [SCC-intrusion charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
  §§1–4 treats F5's generalization and closed-scheme architecture as
  replacement material. It requires explicit semantics for crossing versus
  local identities, outer sharing, recursive SCC sharing, independent use
  substitutions, visibility, failure, and source envelope.
- The [static SCC session design](../design/2026-09-21-oracle-aligned-static-scc-inference-session-draft.md)
  §§2–5 fixes the current owner, dependency-first schedule, internal-use
  routing, all-member draft barrier, post-finalization incoming routing, and
  whole-attempt failure. Its F4 scheme payload contract is limited to its
  declared scope.
- The [experimental transport gate](../design/2026-10-04-intrusion-experimental-transport.md)
  is Authoritative only for test-only identity transport. Its root, local/fixed
  partition, and selected bounds are supplied inputs; it expressly does not
  prove their source generation or adequacy.
- The [cross-edit rebuild addendum](../design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md)
  requires a future complete generalized interface/equality proof for
  downstream reuse, but selects no fields, canonical form, or component
  granularity.
- The [cutover seam audit](2026-10-05-cutover-migration-seam-audit.md)
  identifies whole-attempt `InferenceSession` as the current owner and names
  this SCC-boundary contract as the next useful evidence, not as an approved
  production seam.

## Abstract producer/consumer contract

Write `Γ` for the enclosing live inference context and `C` for one scheduled
SCC. These are mathematical indices, not proposed runtime records. A producer
and consumer must satisfy the following source-checkable obligations:

1. **Source-derived boundary.** Derive every member root and the local/fixed
   identity partition from the collected source/SCC inputs and `Γ`. Do not
   accept the partition as an unexplained oracle parameter.
2. **Joint outgoing relation.** Preserve the member predicates and every
   semantically relevant directed value bound, coupled effect bound, guarded
   recursive relation, scope dependency, and required evidence jointly over
   the same assignment. Do not replace them by printed type text, a root-only
   value projection, or independently solved marginal ports.
3. **Fixed-context sharing.** Identities classified as enclosing/non-generic
   retain their shared identity and existing constraints; component-local
   identities may be generalized. No local freshening may capture or split a
   fixed identity.
4. **Visibility and internal recursion.** All roots in `C` are produced as
   one logical generalized result. Internal uses remain connected to live
   member roots before that result becomes visible to incoming consumers.
   The current ordering permits physical member installation one by one only
   behind the all-member barrier.
5. **Consumer extension.** Each incoming use receives a fresh substitution
   for component-local binders, shared consistently at every occurrence
   within that use, while preserving fixed identities. The consuming
   occurrence's constraints are added to the same enclosing live context.
   Distinct uses cannot alias their local substitutions; later constraints
   from the caller must observe the same sharing and evidence as direct joint
   source solving.
6. **Failure and observations.** A failed reconstruction publishes no partial
   successful component or mixed-version result. The complete cutover proof
   must separately disposition the existing public Term/artifact lineage,
   ordered projections, diagnostics/causes, facts/provenance, counters, and
   result queries; those observations are not all automatically fields of the
   successor's semantic interface.

The central preservation statement is relational, not representation-specific:
for every admitted source component, fixed enclosing context, and finite
sequence of incoming uses with subsequent caller constraints, solving the
source component jointly with those uses and producing then consuming its
generalized boundary must yield the same joint admissible solutions and
source-defined observations. Generality/principality and source-envelope
coverage remain separate obligations over the resulting constrained
interface. This statement does not equate F5 scheme equality with semantic
equivalence.

## What the current implementation establishes

The current production path in `crates/yu-solver/src/lib.rs` is:

```text
dependency-first SCC
  -> internal-use routing
  -> per-member generalization drafts under one frozen bound epoch
  -> joint draft normalization and all-member visibility barrier
  -> member finalization and installation
  -> incoming-use instantiation/routing
```

The current `DefinitionUse` retains exact use/parent/target identities,
occurrence/cause, frozen use level, consuming value component and target-root
component. Internal routing adds `target-root <: use-value`. Incoming routing
uses a per-use substitution map for quantified and recursive binders, restores
recursive bounds under the consuming occurrence/cause, and adds resulting
constraints to the enclosing attempt. This is evidence for scheduling,
identity discipline and transaction behavior in the current implementation;
it does not prove successor source adequacy.

The F5 `GeneralizationDraft` payload currently consists of a quantifier count,
recursive lower/upper bounds, and a positive predicate. Its structural nodes
preserve polarized value constructors, Function argument/result sharing and
recursive structure. Function effect ports are fixed pure leaves; the
generalizer accepts only the corresponding pure-effect rows. It serializes no
Pure/Handler role, callback invocation view, cast/adapter choice, attachment,
subtraction evidence, or generalized effect-row relation. Source identities,
scope/level metadata, guarded traces, and diagnostics remain in other
session/store structures, not in that payload.

The current exported queries also observe more than the root predicate:
`finish` projects live occurrence bounds, `root_value_for` collapses structured
and quantified roots to `Unknown`, and `SolvedModule` retains the store,
diagnostics, provenance, and counters. Public projection equality therefore
cannot stand in for generalized-boundary equality.

## Exact missing premise and stop line

The current evidence does not establish that source generation constructs a
producer input satisfying clauses 1–3 for the claimed successor envelope. The
missing premise is not a more convenient representation: it is the
source-to-boundary relation that determines roots, fixed/local identities,
joint value/effect obligations and evidence from source plus the actual
enclosing context. After deriving that relation, a separate consumer
extension theorem must prove that fresh incoming uses preserve all later
caller constraints and observations for this boundary. Soundness,
principality, and coverage of the claimed source envelope remain broader
gates.

Current HIR does not emit general callback application nodes, and current F5
scheme payloads admit only pure Function effects. Thus the present production
path cannot witness the broad callback/effect boundary. This is a concrete
generation/payload mismatch, not a counterexample to SCC-intrusion semantics.
The result does not authorize copying the F5 payload, adding a parallel
carrier, or routing production through the test-only transport model.

## Review and verification scope

The architect audit reviewed the governing contracts and localized source
boundary adequacy as the prerequisite. The explorer audit traced the current
producer, installer, one incoming consumer, and exposed query surface in
source. Their reports are the basis of this map; this note is the primary's
reconciliation, not independent theorem review.

Checks: source locator reads and `git diff --check`. No tests, builds,
measurements, or production edits. The note establishes neither soundness nor
principality, has no design authority, and does not close the main theorem.
