# Parent-copy SCC intrusion: current user decision

Status: Authoritative within the operation explicitly selected below
Scope: extrusion parent retention and same-SCC parent/copy equality in the successor
Approved-by: user, directly in the working conversation
Approved-at: current conversation; exact message timestamp unavailable
Baseline: `7334dcfdb6f9d57eff04f02fb575fbba1ef1b414`
Supersedes: earlier unselected-operation assumptions only; no full cutover approval
Mechanism review: bounded architecture packets and M2 implementation/delta reviews complete
Implementation: private successor with bounded owning runtime regressions; public cutover not certified

## Direct decision

The user clarified that intrusion is the operation used to process SCCs, then
defined it directly:

> extrusionではfreshな変数がfreshでない変数を参照したときにコピーを行うわけですが，このとき親を覚えておきます．そしてSCC内にこの変数同士が入った場合，型変数を親に戻します（正確には親とイコールになります）．これがintrusionです．

After the primary restated parent/copy retention and equality, the user instructed:

> では入れてください

This is direct implementation authorization, not a pending answer-board handoff.
Do not demand another approval for this already selected operation.

## Selected operation and compiler responsibility

The later [value-to-type association clarification](2026-10-12-intrusion-value-type-association.md)
controls the graph domain and activation test: SCCs belong to value variables;
intrusion acts on their associated extrusion-related type variables. References
below to parent/copy SCC membership must be read through that association,
not as placing type-copy rows themselves in the Value-reference graph.

Retain the actual parent when extrusion creates a copy. When that copy and its
parent enter the same SCC, equate the type variable with its parent. Equality
must affect actual solving and later use, not just an observation or printed
name. Parent provenance is recorded at creation, not reconstructed from IDs,
levels or matching endpoints.

The implementation must connect this operation to actual successor SCC
processing. Merely leaving recursive internal uses rejected, or adding unused
parent metadata, does not satisfy the requested implementation.

## Value-reference SCC clarification (direct user decision, 2026-10-11)

The SCC qualification is over Value variables and edges are references in
their values. A comparison judgment such as `a <: b` is not itself an edge.
References may cross the extrusion-family tree: a parent value may reference a
child, and a nephew value may reference an uncle. These actual references can
form SCCs. Do not infer the graph from subtype direction or from parent/copy
metadata; the source constructors that create the references determine its
adjacency. This clarification supersedes earlier candidate graph definitions
that treated comparison judgments as edges or treated bound-storage adjacency
as unverified merely because it was stored on a lower/upper side.

Value/effect kind, polarity-specific copies, bounds, lexical levels, shared
captures, fresh-use independence and transactional state remain concrete
correctness responsibilities. The bounded mechanism review resolves data
structures and integration against those requirements; it does not replace the
user's operation with a different one to simplify a proof.

### Apply-result source-fragment ownership (direct decision, 2026-10-12)

For an `Apply` expression, its result Value row owns the resolved Name
references in the Apply source fragment. Each such reference contributes an
edge from the result row to the actual Value row of the resolved binder,
before and after Call dispatch. For example, `konst 1` contributes
`result → konst` even when the returned provider is the literal `0`. This edge
records source-computation incidence for SCC construction; it does not claim
that the returned runtime object points to the callee or argument.

The Apply source constructor must retain this incidence explicitly. Function
demand ports, subtype comparisons, bound-storage direction, possible or
selected providers, and extrusion-parent metadata do not create or replace
these edges. This decision fixes Apply-result adjacency only. It does not
complete Call typing, define effect behavior, prove source-to-row construction
or transport through extrusion/fresh use, or establish that any retained
parent/copy pair qualifies for intrusion.

#### Nested Apply membership (user-approved decision, 2026-10-12)

Approval is recorded in the integrated answer for
[`2026-10-12-nested-apply-reference-membership`](../../questions/2026-10-12-nested-apply-reference-membership/approved-answer.md),
revision 1.

An Apply result recursively owns resolved Name occurrences in its callee and
argument source subtrees, including nested Apply callee/argument subtrees. For
`my use f = f(0)(0)`, the two Apply results therefore contribute `R1 → F` and
`R2 → F`, where `F` is the original resolved binder row for `f`. Syntactic
containment alone does not contribute `R2 → R1`; every edge targets the row of
an actual resolved Name occurrence.

This decision does not settle Lambda, Block, wrapper, or local-initializer
boundaries for Apply-fragment membership. It does not extend the Apply rule to
other source constructors or establish source-to-row construction or transport.

#### Definition-root Value ownership (user-approved decision, 2026-10-12)

Approval is recorded in the integrated answer for
[`2026-10-12-definition-root-value-reference-forwarding`](../../questions/2026-10-12-definition-root-value-reference-forwarding/approved-answer.md),
revision 1.

At definition publication, the definition root owns resolved Name references
in its source-owned initializer/body. A nested declaration's initializer
references belong to that nested declaration's own root. These are explicit
Value-reference incidences; they do not identify definition roots with
Lambda, Block, or Apply rows and are not inferred from subtype constraints.

Thus the nested `odd`/`even` source has root edges `O → E` and `E → O` across
the lexical/inference-level boundary, when its Names resolve to those roots.
Value-reference SCC eligibility is not restricted by lexical level. The rule
does not establish that the current compiler emits or transports these edges,
that an extrusion parent/copy pair is in this SCC, or that equating such a pair
preserves soundness or required principality.

The boundary of the Apply decision is deliberate: recursive membership covers
nested Apply callee/argument subtrees only. It does not settle Lambda, Block,
wrapper, or local-initializer boundaries for Apply-fragment membership. The
definition-root decision separately owns Name references in each definition's
source-owned initializer/body; it does not imply that the root is identical to
the body's Lambda, Block, or Apply row.

The nested `odd`/`even` example also makes clear that lexical nesting and
inference levels do not filter or rank Value-reference edges. The source-owner
references point in both directions across the nesting boundary; this is not
evidence that the exact text is admitted by current Y3 HIR or that an actual
native parent/copy pair is in that SCC.

## Retained boundary

The full inference/F5 replacement objective remains active. Complete Call,
effects/protection and source/public correspondence retain their contracts.
This decision does not by itself prove soundness, principality, recursive
acceptance or target-branch replacement. Frozen `main` remains untouched; the
current implementation branch is `research/simple-sub-intrusion`.

## Implementation checkpoint

The [implementation record](../progress/2026-10-10-parent-copy-intrusion-implementation.md)
records actual canonical equality, bound propagation, live-root recapture,
recursive internal uses, transactional rollback and review repairs. Source-row
identity is session-scoped canonical identity across retained snapshots;
structural node content/identity remains historical. Owning candidate/default
builds passed. The later [runtime regression record](../progress/2026-10-10-intrusion-runtime-regressions.md)
adds five passing tests for actual extrusion provenance, same-SCC equality and
its control, merged metadata/later bounds, rollback and natural recursion/live
captures. It distinguishes direct operation evidence from source-only SCC
claims. Broader semantic correctness and target cutover remain uncertified.
This status does not expand the approved operation.
