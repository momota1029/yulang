# Initialization order and global effect handling

Status: Authoritative replacement decision; source/implementation proof gates OPEN
Scope: top-level initialization ordering and escaping-effect consumer
Approved-by: user, forward-definition-initialization-context-a1 revision 2
Observation addendum: user, initialization-effect-order-observation-a1 revision 1, exact bundle `6b6cafea1`
Approved-at: 2026-10-16
Approval: [exact approved answer](../../questions/2026-10-16-forward-definition-initialization-context/approved-answer.md), bundle `885012b42`
Reviewed-by: `ordinary_carrier_contract`, exact bundle conformance and decision/receipt/status transcription CLEAN
Supersedes: the two proposed alternatives in question revision 1; does not select either proposed dependency-first rule

## Approved replacement

The latest explicit user wording is:

> エフェクトが発生した行同士は交換できない，ということで．それ以外はOKです

1. Effect-producing lines cannot be exchanged with one another. Forward demand
   for an unavailable definition alone does not authorize earlier initialization
   that violates that ordering. This does not require every effect-producing
   line to remain individually immovable, or impose the earlier proposed
   contiguous-pure-lines-only restriction.
2. Effects escaping top-level initialization are handled globally or produce an
   error. A handler surrounding a read of the definition's value does not thereby
   handle that definition's initialization effects.
3. Allow the possibility of registering global handlers, but keep the present
   scope to automatic handling of `nondet`, `io` and similar effects. An arbitrary
   global-handler registration feature is outside this decision's implementation
   scope. This decision does not certify any existing automatic consumer.
4. This is a replacement for the offered alternatives. In particular, neither
   alternative's blanket dependency-first initialization timing is selected.
5. Connect this rule to existing forward references, dependencies and ordered
   source root demands. Establish the actual initialization entry/return and
   effect-handling construction. Do not infer an effect-detection method or an
   additional rule for uninitialized references from this answer.

Internal initializer handlers keep their ordinary semantics. No concrete owner
switch, store snapshot, signature-keyed cache, repeated publication,
cancellation/reinitialization rule or old A/B resumed-publication alternative is
selected. Approval does not establish reachability, unreachability, soundness,
implementation correspondence or production readiness.

## Source correspondence and integration obligations

Retain the authentic mixed-root schedule from the
[module-expression design](2026-10-16-module-expression-source-owner.md).
Its implemented source-order root cursor and cache skip do not, by themselves,
prove that a suspended earlier root and demanded later initializer preserve the
approved effect-producing-line order. The [Name-role theorem](../theory/2026-10-16-definition-name-computation-role.md)
proves populated-cache observation and pure Name routing; it supplies neither
empty-cache initialization timing nor a source effect detector.

At the escaping-initializer boundary, prove the original initializer's internal
handlers remain eligible and caller-only handlers are not used to discharge
initialization. Any global consumer requires its own existing justification;
otherwise preserve an error/unhandled outcome. Establish current-store,
publication, original Name/Observe return and later cached latent execution
correspondence without importing the unresolved scheduling premise.

Keep effect-order/source construction, local handler-boundary correctness,
materialization/publication and whole-source/cutover gates distinct. No runtime
edit accompanies this decision transcription. The primary retains their owners
and will dispatch proof-supported implementation only within established scope.

The [receipt](../../questions/2026-10-16-forward-definition-initialization-context/receipt.md)
records exact hashes, approval provenance and consumption checks. The unapproved
revision-1 draft is preserved locally outside the integration bundle.

## Local implementation checkpoint

The [initializer handler boundary](../progress/2026-10-16-playground-initializer-boundary.md)
implements the escaping-effect clause only. The constructive top-GlobalRead cut
and exact repaired-source correspondence have independent CLEAN semantic/spec
review; all 108 playground tests pass. This selects no source effect detector,
early-entry timing or global consumer. Initialization order/source admission
and whole materialization remain OPEN. The observation boundary is now selected
by the following approved addendum; this does not certify an ordering algorithm.

## Approved observation addendum (2026-10-16)

Authority: [exact approved observation answer](../../questions/2026-10-16-initialization-effect-order-observation/approved-answer.md),
question revision 1 / a1 revision 1, validated and integrated at `6b6cafea1`.
The user selected option 1 and approved the complete displayed draft with `OK`.
The [receipt](../../questions/2026-10-16-initialization-effect-order-observation/receipt.md)
records exact bytes, source freshness and consumption. This addendum fills the
previously unspecified observation predicate; the preceding ordering and
global-handling decisions remain.
Independent `ordinary_carrier_contract` review is CLEAN for the exact
approved-scope addendum and matching receipt/task/index transcription.

The relative-order rule counts effects **actually escaping each initializer
after its internal handlers**. A request fully handled inside does not count.
Effects escaping a handler arm or resumed computation do count, as do effects
reaching an automatic global consumer, which is outside that initializer.
A declared permission or nonempty static effect upper bound alone does not
prove an occurrence.

In the reviewed [source-observation example](../theory/2026-10-16-initialization-effect-order-source-observation.md),
internal `ping 2` then `ping 1` with both outward images empty is not itself an
ordering violation. This observation does not certify whole-program admission,
forward-demand timing or the current scheduler. No concrete detector/scheduler,
blanket dependency-first policy, additional uninitialized-reference rule,
observable speculation or arbitrary global-handler registry is approved by
this addendum. Source construction, actual runtime correspondence and full
initialization/materialization gates retain their independent owners.
