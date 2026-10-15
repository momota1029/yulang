# Initialization and raw capture: corrected source premise

Date: 2026-10-16
Branch: `research/simple-sub-intrusion`
Runtime baseline: `35e87f844`; record baseline: `64c875556`
Status: two bounded source results independently reviewed; original successor
control correspondence OPEN. No new runtime law or implementation adopted.

The [consumed user correction](../../questions/2026-10-16-resumed-definition-materialization/receipt.md)
requires source reachability before choosing repeated-definition publication
laws. It distinguishes initializer effects from the published value reference.

## Established results

1. [Oracle publication exclusion](../theory/2026-10-16-resumed-definition-source-reachability.md),
   producer `aec1b3d4…`, has fresh compiler-referee review CLEAN. Both inspected
   Oracle runtimes publish an instance only in synchronous host return code;
   explicit request continuations cannot contain the pending write of that
   same materialization invocation. Raw/host reentry may start another
   invocation, which is not repeated completion of the original write.
2. [Actual initializer body checks](../theory/2026-10-16-initializer-effect-admission-correspondence.md),
   producer `7af1e7fe…`, also have fresh review CLEAN. Stored-value comparison
   projects `Thunk(E,Int)` to value compatibility and `Pure <: E`; it supplies
   no reverse purity or residual root-allowance certificate. Ordinary/no
   annotations, binding commit, ComputedDef and body specialization do not
   establish the proposed caller-independence premise. Explicit effectful
   annotations remain a separate source rule.

The second result is a failed proof route, not a compiler defect or permission
to require pure initializers. Effects of a root may lead to an unhandled runtime
request. Neither successful graph solving nor RuntimeEvidence::default proves
the missing initialization-control correspondence.

## Exact remaining owner

Forward Names are admitted and keep pure occurrence effects. Initializer
effects retain their original declaration/InstanceBody ownership. Oracle's mono
runtime refuses an escaping initializer request; its evidence VM resolves one
under ambient active catches before publication. The inspected root contract
does not by itself reconcile their before-publication forward-demand behavior.

The successor reifies a GlobalRead publication frame and refuses its raw
capture. Remove neither that guard nor the parent proof obligation. A proposed
initializer delimiter must preserve internal handlers, pure forwards, original
dynamic owners and caller handling of subsequently executed cached functions
or computations. Its source correctness has not yet been established.

Primary owns the original gate. The next-action selector is assigned the
actual source/root/InstanceBody-to-Name/GlobalRead control correspondence after
the failed admission route. Another conditional purity proof, blanket source
restriction or A/B publication question would not resolve this premise.

## Reviews, checks and scope

Bounded source/proof work used a constructive prover and independent
compiler-referee `runtime_semantic_review`. Separate explorer and architect
audits supplied source owners and classified the unapproved delimiter proposal.
They did not certify the proof or select source semantics. No production edits
or expectation changes occurred; no broad suite was repeated.

Primary ran two 60-second-capped CLI processes using the existing built
`target/debug/yu-playground --run main --steps 30000 FILE`:

- `/tmp/yulang-initializer-admission-negative.yu`: `pending = signal::ping()`
  without a handler exits 1 with an unhandled runtime request.
- `/tmp/yulang-initializer-admission-control.yu`: the same initializer handles
  its own operation and exits 0 with exact output `1\n`.

Exact sources are the two sentries in the admission note §6; logs share these
basenames with `.log`. These are operational controls, not proof that either
value-constraint result certifies complete source admission. No forward variant
was asserted valid or run. No timing/RSS measurements or benchmark samples.

Current task, research queue, design index and question receipt are synchronized
at integration. Native annotation-formation work independently awaits the
pending `questions/2026-10-16-annotation-declared-envelope/question.md` choice.
