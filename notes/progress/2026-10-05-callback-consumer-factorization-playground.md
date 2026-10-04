# Callback Force/body/result-consumer factorization playground

Date: 2026-10-05
Status: bounded research evidence; no production semantic or implementation authority
Governing direction: [executable inference research playgrounds](../design/2026-10-04-inference-research-playgrounds.md)
Governing theorem/design: [source-generated callback theorem](../design/2026-10-04-source-generated-callback-structural-theorems.md) §§2.3–2.6 and [production callback endpoint generation](../design/2026-10-04-production-callback-endpoint-generation-draft.md) §§3–4.

[`research_callback_consumer_factorization.py`](../../tools/research_callback_consumer_factorization.py)
compares two finite constructions for
`Force(D) >>= rebind >>= body >>= designated_result_consumer`. The reference
construction composes computations with `bind`, attaching a pending suffix to
each request continuation. An independent stage walker directly enumerates
the argument, body, and consumer relations and resumes each request without
calling the bind implementation.

The exhaustive fragment uses two values, two live states, all 16 binary
body relations, all 16 binary consumer relations, all eight request/no-request
shapes across the three stages, both initial values, and both initial states.
It compares 87,264 pending-prefix and completed observations over 8,192
graphs. Each observation retains distinct outer and latent owners and tuples,
binder scope, `J_arg`/`J_call` path IDs, callback and argument receipts, and one
fixed `nu,K,D` fiber. Argument request occurrences project to distinct `d-`
and `d+` identities; body and designated-consumer request occurrences project
to `b+`. The 35,840 completed consumer-request observations all retain the
consumer contribution in `b+`.

The first independent review found that the original Force-replay mutant only
tested evidence-projection consistency, and that both paths shared a pending
suffix helper. The checker was repaired: the replay mutant now updates `d-`
and `d+` consistently, then is rejected against the direct source-history
relation; the direct walker derives its suffix from its own ordered stage
list. The minimized omitted-consumer `b+` mutant is one direct Force result,
one body relation row, and one consumer request/response. The minimized
replay witness adds one argument request before the consumer request. Focused
execution rejects both. The reviewer delta closed both findings: replay is
rejected against the independent source-history set, and pending suffixes are
computed separately by the direct walker. This strengthens the finite
comparison but does not turn a mutated observation into an executed faulty
continuation.

This checks finite compositional bookkeeping and resumption only. It does not
derive these rows from production HIR or `ConstraintStore`, model multiple
requests within one stage, local primitive certificates, binders beyond one
scope label, witnessed concrete attachments, challenge admission, latent
future use, source-level return delimiters, higher-order payloads, or a
production endpoint denotation. Its equalities are finite characterization,
not Theorem C or callback adequacy. The production full-bound realization
crosswalk remains open.

## HIR-backed continuation boundary

`crates/yu-solver/src/tests/research_function_realization.rs` now adds
`designated_consumer_resumes_after_the_hir_derived_callback_returns` starts
from the actual collected/solved `id x = x` and `zero x = 0` artifacts. It
enumerates all 21 handled Force histories of length zero through two, where
each response chooses one of two values and one of two states. For each
history, the designated consumer request starts in the callback's final live
state and is resumed into either of two next states: 42 callback executions
and 84 consumer resumptions total. The test checks result values, state flow,
request origin/continuation, and exactly one callback receipt, Force, and body
entry per trace. Each callable retains Pure/Value role under a Handler view.

This grounds the continuation boundary in the current solver's retained
identity and constant-body Lambda artifacts. The consumer program and its
request evidence are still supplied by the test, and no production `Apply`,
consumer relation, Function-bound observation, or `b+` endpoint is generated.
`InvocationResult` carries the callback's final live state into this designated
consumer; `InvocationStep::Return` marks callback result delivery before the
consumer and complete invocation view return. The focused Rust test module
passes. The compiler-referee review is clean for this enumerated test; production
lowering and backends remain outside scope.
