# Initialization ordering: which effect observation counts?

Question ID: 2026-10-16-initialization-effect-order-observation
Question revision: 1
Predecessor: forward-definition-initialization-context q1/a1 revision 2, integrated at 885012b42
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision: 44bc1e530; runtime boundary candidate machine SHA-256 04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c
Task/thread locator: continuing playground/inference/execution conversation; stable message URL unavailable
Status: independently reviewed and presented; pending user decision; no decision presumed

Independent prepublication review: compiler-referee `runtime_semantic_review`
returned CLEAN for the supporting source proof and question coherence;
`ordinary_carrier_contract` returned CLEAN for scope/conformance. These reviews
select no observation boundary or scheduling policy.

## Established decision retained

The approved replacement says:

> エフェクトが発生した行同士は交換できない，ということで．それ以外はOKです

It also separately specifies global handling or error for effects escaping
initialization. It approves neither blanket dependency-first timing nor a
concrete detector or extra uninitialized-reference policy. This question retains
those decisions and asks only which computation observation the ordering clause
counts. It selects no old A/B publication law or new global consumer.

## Concrete distinction

The existing source kernel distinguishes a Request handled inside a computation
from one escaping that computation. Consider:

```yu
act signal:
    our ping: int -> int
my first = {
    my x = later
    catch signal::ping 1 { signal::ping(p), _ -> x, v -> v }
}
my later = catch signal::ping 2 { signal::ping(p), _ -> p, v -> v }
my main = first
```

The bounded [source/frame construction](../../notes/theory/2026-10-16-initialization-effect-order-source-observation.md)
shows the current forward-demand route handles `ping 2` inside later, then
`ping 1` inside first. Both initializers return 2 without any Request escaping
that initializer. This is an interleaved evaluation, not a literal exchange of
whole code blocks. It separates the observation predicates and does not prove
that this route satisfies the new ordering rule. No global consumer or pending
cache publication is captured. The static proof is not a new execution result
or full compiler-admission theorem.

## Exact options and consequences

1. **Count effects escaping each initializer (recommended).** An initializer
   whose own handlers consume all requests is not effect-producing at this
   outer ordering boundary. Effects reaching an automatic global consumer
   still count: the global consumer lies outside the initializer. In the
   example, internal request order alone does not violate the ordering rule.
2. **Count internal Request occurrences too.** Handling a request inside an
   initializer does not remove that initializer from the effect-producing
   ordering relation. The shown later-then-first occurrence order cannot be
   justified by empty outward effects. A scheduler/detector needs to account
   for this broader observation; an empty outward effect row alone is not a
   sufficient certificate.

Both options concern actually observed effects. A declared permission or
nonempty static allowance alone does not prove that an effect occurs. Neither
option chooses a detection algorithm, allows speculative observable effects,
requires universal initializer purity, or defines how an impossible forward
dependency is rejected. Such issues keep their own construction/authority gates.
A replacement observation rule is also possible if its boundary is stated.

## Requested decision and blocked scope

Which observation governs the approved relative ordering: requests escaping
each initializer, or also requests handled inside it?

Blocked work is only source effect-order interpretation and dependent scheduling
implementation. The independently reviewed initializer-to-caller handler boundary
and native inference proofs continue. Approval of an observation boundary does
not prove the scheduler correct or resolve every forward dependency.

Governing sources: approved predecessor revision 2 and its consumed receipt;
notes/design/2026-10-16-initialization-order-global-effects.md;
ordinary-computation-semantics-package §§2,5. Keep this directory unstaged and
uncommitted until an exact approved question/draft/answer bundle is validated by
the questioning primary. The separate answerer preserves revisions and writes
only selected answer files, without Git operations.
