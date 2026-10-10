# q113 outgoing closure throughout the selected successful drains

Status: independently reviewed conditional source-to-implementation lemma.
The fixed six-callback interval has no intermediate physical path from q113
to R45 or R47. Alternative A/B, later diagnostic rescue, other schedules and
all-source claims remain open.

## Statement and hypotheses

This extends the authentic boundary observation in [q113 outgoing closure](2026-10-11-q113-outgoing-closure-observation.md).
For each of its six exact `constrain_live_item` invocations, consider every
sequential candidate state inside the call, including states between mutation
statements. Use the owning SCC graph: Effect rows point to physical items in
all four bound vectors; Allowance/Support views point to their canonical tails;
nonvertex atoms, relation dependencies and parent provenance are not edges.

The result is conditional on the fixed execution evidence: ENTRY and every
BEFORE_DRAIN/AFTER_DRAIN boundary show q113's complete outgoing component as
`E113 ↔ Allowance9`, disjoint from canonical R45 and R47; representatives and
the alias list are unchanged; intrusion generation is 8; and each direct drain
returns `Ok(0)` normally, with no containing-route rollback/error. These are
hypotheses for this one source interval, not a source restriction.

## Constructor argument

The frozen owners establish persistence inside each successful drain:

1. `candidate_insert_bound_impl` appends a physical bound to one vector. It
   does not replace or remove an earlier item. Fresh row/view allocation also
   appends new identities; existing view tails are immutable.
2. A nontrivial `merge_candidate_rows` transfers bounds by append, leaves old
   source storage intact, then publishes a representative and strictly
   increments the checked intrusion generation. Any failure before that
   publication propagates as `Err` through the drain; it is not swallowed.
3. Representative lookup and forest compression do not change roots. The only
   destructive physical bound/view/forest restoration is route rollback, which
   is excluded by the successful direct returns and containing-route premise.

If a nontrivial merge completed within a drain, generation would rise above
8 and could not fall back before its AFTER_DRAIN snapshot. If it failed before
publication, its error would escape the drain. Since the observed boundary
generation stays 8 and all six calls return `Ok(0)`, no completed or abandoned
partial nontrivial merge occurs in these calls. Equal-endpoint intrusion is a
no-op. Thus q113, R45 and R47 keep their canonical representatives throughout
each drain.

With representatives fixed, every physical edge present at an intermediate
state persists to AFTER_DRAIN: bound writers append, view tails do not retarget,
and no qualifying merge or rollback removes/redirects an edge. Therefore an
intermediate q113-to-R45 or q113-to-R47 path would still exist in the
AFTER_DRAIN graph, contradicting its complete two-node outgoing component.
The original q113/Allowance9 cycle also persists, so its outgoing component
stays exactly that cycle throughout all six invocations.

## Review and evidence

A fresh compiler-referee review passed the mutation audit and the
successful-return/generation argument. It recalculated all six return and
bracket locations and found no disappearing path consistent with the stated
hypotheses. Frozen inputs and code locators are detailed in
`/tmp/yulang-prover-q113-within-drain-20261011.md`.

A configured `prover` child produced the derivation through
`tools/codex-prover.sh`: `/root/proof_q113`, `agent_role=prover`. Its session
JSONL records `model=gpt-6.1-sol`, `effort=high`. The producer inspected and
hashed the frozen solver sources and existing run log; it performed no build,
test, source execution, repository write or Git operation. This proof therefore
uses the separately reviewed authentic-source observation as its runtime
premise and adds no new execution.

## Limits

The proof ends at the sixth AFTER_DRAIN boundary. It establishes no missing
ordered fiber, lack of diagnostic rescue, rollback/retry result, alternative
source/schedule behavior, or universal impossibility. The nearby source
candidate that links q to a captured Function-effect port still requires its
own actual restoration-order and later-rescue trace. Complete Yulang2 effect
hygiene transfer, general source inference, soundness/principality, production
cutover and F5 replacement remain active goals.
