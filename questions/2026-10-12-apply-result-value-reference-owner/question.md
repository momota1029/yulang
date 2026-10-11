# Apply result Value-reference owner

Question ID: 2026-10-12-apply-result-value-reference-owner
Question revision: 1
Predecessor/history: none
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): f6c2f4cbe (current HEAD when drafted)
Task/thread locator: unavailable; current working conversation
Governing source/section: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Value-reference SCC clarification”; `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–3

## Requested scoped decision

Select the source-constructor equation for Value references owned by the Value row of an `Apply` result. This decides SCC adjacency only; it does not change the approved parent/copy intrusion operation, complete Call typing, effect semantics, or source support.

## Background and current premises

The approved meaning fixes vertices as actual Value variables, edges as references in their values, and adjacency as facts established by source constructors. A subtype comparison, physical bound direction, extrusion parent record, provider possibility, or lexical nesting relation does not by itself create an edge.

The user supplied the cross-level recursive example:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

At source-owner granularity it has `even → odd` in the nested initializer and `odd → even` in the enclosing body's final expression. This establishes a nontrivial source-owner SCC across lexical levels. It does not identify either binding's Value row with the inner or outer Apply result row.

The current candidate retains distinct `callee`, `argument`, and `result` rows for Apply. It emits a negative Function demand with argument and result ports and compares the callee against that demand. Neither the approved graph definition nor the original Simple-sub application rule supplies an owner equation for references on the Apply result row. The bounded source audit found two locally distinguishable completions:

## Options and consequences

### A. The Apply result row owns the resolved computation fragment

Every resolved Name in the Apply source fragment contributes an edge from the result row to its actual binder Value row, before and after dispatch. For `konst 1`, this gives `r → konst` even though the returned provider is the literal `0`. This is a source-computation reference and does not assert that the runtime result object points to `konst`.

This gives a stable, provider-independent adjacency rule. If a path `konst →* r` exists, the added edge can make the result row and `konst` mutually reachable and can qualify an extrusion pair that option B does not. It must not be inferred from the Function demand ports; the Apply source constructor must retain the resolved Name incidence explicitly.

### B. The Apply result row owns the returned Value content

The result row receives the references of the actual Value returned by the complete Call. For `konst 1`, the returned literal has no outgoing reference, so `r` has no `r → konst` edge from that call. For `invoke f = f 1`, result adjacency depends on the same returned provider selected and checked by complete Call; it cannot be fixed from the Apply syntax or result type alone. The source Lambda still owns its code reference `invoke → f`.

This requires an explicit pending-call and result-forwarding law that preserves provider identity, source scope, and reference transport. It can qualify fewer parent/copy pairs than option A. The binder-level `odd`/`even` SCC remains in either option; the example does not decide this Apply equation.

## Affected work

Blocked scope: defining Apply-result Value adjacency; proving its source construction and transport; deciding whether any Apply-result parent/copy pair qualifies for intrusion.

Independent authorized work: Simple-sub generation/propagation proofs, non-Apply Value constructors, complete Call source construction, effect hygiene, and their disjoint source/consumer gates.

Required answer: select A or B, or state a combined rule precisely, including which source references are owned before a Call provider is known and how the selected result content is attached after dispatch. A preference without a constructor equation is insufficient to implement the SCC graph.

Pending publication: keep this entire question directory unstaged and uncommitted until the questioning primary validates an explicitly approved local answer and commits the matching question/draft/answer together. Posting does not pause the goal; only the dependent Apply-owner gate waits.
