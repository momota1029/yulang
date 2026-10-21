# Sprint R244 — Forwarding capture across cuts

Status: ACTIVE_PROOF_SOURCE_AUDIT; Luna sole primary. Serial, no workers.
Baseline: `5221763232e44c078f2fcae2e8ae46cb4aa7323c`.

## Fixed parent and outcome

Parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7, SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`. Preserve its shared assignment, original formals, arbitrary finite chains, repeated calls, simultaneous entries and finite-prefix quantifiers. R242 and R243 are partial, unreviewed handoffs; R71/R72 and production remain OPEN.

Prove or falsify a graph-cut invariant for forwarding capture: each required source edge must either be restored inside the captured local region or remain valid through an unchanged shared endpoint under its authentic per-use map. Apply it to R187's bridge/relay case and then the parent's finite-chain step. Enumerate physical owners for each edge, including reverse discovery from the relay return-effect through a completed Lambda origin, ordinary expansion, shared-anchor preservation and each Local route. Equal canonical endpoints and logical connectivity do not establish a physical path.

Treat completion evidence as a distinct premise. `record_source_drain_completion` silently returns when `try_reserve` fails, while inference may succeed. Determine whether the needed reverse-discovery edge is preserved without that receipt. Do not narrow the parent to executions retaining instrumentation receipts. A counterexample must derive the missing required edge from source constructors and show it is absent from both capture and licensed shared anchors.

## Lanes, limits and handoff

Serial Luna proof/source audit. No child/Astra, code changes, tests, builds or samples. Implementation `NO_SAFE_CODE_SLICE` unless an approved-contract violation is established; no repair authorization. Cap 900 seconds, no carryover. Freeze at a proved cut invariant, exact failed transition or cap. Fresh independent review required for promotion. Unknown legacy leases remain quarantined.

Exact write leases: this contract, `notes/theory/2026-10-21-r244-forwarding-capture-cuts.md`, and `tasks/agent-loop/current.json`.

## Direct dependency pins

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  parent §§1,6–7
d61602922c7e656a605e1649d59b436b9fac03b0bd10eb900a6106c46cbedfe1  R243 contract
15e375d943cbd3b89487eb551e3b2305010e277520f847406e0d44c980897c14  R243 note
68caee16ceebc6400829dc3ed8a0ac2aa33f528aa54c8263e085ab47c7ef6e24  R187 note
135b72655d948d5035b21eaddce9fbeb0260c49bc3093e4bf2df73b03d88c4a1  candidate_scheme.rs
90665143f127394316b950d039fc498d460ac680df20b2387911a2fbdcaaeee1  candidate_context.rs
45324aaec3825b1bf5cb15811ce309b8ff2dc020d5882383c0ed33d9d0b779f8  candidate_effect.rs
90ed01915688b9c13c95593ddce296e7e3702a623e23dd4b9255d718b380a599  candidate_source.rs
5185481127cb619d66d49025c0a20ee7d829bc1e7a46072a05adecf4d22aa891  candidate_extrusion.rs
ea5c141b31db8309908b4ee1e5c5465db0a2bfdc39551c372b8124ed633e9e84  candidate_call.rs
7ba8d2a38487e5ad204fc6b19a3aa5a6f4984ee03249a9fc2210ee01993594ae  candidate_value_graph.rs
50ad99c3afabb12816e9ec17fe50372bac758964699519d9ce6f1fc1f6649599  shadow_apply.rs
ca7b2fd842ae8ccac3cc22d572b75221ab011725f9cd2dcbfd19e03e4b8b6b3a  local_source_observation.rs
```
