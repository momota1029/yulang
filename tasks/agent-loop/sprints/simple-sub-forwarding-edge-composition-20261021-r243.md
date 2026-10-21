# Sprint R243 — Forwarding-edge composition

Status: ACTIVE_PROOF_SOURCE_AUDIT; Luna sole primary. No child workers.
Baseline: `7fda14d74` (`research/simple-sub-intrusion`), after R242 partial freeze.

## Fixed parent and outcome

Parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7, SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`. Preserve the shared assignment, original formals, arbitrary finite chain length, repeated calls, simultaneous entries and finite-prefix quantifiers.

Starting from R242's direct-terminal base, trace one actual forwarding body `R_next t` through its source Name, the body's actual Apply, and the next provider's own source-parametrized Function. Identify distinct authentic per-use correspondences `mu_i` and `mu_{i+1}`; show how the mapped formal-Name effect enters that body's actual argument effect, how the body's application effect reaches the enclosing provider's mapped RE, and how the next comparison uses its own provider map and admitted bounds. Keep Local capture, shared anchors and same-SCC internal live-root routes separate. Attempt the arbitrary finite-chain composition only while every edge retains these exact source/use identities. A one-edge result is not the induction or whole parent theorem.

## Proof method and falsifiers

Use R242 for the direct-terminal source bounds, R239 for conditional mapped-bound restoration, R240 for source/capture ordering and R241 for the actual Apply and live-root joins. Follow the source `Apply` record and source Name owner to the exact `ApplySourceInput`, every generated typed constraint, every capture/shared anchor, both per-use maps and each physical admission/readback. Compose only maps with the same original provider/formal and their actual forwarding-use occurrence; preserve the distinction between `mu_i` and `mu_{i+1}`.

R187's bridge/relay input is a discriminator for mixed-age intermediate Apply-effect rows, not an established counterexample. Trace whether each required intermediate edge is captured under the current source and relation owners or remains a valid shared anchor. Do not infer capture from logical connectivity alone.

Falsify the proposed edge if a required intermediate edge is absent from both the exact provider instance and licensed shared anchors; if the body Apply or its actual argument belongs to another source use; if a copied endpoint is substituted for its original without the map; or if the next comparison does not use the next provider's own map. Preserve all parent quantifiers. Keep replay-use-antecedent, source/native and R71/R72 gaps explicit.

Success is a constructor-derived forwarding-edge composition with separate authentic maps and exact Apply joins, plus the first proved induction step if available; otherwise freeze the first exact missing source-to-use transition and its falsifier. Do not claim parent closure from one edge or a finite candidate model.

## Lanes, leases and limit

Serial Luna proof/source audit; no children or Astra. Read-only: no code, tests, builds or samples. `NO_SAFE_CODE_SLICE`; no production or semantic authority. Fresh independent review is required for promotion. Resource cap 900 seconds, no carryover. Unknown legacy leases remain quarantined. Freeze on a substantive edge result/falsifier, material blocker/dependency/lease change, or budget boundary.

Exact write leases:
- `tasks/agent-loop/sprints/simple-sub-forwarding-edge-composition-20261021-r243.md`
- `notes/theory/2026-10-21-r243-forwarding-edge-composition.md`
- `tasks/agent-loop/current.json`

## Direct dependency pins

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
d25c3d352237560d2e02a5be33f14e80c3f21ae1dea287965cd436ab16264401  tasks/agent-loop/sprints/simple-sub-direct-name-instance-closure-20261021-r242.md
c5af54d3f4ad03072f8eee862310113555452c6af3d0a369197fda70c6df9fe6  notes/theory/2026-10-21-r242-direct-name-instance-closure.md
8ecb68feb9177a78af6f5cfb47faa161081ee13bf27376c490c52caf96a9769f  notes/theory/2026-10-21-r239-parent-instance-admission.md
11c53272e36569c0d58c3292c89a97866b8316bac8601304e2206ff6378fb959  notes/theory/2026-10-21-r240-source-instance-correspondence.md
2796242a5c1cd0917716695d7fc18359ca964b232c7c9df71a43a5821c554704  notes/theory/2026-10-21-r241-live-root-apply-correspondence.md
135b72655d948d5035b21eaddce9fbeb0260c49bc3093e4bf2df73b03d88c4a1  crates/yu-solver/src/candidate_scheme.rs
90ed01915688b9c13c95593ddce296e7e3702a623e23dd4b9255d718b380a599  crates/yu-solver/src/candidate_source.rs
7ba8d2a38487e5ad204fc6b19a3aa5a6f4984ee03249a9fc2210ee01993594ae  crates/yu-solver/src/candidate_value_graph.rs
90665143f127394316b950d039fc498d460ac680df20b2387911a2fbdcaaeee1  crates/yu-solver/src/candidate_context.rs
5185481127cb619d66d49025c0a20ee7d829bc1e7a46072a05adecf4d22aa891  crates/yu-solver/src/candidate_extrusion.rs
45324aaec3825b1bf5cb15811ce309b8ff2dc020d5882383c0ed33d9d0b779f8  crates/yu-solver/src/candidate_effect.rs
285a39449360b050d7689f9e52f400b821e651ec9ce300bd14a1a3d9a9ab8b64  crates/yu-solver/src/lib.rs
50ad99c3afabb12816e9ec17fe50372bac758964699519d9ce6f1fc1f6649599  crates/yu-solver/src/shadow_apply.rs
ea5c141b31db8309908b4ee1e5c5465db0a2bfdc39551c372b8124ed633e9e84  crates/yu-solver/src/candidate_call.rs
```
