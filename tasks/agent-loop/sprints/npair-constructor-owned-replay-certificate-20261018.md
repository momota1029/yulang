# Sprint `npair-constructor-owned-replay-certificate-20261018`

Status: CANDIDATE pending Luna's fresh author receipts. Branch `research/simple-sub-intrusion`; baseline `7087de449`. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN. Preserve original quantifiers, source domain, fixed-c, F1/FK1, N-Transport, Call, soundness, principality, termination, and production boundaries. Astra0; no rollover.

## Fixed outcome

For both actual same-source FreshUse routes, authenticate a constructor-owned chain of evidence through captured source, imported snapshot, FreshUse admission and concrete physical fiber, exact Replay constructor and fibers, actual Function consumer C and all four port admissions. Require explicit identities for `p`, copied `p1`, Replay upper `h`, Replay child `q`, and consumer `C`. Never infer a path from matching metadata or incoming-edge counts.

Before source edits, produce and independently review this owner map. Numeric coordinates stay `NOT OBSERVED` until the exact fixture runs.

| Evidence | Primary owner | Required relation |
|---|---|---|
| Captured source | `Capture::bound` in candidate scheme | source relation, complete BoundKey, captured snapshot |
| FreshUse transport | prepare/restore path | imported antecedent, mapped relation `p1`, term/scope/input maps, actual Transport child |
| Physical output | `candidate_extrusion.rs:446–599` (read-only) | admission→emission→row/lane/index and value physically stored there |
| Restored fiber | `candidate_context::bound_relations` | complete destination BoundKey and relation membership |
| Replay | `candidate_context_begin_replay` and recipe registry | exact lower/upper/child, both input fibers, retained recipe |
| Consumer | `candidate_function_port_admit` | actual C, field, typed endpoint, operation, child scope/transformer |

First decide from actual constructors whether p1→h exists or p1=h by relation identity. FreshUse and Replay may independently contribute to one shared q; do not force them into a single incoming ancestry spine. If no p1→h path is retained, state that exact gap and derive a constructor certificate for the shared conclusion before implementing a replacement. Root/term equality never substitutes for relation identity.

## Lanes, leases and budget

**Proof — Sol/prover, 720s.** Write only:
- `notes/theory/2026-10-18-constructor-owned-replay-certificate.md`
- `tasks/agent-loop/inbox/20261018-constructor-owned-replay-proof.md`

Use the previous CLEAN conditional proof and frozen review as inputs, then map every equation to the actual constructor owners above. Establish the shared-conclusion/FreshUse/Replay topology or identify the first absent owner record. State exact fixture coordinates as unobserved until runtime. No parent theorem closure unless the exact original obligation is proved.

**Implementation — Luna/implementer, 1920s including 360s protected runtime; authoring cap 1560s.** Write only:
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/tests/candidate_graph_call.rs`
- `crates/yu-solver/examples/research_scoped_formal_replay.rs`
- `notes/progress/2026-10-18-constructor-owned-replay-certificate.md`
- `tasks/agent-loop/inbox/20261018-constructor-owned-replay-impl.md`

Source-owner mapping and its early independent review must be CLEAN before writing checker code. Then use explicit constructor references; authenticate the physical slot's actual index content and full bound membership; verify all four port-child scoped flows and identity/stamp_input/protect_body equations; add separate actual-record mutations for snapshot, slot content, fiber membership, dependency kind, endpoint, and flow. Preserve solver semantics. No new storage unless checked accounting, rollback, and review are in scope.

**Independent reviews, 600s:** source-owner map review 120s before code; final frozen proof/compiler delta review 480s after author STOP. Reviewers are fresh and do not edit. **Primary integration 120s; reserve 240s.** Total cap 3600s: proof720 + implementation1920 + review600 + primary120 + reserve240. No rollover.

## Exact runtime commands

Only after the frozen proof and implementation receive CLEAN reviews, run once, sequentially, with each timeout <=120s and full primary-owned stdout/stderr/exit metadata:

1. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate authentic_demand_capture_tests --lib`
2. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_graph_call --lib`
3. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo run --offline -p yu-solver --features shadow-apply-candidate --example research_scoped_formal_replay`

Logs: `tasks/agent-loop/runtime/20261018-replay-fiber-consumer.{helpers,graph,example}.{stdout,stderr}.log` and `.meta.json`. No retry after failure.

## Dependencies and stop conditions

- Previous conditional proof CLEAN: `notes/theory/2026-10-18-replay-fiber-consumer-certificate.md`, SHA `691a537b441bff0947b47886f423199e9558740778d81e50858eedd85e3e3614`.
- Previous compiler review BLOCKING/MAJOR findings: `notes/progress/2026-10-18-replay-fiber-consumer-closeout.md`.
- Unapproved candidate snapshot: commit `1958cf20e`, review/state checkpoint `7087de449`; exact frozen path hashes are in `tasks/agent-loop/inbox/20261018-replay-fiber-consumer-impl.md`.
- PR #11 policy merge: `27a7e00d4b581f18987bb2a3cbf2e492789c2293`; no authority or semantics changed.

Stop if owner mapping cannot distinguish relation identities, physical fiber data is unavailable, shared conclusion proof is unsound, pins drift, a negative authenticates, a command fails, or budget is uncertain. Candidate passes and conditional proofs do not close parent conditions.
