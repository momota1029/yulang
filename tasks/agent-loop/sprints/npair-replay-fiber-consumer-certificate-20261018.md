# Sprint `npair-replay-fiber-consumer-certificate-20261018`

Status: CANDIDATE until Luna records fresh author receipts. Branch
`research/simple-sub-intrusion`; baseline `f56022c19`. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN. Preserve all
original quantifiers, accepted source domain, same fixed-c requirement,
independent F1/FK1 and all call/soundness/principality/termination gates.
Astra0. No prior budget rolls forward.

## Fixed outcome

For the same accepted source and two distinct FreshUse instances, construct and
verify a concrete certificate for each actual route:

```
source p → copied bound p1 → Replay upper h → Replay child q
            separate FreshUse spine       → Function consumer C → four ports
```

`p1→h` and `q→C` are separate spines. Distinct source, copied bound, Replay
upper, Replay child and consumer identities must be retained; if an edge has
zero steps, check that identity/equality directly. Fix the actual Replay row
first; never search by a tuple and attach a convenient route afterward.

Authenticate the captured `BoundEvidence` snapshot, imported antecedent,
source bound, restored destination fiber and retained Replay recipe for the
same bound. Check the FreshUse witness and all scoped-flow equations
(call/use/scope/input, zero or explicitly supported transformer, root). At C,
check both whole Function typed pairs, four ordered child endpoint pairs,
operation and field identity, demand consumption, and exact identity,
`stamp_input`, `protect_body` transformers. The two source and copied maps must
be distinct where the fixture owns them. Unknown/ambiguous evidence rejects.

Negative tests must independently alter real captured snapshot, dependency
kind, bound/fiber membership, port endpoint, and scoped flow, and observe
rejection. A changed call/use ID or tuple alone is not a snapshot/edge
falsifier. Reuse the corrected swap test, helper-filter command and integer
propagation checks when valid. Keep `native_root_matches=false` visible. This
is a diagnostic/source-native certificate, not semantic `At(D,c,delta)` and
not original theorem closure.

Success: both unmodified fixture certificates authenticate; each targeted
evidence alteration fails for its reason; all four actual consumer ports
match; both integer results receive their lower; three exact commands pass
once after clean independent reviews. If retained sources cannot establish one
premise, record its source owner and exact missing evidence; do not authenticate
by shape or alter solver meaning.

Original conditions closed before/after: **0 unless a reviewed proof applies
to an exact original obligation**. Original fixed-c formation, R/W/Z/domain,
consumer reflection, F1/FK1, N-Transport, Call, soundness, principality,
termination and production remain open.

## Frozen dependencies

| Input | SHA-256 / locator |
|---|---|
| Prior closeout | commit `f56022c19` |
| Prior closeout receipt | `notes/progress/2026-10-18-replay-ancestry-closeout.md`, SHA `0f3a4a8da1af5a557a1fc4eef2e50907c08418fb07ec62bd6b5fd065a1f4c667` |
| CLEAN conditional proof | `notes/theory/2026-10-18-replay-ancestry-authentication.md`, SHA `00603a98b9f66eb71c61c0fe80e8812ff059c6cde54abd2d91e02036674381f6` |
| CLEAN proof review + compiler blockers | previous closeout receipt above |
| `candidate_context.rs` prior candidate | `cde5c7368a038d77793d2d8b07e0beb400c33b83d4dd0cd689076d641ee788fb` |
| `candidate_scheme.rs` prior candidate | `1b5da9c8b34a53db04875294e03b5d03997abd78fc43145cce0742ad4a72ef03` |
| `shadow_apply.rs` prior candidate | `683928cc71f828b3536950911b8d20d5c141415300555c2271d4b790ac8d7e65` |
| `candidate_graph_call.rs` prior candidate | `01dbaef3b6d6b8f7a943fe627b64ad7fa7822e5ea7f04437b9ef390f4e8eec7e` |
| example prior candidate | `e4c1bec2a41accfe09f664d5992b2575ce78b855c3ff622f08eeb6de8765e3d3` |
| `candidate_context.rs` earlier constructor source | `46f0b74c8aa942c629a456272c3ae601827f1794b25d7034479edee62bc13e4f` |

## Lanes, leases and resources

**Proof — Sol/prover, 900s.** Write only:
- `notes/theory/2026-10-18-replay-fiber-consumer-certificate.md`
- `tasks/agent-loop/inbox/20261018-replay-fiber-consumer-proof.md`

Map the CLEAN proof's exact constructors to current source owners and APIs.
Produce an evidence table for both fixture uses with actual source p, captured
snapshot/bound, copied p1, FreshUse witness/map, h, q, C, and all four typed
ports. Prove the two spines separately, including zero-step cases. Show why
snapshot import, restored fiber, replay recipe, root/scope/flow, endpoints and
consumer transformers correspond. State exactly where current source fails to
supply evidence; do not replace missing facts with assumptions. Apply only to
this local P3/P4 route, not same-c or universal P3/P4.

**Implementation — Luna/implementer, 1800s total including 360s protected
runtime; code authoring max1440s.** Write only:
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/tests/candidate_graph_call.rs`
- `crates/yu-solver/examples/research_scoped_formal_replay.rs`
- `notes/progress/2026-10-18-replay-fiber-consumer-certificate.md`
- `tasks/agent-loop/inbox/20261018-replay-fiber-consumer-impl.md`

Implement the smallest verifier for the explicit fixture certificate, using
existing retained evidence. Do not build an open-ended generic ancestry search.
Return unauthenticated when any required evidence is unavailable. No changes to
constraint generation, propagation, solver behavior, scope/root semantics or
consumer policy. Negative tests must mutate actual evidence independently, not
just fields used to select a row. Preserve dual integer propagation, distinct
sibling uses, and the raw mismatch. Any new retained storage requires checked
arithmetic, fallible reserve, atomic rollback/failure, complete accounting and
review coverage.

Stop code authoring by 1440s, leaving 360s for the commands below. At code
freeze, at least 1380s remain for review840 + runtime360 + primary integration
180; the additional reserve480 is untouched.

**Primary runtime — run each exact command once, sequentially, only after both
fresh reviews are CLEAN and capacity is remeasured. Timeout <=120s each; save
full command/stdout/stderr/exit in primary-owned logs. No retry after failure.

1. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate authentic_demand_capture_tests --lib`
2. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_graph_call --lib`
3. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo run --offline -p yu-solver --features shadow-apply-candidate --example research_scoped_formal_replay`

Use `tasks/agent-loop/runtime/20261018-replay-fiber-consumer.meta.json` and
`tasks/agent-loop/runtime/20261018-replay-fiber-consumer.{helpers,graph,example}.{stdout,stderr}.log`.

**Fresh independent reviews:** proof/spec 240s and compiler 600s. Review frozen
proof, implementation, direct pins, all three captured commands, positive
certificates and actual evidence mutation failures. Check both spines, exact
snapshot/fiber/import, whole pairs, child endpoints, operations, fields,
consumed demand, scope transformers, sibling identity, allocation and unchanged
solver semantics. Authors cannot review their own output.

Total cap 4200s: proof900 + implementation1800 (code1440/runtime360) + reviews840
+ Luna integration180 + reserve480. No rollover. Astra0. Only Luna integrates,
commits and pushes at material milestones.

## Stop and closeout

Stop if a normal route cannot be authenticated from retained evidence, a
falsifier authenticates, snapshot/fiber identities conflict, any port's true
endpoint/transformer is unavailable, source/native behavior disagrees, semantic
change is needed, pins drift, a command fails, or budget/cessation is uncertain.
Do not infer compiler unsoundness or theorem closure from a diagnostic
certificate. Report parent closure, exact runtime behavior, review status and
the next one missing original premise.
