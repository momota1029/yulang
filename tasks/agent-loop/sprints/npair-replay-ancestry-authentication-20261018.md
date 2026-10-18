# Sprint `npair-replay-ancestry-authentication-20261018`

Status: CANDIDATE until Luna records fresh author receipts. Branch
`research/simple-sub-intrusion`; baseline `f423047fa`. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; preserve every
original quantifier, source domain, fixed-c requirement and independent F1/FK1.
Astra0. No old sprint time rolls forward.

## Fixed outcome

Authenticate one exact demand-bearing typed Replay row from the original native
source demand through its exact retained FreshUse route and typed dependency
ancestry to the current Replay upper/root and all four consumed Function ports.
Use real child/lower/upper relation IDs and BoundKeys, the actual
`Dependency::Transport` FreshUse witness, any intervening supported
`Derived`/`Transport` root rewrite, and ordered `FunctionPort` dependencies.
A matching demand tuple, endpoint pair or shape is only a search hint and is
never sufficient authentication. Unrelated captured relations, sibling uses,
substituted roots/BoundKeys/ports, missing edges and unknown edge kinds must
reject authentication. Preserve the prior `native_root_matches=false` field.

Correct the pairwise-swap test so it checks that all-port authentication fails
(and the two swapped positions differ while untouched positions match). Include
`authentic_demand_capture_tests` in an exact authorized command. The same-source
two-use regression must prove distinct route/use identity and integer lower
propagation to both results. Keep all source admission, constraints, solver,
root transport, scope and consumer behavior unchanged. This is observational
evidence, not original `At(D,c,delta)` or theorem closure.

Success: fresh independent proof/compiler reviews are CLEAN; all three exact
commands below run once and exit 0; captured rows show the actual source demand,
FreshUse map and witness, replay dependency ancestry, current upper/root,
ordered four ports, two distinct uses, both integer results, and raw mismatch
still false. If the actual fixture lacks a path, record the exact first missing
edge; do not manufacture one or claim compiler unsoundness.

Original conditions closed before/after: **0 unless a reviewed derivation is
applied to an exact original obligation**. Preserve original fixed-c formation,
R/W/Z/domain, consumer, F1/FK1, N-Transport, Call, soundness, principality,
termination and production gates.

## Frozen dependencies

| Input | SHA-256 / locator |
|---|---|
| Previous closeout | commit `f423047fa` |
| Previous closeout note | `notes/progress/2026-10-18-demand-root-transport-closeout.md`, `4a7cb704d807e020acb0edb10a50e19fe26846f7b7e6b041d7e93b3ceb52d66f` |
| Conditional proof | `notes/theory/2026-10-18-demand-root-transport-correspondence.md`, `426b1bf969eb9628b73f5bcddec38b2f169d41341479dda4019965b34fad1244` |
| Prior implementation review blockers | same closeout note above; exact source snapshot in prior commit |
| `candidate_context.rs` | `46f0b74c8aa942c629a456272c3ae601827f1794b25d7034479edee62bc13e4f` |
| `candidate_scheme.rs` candidate | `c1a5619633826ffd266b9dbe61c8a3b8d66b22fe708982c622d048ae457f1d30` |
| `shadow_apply.rs` candidate | `bbece5f6afd328df5829d507210cdcba7384bacf48603727a408bf674bcbdeef` |
| `candidate_graph_call.rs` candidate | `3b615f324e25d1a65fd8b4f886b6e882ec4551020ddf46242a479b65d3064b7f` |
| `research_scoped_formal_replay.rs` candidate | `0c813c194147fd1ef552a0047d9d80a91374261c004936adc320575352c1bf66` |
| Prior progress/handoff | `notes/progress/2026-10-18-demand-root-transport.md` SHA `10d7e60322aba054ff286dd664c670085b1eb430925ceef1adddb313d2493c3c`; inbox SHA `4e3c241bedbaf8beadb56466ece808014ffbdc37744fc569b958748f40473332` |

## Lanes, exact leases and resources

**Proof — Sol/prover, 420s.** Reuse the CLEAN conditional constructor theorem;
write only:
- `notes/theory/2026-10-18-replay-ancestry-authentication.md`
- `tasks/agent-loop/inbox/20261018-replay-ancestry-proof.md`

Turn the theorem's exact side conditions into an executable ancestry criterion.
Name the source relation/snapshot, FreshUse route, copied map, restored BoundKeys,
Transport witness, allowed rewrite edges and root updates, exact Replay child
and upper fiber, and the four ordered FunctionPort edges. State how cycles,
multiple incoming edges, duplicate tuples and unsupported dependencies fail
closed. Apply only to the fixture and local P3/P4 route; parent closure stays 0.
No new semantics or proof-by-shape.

**Implementation — Luna/implementer, 1080s total including 360s protected
runtime; code authoring max720s.** Write only:
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/tests/candidate_graph_call.rs`
- `crates/yu-solver/examples/research_scoped_formal_replay.rs`
- `notes/progress/2026-10-18-replay-ancestry-authentication.md`
- `tasks/agent-loop/inbox/20261018-replay-ancestry-impl.md`

Build the observer from exact Replay coordinates/dependencies, then authenticate
the map/witness chain and all four actually consumed ports. No solver-semantic
changes. Correct and exercise the previously omitted swap helper. Include
negative cases for matching-but-unrelated relation metadata, wrong source
snapshot, sibling use, wrong root, BoundKey substitution, missing/substituted
ancestry edge, unsupported edge, and every pairwise port swap. Assert integer
lower propagation to both sibling-use results. Preserve raw mismatch. No global
or unbounded storage; if state is needed, use checked arithmetic, fallible
reservation, rollback/atomic failure, explicit accounting and include this in
review. Stop code edits at 720s, leaving 360s for the commands below.

**Primary runtime — exact commands once each, sequentially, only after clean
reviews and a fresh capacity check.** Each timeout <=120s; capture complete
command/stdout/stderr/exit into the named primary-owned files:

1. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate authentic_demand_capture_tests --lib`
2. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_graph_call --lib`
3. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo run --offline -p yu-solver --features shadow-apply-candidate --example research_scoped_formal_replay`

Use separate `tasks/agent-loop/runtime/20261018-replay-ancestry.{meta.json,helper.stdout.log,helper.stderr.log,test.stdout.log,test.stderr.log,example.stdout.log,example.stderr.log}`. No retry after any failure or falsifier.

**Fresh independent reviews:** proof/spec review 180s; compiler review 360s. Review
frozen bytes and direct pins, then all captured rows/commands without rerunning.
Check exact relation/dependency ancestry, supported edge semantics, duplicate
and sibling isolation, current upper/root, four real port consumers, negative
falsifiers, memory/noninterference, and complete evidence. Authors cannot review
their own work.

Total 2400s: proof420 + implementation1080 (code720/runtime360) + reviews540
+ Luna integration120 + reserve240. At code freeze protect at least 1020s for
reviews540 + runtime360 + integration120. Astra0; no rollover. Commit/push
material frozen milestones under Luna ownership.

## Stop and closeout

Stop on an unrelated tuple authenticating, any missing/ambiguous dependency,
source/native mismatch, semantic change requirement, pin mismatch, command
failure, runtime falsifier, budget boundary or writer cessation uncertainty.
Do not call diagnostic transport NPAIR evidence. A passing fixture proves only
the exact authenticated route. Close with original parent closure count, actual
runtime behavior, review findings, and the single next missing original premise.
