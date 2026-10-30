# R51 Rust native-publication observation — frozen revision 2

Assignment `/root/r49_rust`, exact B1 repair lease. R51 contract SHA-256:
`1cdaa9c5b6becf635e0bd859c7739d8122468fb92a688662ae6b78462803ae37`.
Independent review finding: BLOCKING B1 at
`tasks/agent-loop/inbox/effect-permission-native-publication-r51-review.md`.
Review SHA-256: `d1777a111d45d3dc2e8adf762194312cc29db795f3ac060114b78eb864633aee`.
Pre-repair source pin: `e6d26028928fa6cfb77ece862f45a6391d813e5141ffe797d706ec2a44565d53`.
Revision 2 makes all added publication-observation preparation best-effort;
revision 1 is retained verbatim below this repair receipt (archived byte hash
`d0290a56f069856f6b5fc2288940a0f0b08c189423bd130d39ae35c2f2ed32d9`).

`complete_residual_plan` still owns the R50 authenticated decision behavior.
After it succeeds, `prepare_native_publication` returns an `Option`; snapshot
reserve failure, missing result row, or unavailable/ambiguous slot or emission
metadata selects no private observation and never reaches `?` in the solver
result path. Successful Forward calls still use the exact decision endpoint,
`pending.upper`, fact occurrence, and cause. Post-publication capture remains
best-effort and can also return unavailable. The pre-existing R50 decision
plan and outcomes reservations retain their prior behavior. This is an author
repair frozen for fresh independent delta review; B1 is not adjudicated closed
by this handoff.

Requested model/effort: implementation lane Luna/high. Observed model, effort,
runtime and active-time telemetry: UNKNOWN. No descendants. No builds, tests,
Cargo, Lake, formatter, Git, runtime checks, scratch, cache, target, worktree,
environment, or nested CLI were used. Source inspection/static reasoning only.

Frozen revision 2 hashes:

- `crates/yu-solver/src/candidate_receiver.rs`: `41272bf276761cdfe847264b4aaf0093d9feab361ca8d80881fd69ca86d449e0`
- `tasks/agent-loop/inbox/effect-permission-native-publication-r51-rust.md`:
  supplied with the frozen message receipt to avoid self-reference.
- `crates/yu-solver/src/candidate_context.rs` was read-only for this repair and
  remains at `c26a152e957980fcc844b7ff7145f712c4fd218b03415c50263e3dd81156c71f`.

Source correspondence remains provisional and all source execution,
extraction-completeness, original A/B, and production gates remain OPEN.
Worker state: WRITES STOPPED after the revision 2 freeze. Only the two exact
repair paths were written; no generated outputs or descendants.

---

# R51 Rust native-publication observation — frozen revision 1

Sprint-ID: `EFFECT-PERMISSION-NATIVE-PUBLICATION` / R51.
Contract SHA-256: `1cdaa9c5b6becf635e0bd859c7739d8122468fb92a688662ae6b78462803ae37`.
Admission SHA-256: `fcd73b0172421b2906eca89828db16252bc2456bbcca2a25160e263864b1057d`.
Assignment: `/root/r49_rust`, Rust lane, handoff revision 1.
Parent-supplied baseline HEAD: `5531aaf43b9584b654116a47ea53251f6d74dbc0`, branch `yulang3`; no Git command was run.
Requested role/model/effort: implementation lane, Luna/high. Observed model, effort, session identity, launch/runtime telemetry and active seconds: UNKNOWN. No descendants observed.

## Outcome and behavior

Outcome class: bounded provisional source/native evidence instrumentation.

The existing R50 consumer still completes the whole immutable `CompleteResidualPlan` before its first `constrain_live_effect`. It owns the complete prepublication lower-row and lower-atom vectors for the result row. Each Forward row retains the exact result-row lower `BoundKey`, physical lower slot/index, prepublication presence bit, prior slot-emission count, and emission-vector frontier. Planned append indices account for earlier absent Forward rows in the same physical lane. Suppress rows have no forwarding plan and remain governed by the existing R45/R47/R48 same-witness path. The source operation classification and Catch-arm evidence are unchanged.

After successful residual calls, a private optional observation is captured. It first checks exact frame preservation: the original lower-row and lower-atom vectors remain unchanged prefixes, and the suffixes equal the planned absent Forward endpoints in plan order, with no unexplained result-row append. A Forward observation retains the exact original endpoint, `pending.upper`, fact occurrence and cause; a unique `SourceDrainReceipt` tied to that occurrence/task/cause and its origin/selected relation; and one of:

- `AlreadyPresent`: the exact result-row physical lower slot remains present and unique, and the retained emission count for that slot did not change. Zero prior emissions is accepted. Any single retained prior emission must have matching slot/readback and a matching bound admission/relation pair; it is not attributed to this publication decision. This reports a pre-existing bound with no new emission attributed to this decision.
- `NewlyEmitted`: the exact physical slot is present and unique, exactly one matching slot emission exists past the captured emission frontier, its recorded constructor readback names that exact slot and bound, its admission/relation pair matches the bound, and the relation is descended from the forwarding source-drain relation.
- `Unavailable`: represented by absence of the private observation vector when required identity, source-drain completion, physical bound, emission/admission, relation, ancestry, or query allocation is absent, ambiguous, or inconsistent.

The plan records the anticipated slot before publication. Post-publication capture performs no solver mutation. Failure to allocate the completion ledger is already tolerated by `record_source_drain_completion`; the added private query then returns unavailable and does not convert that observation loss into a solver error. Observation-vector reservation failure likewise leaves the query unavailable after successful ordinary candidate publication.

Suppression continues to mean only that this consumer issued no forwarding call for that selected endpoint. It does not establish global absence. Pre-existing contributions and other same-family endpoints are not removed by this instrumentation.

## Source correspondence and limits

Read-only producer inspection of `lib.rs` found the existing typed-drain start/completion path. The producer retains the source receipt on the owning origin and silently omits only the completion-ledger event if `try_reserve` fails. No `lib.rs` change was needed or made.

The new query checks the retained origin's exact occurrence and typed task pair, receipt origin/seed/selected relation, task and cause, cause occurrence, and completion-ledger membership. For newly emitted results it also checks the live result-row slot, retained emission and admission, typed bound relation, and current dependency ancestry. For pre-existing results it checks current exact physical slot uniqueness and that the exact-slot emission set has not grown since the prepass; it does not relabel an old emission as caused by this decision.

Not established: source extraction completeness; exact fidelity of all candidate terminal extraction/canonicalization; successful concrete Rust execution; completeness of every native bound/emission producer; causal ownership of a pre-existing bound by the current Forward call; replay/rollback behavior beyond the inspected retained state; runtime allocation-failure exercise; Catch execution semantics; full subtraction or hygiene; original A/B, whole-solver soundness, principality, termination, production authority, or any global endpoint-absence claim. The constructor readback records `ConstructorAfterAppend`; the query separately rereads current physical membership, but neither creates an independent execution trace.

## Inputs and results

Frozen pins verified before writing:

| Input | SHA-256 |
|---|---|
| `candidate_receiver.rs` baseline | `88b833dacc1bce6e444ec1da2fb47a87475384473384cd4e0b1b5c3089d8f4c3` |
| `candidate_context.rs` baseline | `1ba38a85e8575b1d6d3cf50d918a3603c4e23068cb730d1c3645e605148636bc` |
| `lib.rs` read-only producer baseline | `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4` |
| R50 Lean model | `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2` |
| R50 review | `563d2b67ea0bb79b2d10d857a1613fbdd5ec779f55170d14cb638c0a9135df6e` |
| R50 outcome | `e2a50b43f3b63b85634516cd97b05ee060a45b02cdebcb29e21949e36570ac71` |

Changed leased source artifacts:

| Artifact | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_receiver.rs` | `e6d26028928fa6cfb77ece862f45a6391d813e5141ffe797d706ec2a44565d53` |
| `crates/yu-solver/src/candidate_context.rs` | `c26a152e957980fcc844b7ff7145f712c4fd218b03415c50263e3dd81156c71f` |

The handoff's own SHA-256 is supplied with the frozen message receipt to avoid
self-referential bytes.

Checks performed: frozen byte-hash verification; read-only inspection of the exact R51 contract/admission, governing sprint rules/README/design, leased Rust owners, and relevant `lib.rs` drain/forwarding producers; source-only consistency inspection after editing. No compiler, test, Cargo, Lake, formatter, Git, or runtime check was run, as required by the contract. No performance telemetry is available. No disposable scratch path or generated artifact was created.

Unresolved premise and owner: Lean/proof and independent review lanes must determine whether their bounded model includes the exact pre-existing/new-emission distinction and unavailable-on-missing-observation behavior represented here. Parent/source owners still owe extraction and execution correspondence. This result changes no production permission and leaves original A/B OPEN.

Next related in-envelope step: send these frozen observation fields and falsifiers to the R51 Lean author and primary for comparison against the R51 model/review; no source-owner expansion is requested here.

Worker state: WRITES STOPPED. Exact leased writes: `crates/yu-solver/src/candidate_receiver.rs`, `crates/yu-solver/src/candidate_context.rs`, and this handoff only. No descendants or generated outputs. Review/integration pending; not commit-ready or production evidence.
