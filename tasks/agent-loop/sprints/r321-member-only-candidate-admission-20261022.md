# Sprint R321 — admit exact selected member HIR into the candidate session

Status: OPEN_CONTINUATION; R321's same-session member-graph boundary is reached, while the parent Yulang2 sample and proof goal remain OPEN.
Branch/baseline commit: `41ccfe74c279828612b22e538e58f7b6494cffd2` on `research/simple-sub-intrusion`; R320 result carried in the current worktree.
Authority: unchanged user goal; inference top-level principles; R149; converted unified design and proof companion; R314 exact member-only HIR obstruction. Solo primary execution; no subagents by user instruction.

## Parent outcome and bounded success

The unchanged Types sample must reach ordinary successful inference and execution without changing its source, accepted semantics, or expected output. Its exact `(Int, Str)` receiver uniquely matches the pinned tuple `Display` implementation and satisfies the exact `Display int` and `Display str` prerequisites. R314 established that HIR can project one exact selected implementation member body, but candidate inference returns `Unsupported` for that member-only HIR before it can become a `MemberGraph`.

R321 isolates the source-to-candidate seam: admit an exact selected role-default or implementation-member HIR carrier into the same candidate inference world as its consumer, capture its `MemberGraph` with receiver/result/effect roots and source identities, and retain provenance sufficient for later FreshUse selection. `Display.say` calls `std::io::out::write`, an operation under `pub host act out`, not an ordinary public value export. The source bridge now parses that host declaration, resolves the exact operation through the public family route, and preserves its parse-owned declaration key in the selected member carrier. Candidate admission also exposed two adjacent source-to-candidate gaps: argument-bearing implementation method headers such as `our x.add y` need a retained dotted target, and infix source traversal must visit both operands. Do not resolve FieldTail by spelling, invent a synthetic owner, omit where clauses, or claim that graph capture selects a method.

Success requires the exact source member identity to survive projection, candidate collection and graph capture; unrelated direct roots stay excluded; a stale/foreign member identity and a multi-root projection remain rejected. An executable trace must show the member graph is available to the same candidate session that retained the unchanged consumer's `say` FieldTail, and that nested `show` is retained in the member graph's FreshUse layout. A test-only graph inventory or standalone member HIR is insufficient.

## Open premises and falsifiers

- Exact selected-member source owner and `SourceRoleMemberId` / `SourceImplementationMemberId` correspondence.
- Candidate collection's `Unsupported` cause for member-only HIR and the minimum owner-local change that admits the carrier.
- Same-session receiver/result/effect row mapping through capture and FreshUse.
- The original Types output and all parent theorem quantifiers remain unchanged.
- Falsify with a foreign parse/source key, duplicate member schedule, dropped receiver row, omitted nested source obligation, or HIR that admits unrelated module roots.

## Non-goals and proof boundary

This candidate packet does not select a concrete implementation, discharge where clauses, close later-bound stability, prove source/native A/B correspondence, close R149, or authorize production/cutover. Runtime and theorem gates remain OPEN. Tests establish construction only.

## Solo lanes and dependencies

Primary proof/source lane: trace the exact source member through HIR projection, candidate source planning, member schedule and graph capture; apply each invariant to the R314 FieldTail obligation. No independent worker or reviewer is launched under the user's no-subagent instruction; record this limit honestly.

Primary implementation lane: host-act source indexing, exact operation-route lowering, argument-bearing dotted member headers, infix operand traversal, and one-time operator provider execution are now integrated. Continue from same-session Types MemberGraph capture toward deferred member selection; keep the original sample fixture unchanged.

## Exact write leases and worktree baselines

| Path | SHA-256 at R321 entry |
| --- | --- |
| `crates/yu-solver/src/candidate_scheme.rs` | `651be259f6a113de2611db190a9de2ef11328d296714579aa48b3dd99968da70` |
| `crates/yu-solver/src/candidate_source.rs` | `7f79cc09832758ae44f58deed49a6594a3f94e4b6ff8b7d4c491cfbc3fe80a5a` |
| `crates/yu-solver/src/shadow_apply.rs` | `8e7bf11c499d2dad4ea5a31973fe6ea782f103d1770e248b96f1cea728869362` |
| `crates/yu-solver/src/lib.rs` | `ceaf8490e45e1fb217c4d2cccb7608837666bb82901efdf13124023abcf94845` |
| `tools/inference-playground/src/lib.rs` | `d35fba6e6db6b5529fc9107f81278a54776cc50fdece4370f2aa947e76c49cf2` |
| `crates/yu-hir/src/module.rs` | `223c37e9cdaf7fb44a617dae602b51f37011e560b6e61ed7b00d9ee4baf6a994` |
| `crates/yu-hir/src/module/local_source.rs` | `e6280947146eb272692302f571bbfb0601dc7f17aacf7eeec24bfc04b35b7e1a` |
| `crates/yu-hir/src/module/source_annotation.rs` | `2412d766811501d6658c823289fcfd0510e775ebfeb98dc51c91caa6e49e3cb0` |
| `crates/yu-hir/src/module/source_exports.rs` | `25e3a19e091ea304ee37f3ee8bc24ff77828f4610aaeed65b25a3b58f9c3dd11` |
| `crates/yu-hir/src/shadow.rs` | `ccecca0d8967eabb87cf388e0b2efe4c2bae4c5ff341050a41dd59991decf18d` |
| `crates/yu-syntax/src/statement.rs` | `87174eeecb950a43a360a6cbe257d229cecda9dd19e6a0b9b20b408ffb96a109` |
| `crates/yu-syntax/src/declaration/act_decl.rs` | `f1af95a12df81900564c83d0aad541064eb2fff21ca41259b7a943ae3ad4fd74` |
| `crates/yu-syntax/src/tests/declaration/act_decl.rs` | `9e48481361c42df7cd82a0fdf8d1c4054bcc9f7bfd804b9eef611ce259c5375a` |
| `tasks/agent-loop/current.json` | `95bce761a99b433426388972d7d18f867319eb05c9c05574388c46072222ffb3` |
| `notes/theory/2026-10-22-r320-operator-owner-scc.md` | `ff351ed77311675eefd33401e4523cf92f54d73ca29a631f8543b5aad9869b0e` |
| `tasks/agent-loop/sprints/r320-operator-owner-scc-20261022.md` | `4088147aa3ee543aa5a198a8ce188c2edccadfbd82d7aafb96f459c16d5de2dd` |

Write only the paths in this lease, this contract, and `notes/theory/2026-10-22-r321-member-only-candidate-admission.md`. Added HIR lease: `module.rs`, `module/local_source.rs`, `source_annotation.rs`, `source_exports.rs`, and `shadow.rs`; syntax lease: `declaration/act_decl.rs` and its declaration tests. The pinned host operation now has parse-owned nodes; the selected member and imported operator provider remain tied to exact source identities. No arbitrary path, short-name fallback, or spelling-based method selection is admitted. Read-only source inputs include the pinned stdlib, R149 artifacts, R303/R312/R314/R315 records, inference top-level principles, and both converted Japanese design/proof documents.

## Verification, resources and stop conditions

Cap 2400 seconds; one heavyweight Cargo process at a time. Run focused HIR/solver tests, `cargo test -p yu-playground --lib`, `python3 tools/agent_sprint.py check`, `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`, and `git diff --check`. Keep source/native and parent proof gates separate from test evidence. Commit/push coherent checkpoints when repository metadata is writable; never force-push. Stop at the bounded same-session member graph, a precise source/candidate construction obstruction, cap, or user STOP.
