# R78 admission — checked source alignment into existing consumers

Sprint: `EFFECT-PERMISSION-INTEGRATED-ALIGNMENT/20261031-R78`  
Decision owner: Luna primary  
Authority: standing continuation authority for the user's ongoing Yulang soundness goal, as recorded in root `AGENTS.md`; selector recommendation after R77 closeout.

## Frozen packet

- Contract: `tasks/agent-loop/sprints/effect-permission-integrated-alignment-20261031-r78.md`
- Contract SHA-256: `42455496150e76635d364fb72d20142583d30ac0cedec239d17520609be95148`
- Input manifest: `tasks/agent-loop/sprints/effect-permission-integrated-alignment-20261031-r78-inputs-r1.json`
- Input manifest SHA-256: `66c5307d5c796765a6557784d30935554fcc4d4ebf444dd8cc3983f980a81803`
- Baseline commit: `68976bad8d44fd5586ac9b06ee2389743bfa4c8f`
- Baseline receiver SHA-256: `9113485e919f41581049a065bef5a533505fc46e71e5d3ae18a4ceec97cdaca7`
- R77 accepted source-alignment module SHA-256: `0aa1185675cc92ac97a20f4163bd2b2486f34cfb5ca725a3fcb3c1861efdf682`
- R77 independent review SHA-256: `913a4f7bef50e6c7a0513615cf9b01bd471f5bf2850bca35709eafeb30aabe8d`

## Exact assignments

| Assignment | Role | Exact write paths | Budget |
|---|---|---|---:|
| R78-RUST | implementer | `crates/yu-solver/src/candidate_receiver.rs`; `tasks/agent-loop/inbox/effect-permission-integrated-alignment-r78-rust.md` | 900s |
| R78-PROOF | lean_prover | `notes/theory/lean/YulangClosure/IntegratedSourceAlignmentR78.lean`; `tasks/agent-loop/inbox/effect-permission-integrated-alignment-r78-proof.md` | 1000s |
| R78-REVIEW | fresh compiler_referee | `tasks/agent-loop/inbox/effect-permission-integrated-alignment-r78-review.md` | 900s |
| Luna primary | coordination, exact-input authorization, review adjudication, records and Git | central state and R78 records only | 800s (500s closeout included) |

Rust and Lean authors may work concurrently because their exact write paths are disjoint and both depend only on frozen manifest inputs. The reviewer starts only after both authors STOP. Git and shared state remain primary-only.

## Fixed gate and limits

R78 integrates the R77 Name/Apply alignment into `InventoryPackage::capture` and `internal_root_view_from`. It retains unrelated calls, exact call/input identity, receiving owner, resolved callee Name and target; it checks the Apply coordinate independently from the DefinitionUse Name coordinate. Existing slot-0/slot-2, permission, parameter, relation, ancestry, root and failure checks remain.

The proof derives both consumer coordinate equations from R77's constructed alignment, with no consumer-success premise, and preserves the three existing plan/owner/parameter conclusions. It contains distinct Name/Apply success and duplicate/foreign/wrong-target/wrong-checking/wrong-index rejection witnesses.

No language semantics or production authority changes. No Rust compiler, Cargo, tests, build, formatter, Lake, cache, target, scratch, new environment or worktree. At most two exact direct stdin audits, each <=120 seconds, separately authorized and pushed before invocation. One same-checkout team; no worker launches a nested CLI or its own sprint.

R77 terminal workers and leases, its 32 pending questions, UNKNOWN identities and quarantined paths are archived under `tasks/agent-loop/history/effect-permission-source-alignment-20261031-r77-state-archive.json`; only the resolved R77 records were compacted from current state. All 32 pending items and unrelated UNKNOWN/quarantined assignments remain intact.

Admission: READY for the primary to dispatch the two author lanes. No user decision is needed; this is the exact in-scope continuation selected after review identified the remaining consumer seam.
