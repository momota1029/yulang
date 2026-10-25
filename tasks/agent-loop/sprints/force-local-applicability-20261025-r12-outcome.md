# FORCE-LOCAL-APPLICABILITY-20261025 / r12.1 outcome

Status: **REVIEWED OUTCOME 3 — exact source-applicability obstruction**
Baseline: `44a61f3ba5a7e0ec36612de6bf022071d093f6c2`
Corrected contract: [r12.1](force-local-applicability-20261025-r12-rev1.md), SHA-256 `b2082b6aedf6d97f0a89eb467f6eab46155a4b54b0fed4fdb55a6a0ce63fab4d`
Governing Force/Flow source: `docs/yulang-operational-type-safety-ja.tex`, SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.

## Result

The unchanged parent question asks whether accepted source clauses entail the complete Force normal-leave result relation for every retained refined typed Force/Delay derivation, one consistent interpretation, each actual finite normal return, and every finite typed result suffix. The returned-thunk discriminator remains `force.result.force.effect` on the operand, distinct from `force.effect` on the returned thunk.

The frozen candidate supplies a reviewed conditional mathematical characterization:

- **T** preserves the complete typed suffix under the `force.result` prefix.
- **F** factors every route to the output through the actual old-to-output frontier under explicit fresh finite-DAG hypotheses H.
- **C** characterizes the all-endpoint/all-suffix route law exactly by frontier soundness and coverage of both the actual result and operand-result paths. This is presentation-independent at fixed interpreted endpoints.
- **R10**'s exact two-row `LOCAL-LEAVE` batch is one sufficient realization of C, not a necessary representation and not an accepted premise.
- **OLD** reduces the criterion to operand-result reachability only if the source separately authorizes reusing the old result occurrence. No such authorization was found.
- **W** records the weaker direct consequence of the accepted Force/Flow clauses: the actual Force View, a separate result transport, normal result-path metadata, fresh targets and finite-prefix form for rows actually emitted, plus restoration of the saved ambient observation packet.

Inverting the pinned clauses does not establish the actual `t,r,o` endpoint equation, universal operand-result coverage for every suffix, or exhaustive frontier soundness. This is an **unestablished source derivation**, not a proof of non-entailment, counterexample, or semantic underdetermination. No complete accepted-clause model separation was constructed. The independent reviewer found the attempted edge-deletion model correctly rejected against charter §13.

## Parent effect and remaining owners

Before: the accepted Force normal-leave applicability question was OPEN with r10's conditional two-row route cut as the only precise sufficient interface.

After: the same source question remains OPEN; the remaining premise is sharper and can be checked against other licensed constructor presentations using C.

**FL12-SOURCE-1 — Luna/source owner:** identify the accepted d/expose/Force/View normal-leave constructor for actual D,t,r,o; establish the complete typed frontier, domains/images and allocation; prove SOUND and both coverage conditions for every finite suffix while preserving packet witnesses, profile predicates, K/D/L identities and owners. Relevant source sites: 1245, 1532, 1653 and 1896. An actual source derivation of these facts falsifies this obstruction.

**FL12-NATIVE-1 — deferred and dependent:** only after the source equation is established, trace the actual operand/result/output correspondence through formation (`machine.rs` 1189–1198; `receiving.rs::delay` 208–223) to `RootCompReturn` (1087–1095). Native `ReceivedValue` reuse alone does not establish OLD or source applicability. `NO_SAFE_CODE_SLICE` remains; this sprint grants no compiler edit.

The abstract r11 `FocusResult ↔ CountedRun` theorem was **not applied** to actual Yulang source behavior. Its source premises remain absent. N1, O-NORM, O-RESULT, source/native correspondence, F1/FK1, and the original semantics/type-inference parent remain OPEN.

## Frozen evidence and review

| Evidence | SHA-256 | Status |
|---|---|---|
| Research artifact `notes/theory/2026-10-25-force-local-applicability.md` | `41db962d48fc1b2ac177fc4ad146ab4cb868076698963419fc941051566f308d` | Frozen author revision 1 |
| Handoff `tasks/agent-loop/inbox/20261025-force-local-applicability.md` | `7dd45db9dc6c521ac78223e20204b595d1a82fcf078e2daf8dc4a42dea4f0c9b` | Frozen revision 1; author STOP |
| Fresh compiler-referee review | Recorded in current-state receipt; STOP `2026-10-25 01:49:21 UTC` | **CLEAN with limits** |

The reviewer independently checked both directions of F and C, necessity when `t=r`, arbitrary finite typed suffixes, conditional OLD, the W clause inversion, the underdetermination limit, and all supplied source/dependency hashes. No blocking, major or minor findings. Requested reviewer model/effort `gpt-6.1-sol`/`medium`; observed model/effort UNKNOWN/UNKNOWN. Review was read-only; no Lean, tests, builds, compiler execution, Git, or delegation.

The primary also recorded the sprint-boundary dispatcher delta: do not renew the same source-construction search on unchanged inputs; continue only after new accepted constructor evidence. Propositions BIND, COVER and SOUND/PACKET are the exact staged obligations, but they share the same source constructor and do not currently support separate concurrent writers. The beyond-contract proposal of choosing new semantics remains subject to the existing authority process.

## Resources, checks and integration

Original cap: 2,700 seconds. Conservatively charged: Astra 300 + Sol 1,200 + fresh review 600 = 2,100. Conditional Lean 120 expired unused because its accepted source-equation entry gate was not met. Luna integration reservation: 480; no carryover. The three legacy UNKNOWN reservations remain quarantined.

Author and reviewer STOPPED. The primary ran only `python3 tools/agent_sprint.py check`, which reported `STATIC CHECK PASS`; that is tooling consistency evidence, not mathematical or source evidence. No tests, Lean, builds, runtime/compiler execution, or production edits were performed.

Primary integration: synchronize this outcome, `tasks/agent-loop/current.json`, `tasks/current.md`, and the Lean theory map; stage only the explicit reviewed paths; inspect the complete outbound range; commit and non-forced push. The sprint is complete as a reviewed obstruction result, while the original proof goal remains active and OPEN.
