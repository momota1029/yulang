# LEAN-CALL-CONTEXT-TYPING-20261025/r1 outcome

Status: **FAILED_VERIFICATION / UNACCEPTED**. The proposition and original parent remain OPEN.

## Frozen work

- Contract: `tasks/agent-loop/sprints/call-context-typing-20261025-r1.md`, SHA-256 `ec637a96ccfc766cf586b89fec740ec9480e50580601516ed588591720e43878`.
- Candidate: `notes/theory/lean/YulangClosure/CallContextTyping.lean`, SHA-256 `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125`.
- Author handoff: `tasks/agent-loop/inbox/20261025-call-context-typing.md`, SHA-256 `66164283bf0195aa9c9c072378e174d8dd3cbba4b645afd0fafb7ce192b35907`.
- Proposition: typed plugging of the exact formal `EvaluationContext`, including its stored context frames, declared-result consumer and pending adapters, for arbitrary `Suffix`.

## Evidence and limits

The author `/root/call_context_typing_author` STOPPED after writing only the two leased files. Requested model/effort were Sol/high; observed model/effort remain UNKNOWN. A fresh read-only reviewer `/root/call_context_typing_review` STOPPED CLEAN for the source-level induction cases, stored equalities, arbitrary suffix, adapter order and scope. The reviewer did not run Lean. Its CLEAN result does not establish kernel acceptance.

All seven frozen source/toolchain/project hashes matched before work and again before target checking: `CoreSyntax` `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece`; `Contracts` `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`; `CoreSubstitution` `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f`; `CoreExecution` `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e`; `lean-toolchain` `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; `lakefile.toml` `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`; `YulangClosure.lean` `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f`.

The initial serial preflight command chained the four compilations, but Luna failed to capture each command's exit status. Silence was incorrectly treated as success. Later filesystem evidence showed `CoreSyntax.olean` and `Contracts.olean` refreshed at 10:56, while `CoreSubstitution.olean` and `CoreExecution.olean` remained from 07:14. Thus preflight PASS was **not established**, and the author-entry precondition had not been met. The candidate was nevertheless launched; this process error is recorded explicitly.

The primary target Lean invocation returned exit code 1. It reported `plugFrames`, `plugFrame`, `plugResultAdapters` and `plugEvaluationContext` unknown in the imported environment, then an unsolved goal. The stale `CoreExecution.olean` explains why source-level declarations were not available, but this is not evidence that the theorem is false or that a particular source dependency fails. No `CallContextTyping.olean/.ilean` was produced. The theorem has not been Lean-accepted and no axioms receipt exists.

## Adjudication

Close r1 as FAILED_VERIFICATION / UNACCEPTED. Preserve both candidate bytes frozen for possible verification. Do not repair them under r1, do not promote the Call proposition, and do not change the unchanged r9 `SOURCE_INPUT_BLOCKED/UNACCEPTED` result. Source/native, execution adequacy, Call A/B, inference A/B and the original parent remain OPEN.

The read-only dispatcher recommends a separate verification-only r2: recompile each pinned dependency in order while recording its exact exit status, output and artifact hash; stop at the first failure; then compile the frozen candidate and query its exact theorem signature and `#print axioms`. No author or source edits are needed unless verification identifies a concrete repair requiring a newly authorized packet.

## Resources and Git

Conservatively charge 480 seconds for the unproven preflight attempt, 600 seconds for the author grant, 300 seconds for independent source review, and 120 seconds for the target-check grant. Luna's integration remains within the original 1,800-second cap; no carryover or refund. No tests or implementation changes were made. All `.olean/.ilean` files are ignored build outputs.

Primary close commit/push is recorded by the repository history and `tasks/agent-loop/current.json`. The three unrelated UNKNOWN reservations remain quarantined.
