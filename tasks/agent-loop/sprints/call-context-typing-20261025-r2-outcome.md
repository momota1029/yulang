# LEAN-CALL-CONTEXT-TYPING-20261025/r2 outcome

Status: **FAILED_DEPENDENCY / UNACCEPTED**. The exact theorem and all parent gates remain OPEN.

## Frozen verification inputs

- Contract: `tasks/agent-loop/sprints/call-context-typing-20261025-r2.md`, SHA-256 `5cf58df4c2efc832c997c697792e4b5d8c7235b497f7b107bdb1a5c939499b9d`.
- Candidate: `notes/theory/lean/YulangClosure/CallContextTyping.lean`, SHA-256 `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125`.
- Handoff: `tasks/agent-loop/inbox/20261025-call-context-typing.md`, SHA-256 `66164283bf0195aa9c9c072378e174d8dd3cbba4b645afd0fafb7ce192b35907`.
- All r2 contract source/toolchain/project pins matched. All ten declared output paths were confirmed ignored under `notes/theory/lean/.gitignore`.
- Lean environment: pinned toolchain source hash matched `leanprover/lean4:v4.35.0`; commands used `lake env lean -j1 -M1024` in `/home/momota1029/rust/yulang/notes/theory/lean`.

## Serialized dependency receipts

The primary's serialized wrapper reported the following commands, in order. These exact vectors and output hashes are preserved here from the visible process receipt; there is no separate raw receipt file. Luna reported that `CoreSyntax` and `Contracts` completed with exit code 0 and empty stdout/stderr:

| Module | Elapsed | Exit | `.olean` SHA-256 | `.ilean` SHA-256 |
|---|---:|---:|---|---|
| CoreSyntax | 1.481 s | 0 | `daefef78abdae103e9a6e8af2e439301680751991552b8ef14fa84620a423751` | `5f369fcbe65119c88b59e2127bbeddecf2d53a6a68ffb6be347633572bb43629` |
| Contracts | 0.418 s | 0 | `eac90ceeca9cb6d4479648a92ce9b3b24960c3b0e99de5af2dc7c942e542f6bc` | `6d24c9e7dd4fe9442150d30b927d2f93b58b592cffd643a96a5078cd3c4a91e8` |
| CoreSubstitution | 1.347 s | **1** | `d534b95be630aab3095bf88e9d0e1449affda2b075f85a74a98d765c962dda65` | `3c899a87227a23211e622fd1cdd47367bd7adc5ff0c6fd66da7b8f913a7bf14d` |

The first two reported invocations used these exact argument vectors and working directory:

```text
argv: ["lake", "env", "lean", "-j1", "-M1024", "-o", "/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSyntax.olean", "-i", "/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSyntax.ilean", "YulangClosure/CoreSyntax.lean"]
cwd: /home/momota1029/rust/yulang/notes/theory/lean

argv: ["lake", "env", "lean", "-j1", "-M1024", "-o", "/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/Contracts.olean", "-i", "/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/Contracts.ilean", "YulangClosure/Contracts.lean"]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
```

The exact `CoreSubstitution` invocation was:

```text
argv: ["lake", "env", "lean", "-j1", "-M1024", "-o", "/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSubstitution.olean", "-i", "/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSubstitution.ilean", "YulangClosure/CoreSubstitution.lean"]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
```

Visible compiler diagnostics began:

```text
YulangClosure/CoreSubstitution.lean:541:14: error: unexpected token 'instance'; expected '=>'
YulangClosure/CoreSubstitution.lean:541:44: error: unexpected token '=>'; expected ':'
YulangClosure/CoreSubstitution.lean:543:25: error: unexpected token '('; expected ')'
YulangClosure/CoreSubstitution.lean:545:0: error: Missing name after `end`: Expected the current scope name `TypedCall`
```

Further parser and type errors followed. The command output was captured by the primary's process wrapper, but the outer tool response truncated it; the complete stdout was not durably preserved. Stderr was empty. This is recorded as a receipt gap, not silently treated as a complete transcript. The generated `.olean/.ilean` hashes equal the preexisting files, so their presence does not indicate a successful compile.

## Independent receipt review

Fresh read-only reviewer `/root/call_context_receipt_review` STOPPED after reviewing the frozen inputs and available receipts. Requested model/effort were gpt-6.1-sol/low; observed model/effort remain UNKNOWN. The reviewer independently matched the contract, all 11 pinned inputs and all six recorded output hashes, confirmed the `.lake/` ignore rule and pinned Lean version, and found no candidate target artifacts. It agreed with **FAILED_DEPENDENCY / UNACCEPTED** closure, but did **not** certify a CLEAN receipt audit: the missing complete `CoreSubstitution` stdout is a major evidence gap. It also noted that the first two argv vectors were absent in the reviewed snapshot; they are now recorded above from the primary's visible process receipt, not independently recovered from a raw log. The reviewer could not independently authenticate reported timings/exits or establish process order from persisted logs.

The review confirms that the outcome does not infer theorem falsity or Lean acceptance. The first dependency failure and the disclosed receipt gap both require stopping under the contract.

## Stop and adjudication

The r2 stop rule triggered at the first nonzero dependency command. `CoreExecution` was not recompiled. The target candidate compile, theorem signature query, and `#print axioms` were not run. No target Lean acceptance or counterexample is established. The source-level r1 review remains CLEAN within its stated scope only.

The exact source failure is at `CoreSubstitution.lean:541` under the pinned Lean 4.35.0 command. This verification-only grant does not authorize source repairs, candidate edits, semantic premises, or a new author. A separate contract and grant are required before any correction. The original `plugEvaluationContext_typed` proposition remains OPEN and the r9 `SOURCE_INPUT_BLOCKED/UNACCEPTED` status is unchanged.

No tests, implementation changes, or unpinned compiler invocations were made. No changes were made to the candidate or handoff. The three unrelated UNKNOWN reservations remain quarantined.

## Resources and Git

The r2 dependency sequence stopped after 3.246 seconds of primary-measured compiler time, within its 480-second ceiling; the reviewer could not independently authenticate that timing from a durable process log. The target compile/query did not start. The receipt review used the 180-second cap; no target or unused-budget carryover is authorized. Final outcome/current commit and push are recorded in repository history and `tasks/agent-loop/current.json`.
