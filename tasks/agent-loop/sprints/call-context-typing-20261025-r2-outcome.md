# LEAN-CALL-CONTEXT-TYPING-20261025/r2 outcome

Status: **FAILED_DEPENDENCY / UNACCEPTED**. The exact theorem and all parent gates remain OPEN.

## Frozen verification inputs

- Contract: `tasks/agent-loop/sprints/call-context-typing-20261025-r2.md`, SHA-256 `5cf58df4c2efc832c997c697792e4b5d8c7235b497f7b107bdb1a5c939499b9d`.
- Candidate: `notes/theory/lean/YulangClosure/CallContextTyping.lean`, SHA-256 `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125`.
- Handoff: `tasks/agent-loop/inbox/20261025-call-context-typing.md`, SHA-256 `66164283bf0195aa9c9c072378e174d8dd3cbba4b645afd0fafb7ce192b35907`.
- All r2 contract source/toolchain/project pins matched. All ten declared output paths were confirmed ignored under `notes/theory/lean/.gitignore`.
- Lean environment: pinned toolchain source hash matched `leanprover/lean4:v4.35.0`; commands used `lake env lean -j1 -M1024` in `/home/momota1029/rust/yulang/notes/theory/lean`.

## Serialized dependency receipts

Commands used the exact arguments and output paths below. Each process was sequential. `CoreSyntax` and `Contracts` completed with exit code 0 and empty stdout/stderr:

| Module | Elapsed | Exit | `.olean` SHA-256 | `.ilean` SHA-256 |
|---|---:|---:|---|---|
| CoreSyntax | 1.481 s | 0 | `daefef78abdae103e9a6e8af2e439301680751991552b8ef14fa84620a423751` | `5f369fcbe65119c88b59e2127bbeddecf2d53a6a68ffb6be347633572bb43629` |
| Contracts | 0.418 s | 0 | `eac90ceeca9cb6d4479648a92ce9b3b24960c3b0e99de5af2dc7c942e542f6bc` | `6d24c9e7dd4fe9442150d30b927d2f93b58b592cffd643a96a5078cd3c4a91e8` |
| CoreSubstitution | 1.347 s | **1** | `d534b95be630aab3095bf88e9d0e1449affda2b075f85a74a98d765c962dda65` | `3c899a87227a23211e622fd1cdd47367bd7adc5ff0c6fd66da7b8f913a7bf14d` |

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

## Stop and adjudication

The r2 stop rule triggered at the first nonzero dependency command. `CoreExecution` was not recompiled. The target candidate compile, theorem signature query, and `#print axioms` were not run. No target Lean acceptance or counterexample is established. The source-level r1 review remains CLEAN within its stated scope only.

The exact source failure is at `CoreSubstitution.lean:541` under the pinned Lean 4.35.0 command. This verification-only grant does not authorize source repairs, candidate edits, semantic premises, or a new author. A separate contract and grant are required before any correction. The original `plugEvaluationContext_typed` proposition remains OPEN and the r9 `SOURCE_INPUT_BLOCKED/UNACCEPTED` status is unchanged.

No tests, implementation changes, or unpinned compiler invocations were made. No changes were made to the candidate or handoff. The three unrelated UNKNOWN reservations remain quarantined.

## Resources and Git

The r2 dependency sequence stopped after 3.246 seconds of measured compiler time, within its 480-second ceiling. Target compile/query and independent review were not started yet; no resource carryover is authorized. Luna's bounded integration records this exact failure. Primary close commit/push is recorded in repository history and `tasks/agent-loop/current.json`.
