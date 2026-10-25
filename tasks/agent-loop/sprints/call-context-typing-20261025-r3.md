# LEAN-CALL-CONTEXT-TYPING-20261025/r3 — repair TypedCall substitution

Status: FROZEN ACTIVE CONTRACT
Branch / baseline: `research/simple-sub-intrusion` / `c664e9ba3d185142b509a7da733bae5787731e0a` (r2 closure and dispatcher record)
Primary: Luna

## Goal and exact scope

Repair the existing Lean `TypedCall` renaming/substitution preservation block so it elaborates under the pinned Lean 4.35.0 toolchain. Then, if that dependency is soundly checked, verify the already-frozen `plugEvaluationContext_typed` candidate from r1. This is a formal proof/elaboration repair only. It changes no language semantics, typing constructors, source claim, theorem statement, premise, quantifier, or metadata action.

The sole author-owned source is `notes/theory/lean/YulangClosure/CoreSubstitution.lean`. The author may edit only the bytes after the exact marker `namespace YulangClosure.TypedCall\n`. The entire preceding `Original` namespace/import prefix is frozen byte-for-byte at SHA-256 `a0be6bebabfb767a91ef6f0404a67bf65d0a8c4ce40471a08976c08e88c36f1f` (21,012 bytes). The initial complete file SHA-256 is `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f`.

Preserve the existing declarations and exact exported types/equations for:

- `liftCallSubstitution`, `renameCallValue`, `renameCallComp`, `renameCallValue_typed`, `renameCallComp_typed`;
- `substituteCallValue`, `substituteCallComp`, `liftedCallSubstitution_typed`, `substituteCallValue_typed`, `substituteCallComp_typed`;
- `executeAdapterBody`, `executeAdapterBody_typed`, `computationEntryBody`, `computationEntryBody_typed`.

Private helper lemmas and alpha-renaming of local binders are allowed. Preserve the original section exactly, every public signature, mutual recursion semantics, request/operator and payload behavior, expose views, binder lifting, adapter execution, and computation-entry substitution. No `sorry`, `admit`, custom axioms, unsafe declarations, new semantic premises, changed source code, or edits to the r1 candidate are permitted.

The immutable downstream candidate is `notes/theory/lean/YulangClosure/CallContextTyping.lean`, SHA-256 `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125`; its handoff is `tasks/agent-loop/inbox/20261025-call-context-typing.md`, SHA-256 `66164283bf0195aa9c9c072378e174d8dd3cbba4b645afd0fafb7ce192b35907`. Do not edit either file. r1 remains `FAILED_VERIFICATION/UNACCEPTED`, r2 remains `FAILED_DEPENDENCY/UNACCEPTED`, and the original typed-plugging theorem remains OPEN until r3 meets its success gate.

## Frozen dependencies

Recheck all hashes before author launch and before each verification phase. Stop on any unapproved difference.

| Input | SHA-256 |
|---|---|
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreSubstitution.lean` base | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `CoreSubstitution.lean` immutable Original prefix | `a0be6bebabfb767a91ef6f0404a67bf65d0a8c4ce40471a08976c08e88c36f1f` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| r1 candidate `CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| r1 candidate handoff | `66164283bf0195aa9c9c072378e174d8dd3cbba4b645afd0fafb7ce192b35907` |
| r1 contract | `ec637a96ccfc766cf586b89fec740ec9480e50580601516ed588591720e43878` |
| r1 outcome | `9ed056210b80b78b944407d122c39b8f2175c4c5f82f583c22b5156f871880c7` |
| r2 contract | `5cf58df4c2efc832c997c697792e4b5d8c7235b497f7b107bdb1a5c939499b9d` |
| r2 outcome | `1cf53752ed46b4c27ff8367a158f333442d41c37a76c8c689725215c9c099500` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |

## Exact ownership and author lane

One Sol/high author owns exactly:

- `notes/theory/lean/YulangClosure/CoreSubstitution.lean`;
- `tasks/agent-loop/inbox/20261025-call-substitution-repair.md`.

The handoff path must be absent at launch. The existing source path is leased exclusively to this author until final STOP. No other source, test, documentation, expected-output, manifest, rules, or Git path is authorized. Author budget: 900 seconds total across the initial repair and at most one feedback continuation. No descendants or scratch files. The author must preserve and report the exact Original-prefix hash and final whole-file hash, all public declaration signatures, no-hole/no-axiom checks, exact errors received, and STOP before independent review.

The author does not run Lean. Luna owns serialized compilation and receipt output. If the first compiled `CoreSubstitution` version fails, Luna may give the author exactly one feedback continuation using the complete persisted stdout/stderr from that command; the author may make one bounded revision within the same 900-second lease, then STOP again. No second feedback cycle. Any failure after that continuation, or any failure in a different dependency or the frozen candidate, closes r3 with that exact obstruction and no further repair.

## Luna verification and durable receipts

Lean is pinned to 4.35.0. Use one compiler process at a time, `-j1 -M1024`, each invocation capped at 120 seconds; aggregate Luna verification cap 600 seconds, at most eight Lean invocations. Verify the complete source hashes and Original-prefix invariant before and after the author lane.

Compile serially in this exact order, rechecking each source hash immediately before its command:

1. `CoreSyntax`
2. `Contracts`
3. repaired `CoreSubstitution`
4. `CoreExecution`
5. unchanged `CallContextTyping`
6. one query module importing the repaired dependency/candidate and issuing `#check` plus `#print axioms` for all listed declarations and `contextTyping_plugFrames`, `adaptersTyped_plugResultAdapters`, and `plugEvaluationContext_typed`.

There is one permitted feedback cycle only if step 3 fails: capture and durably flush the entire command receipt, give the exact diagnostics to the same author, wait for author STOP, then restart verification from step 3 (the earlier CoreSyntax and Contracts successes remain reusable only if their pinned source/output hashes still match). The retry pass then continues through step 6. Any missing source/output hash or receipt stops the gate.

For every invocation, immediately append one JSON object to `tasks/agent-loop/inbox/20261025-call-context-typing-r3-verification.jsonl` and flush it before any next process. Each object records exact argv, cwd, start/end or monotonic elapsed time, exit code or timeout, complete stdout and stderr as captured, input hash, and SHA-256 for each expected output. Do not forward unbounded compiler output directly through a truncating tool response without first persisting it. Silence, mtimes, old outputs, or wrapper completion without exit status do not establish PASS.

Luna may create only the exact query source `notes/theory/lean/.lake/call-context-typing-r3-check.lean`, containing the imports, `#check` declarations and `#print axioms` commands required above. It and the JSONL receipt are primary-owned checker outputs. The ten existing `.olean/.ilean` files listed in r2 are regranted as the only compiler artifact paths. All are ignored under `.lake/`; no other build output is allowed.

Query the exact signatures and axioms of `renameCallValue_typed`, `renameCallComp_typed`, `substituteCallValue_typed`, `substituteCallComp_typed`, `executeAdapterBody_typed`, `computationEntryBody_typed`, `contextTyping_plugFrames`, `adaptersTyped_plugResultAdapters`, and `plugEvaluationContext_typed`. Accept only the exact preserved source statements and standard Lean axioms `[propext, Quot.sound]` (or a strict subset).

## Independent review, scope, and resources

After final author STOP and all final receipts are frozen, one fresh nonauthor proof reviewer audits the diff against the frozen signatures/prefix, constructor coverage, substitution lifting and all command receipts. Reviewer cap: 600 seconds, read-only; no Lean/tests/Git. Luna adjudicates review findings.

Fresh cap **2,400 seconds**: author 900 + Luna verification 600 + independent review 600 + Luna integration 300. Astra 0, one CPU, 1 GiB, one Lean process at a time. No carryover from r1/r2. Preserve all three unrelated UNKNOWN reservations. Author and reviewer run sequentially.

No Rust/compiler runtime edit is authorized. Current findings still give `NO_SAFE_CODE_SLICE` for dependent runtime changes; FL12-SOURCE-1 remains separate, and native/production gates remain OPEN. This repair does not prove source evaluation-context representation, operation/effect preservation, Call A/B, execution adequacy, original inference A/B, source/native correspondence, or the original parent.

## Success, stop, and integration

Success requires: original prefix byte-identical; all existing public statements and syntax equations preserved; all six dependent modules compile from the permitted sequence; the unchanged candidate and all nine theorem checks elaborate; expected axiom output; complete per-command receipts; and a fresh CLEAN review. Otherwise close r3 with the earliest exact obstruction. No semantic promotion or automatic renewal.

Only Luna edits current/outcome/receipt, adjudicates review, stages exact approved paths, inspects the full outbound range, and commits/pushes non-forced. Outcome: `tasks/agent-loop/sprints/call-context-typing-20261025-r3-outcome.md`.
