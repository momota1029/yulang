# LEAN-CALL-CONTEXT-TYPING-20261025/r3 outcome

Status: **PASS / CLEAN — formal candidate accepted within this sprint's scope.** The unchanged abstract typed-plugging theorem is Lean-checked and independently reviewed. Source/native correspondence, operational Call adequacy, effect preservation, original Call A/B, original inference A/B, and the broader parent goal remain OPEN.

## Exact claim and scope

The unchanged `YulangClosure.TypedCall.plugEvaluationContext_typed` theorem accepts every `Suffix : Type`, every stored `EvaluationContext Suffix`, every replacement computation `hole`, and its typing derivation at `context.holeType`; it concludes typing of the exact `plugEvaluationContext context hole` at `context.resultType`. The proof composes the actual typed frame list, stored result consumer and pending adapter list. It makes no claim about runtime execution or source construction of these values.

This sprint repaired only elaboration in the existing `TypedCall` renaming/substitution preservation block, then checked the unchanged candidate. It did not change language semantics, typing rules, theorem statements, premises, quantifiers, metadata actions, Rust code or the r1 candidate.

## Frozen inputs and artifacts

- Contract: `tasks/agent-loop/sprints/call-context-typing-20261025-r3.md`, SHA-256 `50314a04521194eb9ec2faef2d122c7afc65f91c58d1cc0936c807d881935d42`.
- Baseline: `c664e9ba3d185142b509a7da733bae5787731e0a`.
- Repaired `CoreSubstitution.lean`: SHA-256 `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a`.
- Immutable `Original` prefix: 21,012 bytes, SHA-256 `a0be6bebabfb767a91ef6f0404a67bf65d0a8c4ce40471a08976c08e88c36f1f`.
- Author handoff revision 2: `tasks/agent-loop/inbox/20261025-call-substitution-repair.md`, SHA-256 `b9f372fb617d2d9be220c20fa7a16d7a46f9ae04a35b9d860931a6e2bee79768`.
- Unchanged candidate: `notes/theory/lean/YulangClosure/CallContextTyping.lean`, SHA-256 `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125`.
- Candidate author handoff: `tasks/agent-loop/inbox/20261025-call-context-typing.md`, SHA-256 `66164283bf0195aa9c9c072378e174d8dd3cbba4b645afd0fafb7ce192b35907`.
- Verification JSONL: `tasks/agent-loop/inbox/20261025-call-context-typing-r3-verification.jsonl`, SHA-256 `5de0b2edba6173fae2aa8a9a678a423fc63702b82a577cb7c0e9bd86bfcc7aa5`; it contains all eight records, including complete stdout/stderr for every compiler invocation and the author feedback record.
- Query source: ignored primary-owned file `notes/theory/lean/.lake/call-context-typing-r3-check.lean`, SHA-256 `dad41d8bfefc03aa5d3cf38633b76f4e490ab781f1b47de7a8aa103192bb8eac`.

Pinned unchanged inputs all matched before the final compile/query: `CoreSyntax.lean` `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece`; `Contracts.lean` `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`; `CoreExecution.lean` `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e`; r1/r2 contracts and outcomes as pinned by r3; `lean-toolchain` `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; `lakefile.toml` `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`; umbrella `YulangClosure.lean` `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f`. The repaired source is the only approved dependency hash change.

## Repair and serialized Lean evidence

Revision 1 fixed the reserved local binder `instance` and supplied lifted substitution through the named implicit parameter. Its first `CoreSubstitution` compile exposed two more errors: the `expose hc` patterns bound the first `ViewOccurrence`, not the final recursive typing premise. The one authorized feedback continuation bound `effectView`, `resultView`, and the recursive proof separately in both `renameCallComp_typed` and `substituteCallComp_typed`, then passed both view fields to `CompTyped.expose`. No further author continuation was used.

The full ordered process receipts are in the JSONL. Lean 4.35.0 ran serially with `-j1 -M1024`; all seven invocations completed within 8.155 seconds total:

| Invocation | Exit | Elapsed | Result |
|---|---:|---:|---|
| `CoreSyntax` | 0 | 3.682 s | `.olean` `daefef78abdae103e9a6e8af2e439301680751991552b8ef14fa84620a423751`; `.ilean` `5f369fcbe65119c88b59e2127bbeddecf2d53a6a68ffb6be347633572bb43629` |
| `Contracts` | 0 | 0.427 s | `.olean` `eac90ceeca9cb6d4479648a92ce9b3b24960c3b0e99de5af2dc7c942e542f6bc`; `.ilean` `6d24c9e7dd4fe9442150d30b927d2f93b58b592cffd643a96a5078cd3c4a91e8` |
| `CoreSubstitution`, revision 1 | 1 | 1.436 s | Complete 522-byte stdout recorded; two `ViewOccurrence` versus `CompTyped` mismatches, at lines 570 and 643. Verification stopped at this authorized feedback boundary. |
| `CoreSubstitution`, revision 2 retry | 0 | 1.315 s | `.olean` `4539c98dfa46d89504823b389df535a336a7754abcca1b7005769d32bfa282e7`; `.ilean` `8a2761cb0e6ffa2df1fe2e66b34b0854dd30e0735a41c933d033c35fdb8fece2` |
| `CoreExecution` | 0 | 0.821 s | `.olean` `ff2fda0ecc175ae831f070d16e2a2382b3735f079338c60aee98f05cecddc05a`; `.ilean` `4818998f613d24fa6ab31bea7de36f77f407bf978438a85b25013afbdc798817` |
| `CallContextTyping` | 0 | 0.270 s | `.olean` `42c711d21b1f2d1cbd5486581448fce252d1b2bb9958329338ecf4dc9ac42204`; `.ilean` `1d32860c9c11b40785582a37f360987701b11d8f38dd3e85c8f5e0851e2d283a` |
| Signature and axiom query | 0 | 0.204 s | All nine required `#check` commands elaborated; stderr empty; complete 4,776-byte stdout recorded. |

Before each final downstream invocation, source pins and the current successful dependency output hashes were rechecked against their receipts. The failed revision-1 outputs were not reused as successes. No tests or broader build ran.

The query printed exact preserved types for `renameCallValue_typed`, `renameCallComp_typed`, `substituteCallValue_typed`, `substituteCallComp_typed`, `executeAdapterBody_typed`, `computationEntryBody_typed`, `contextTyping_plugFrames`, `adaptersTyped_plugResultAdapters`, and `plugEvaluationContext_typed`. The first six depend only on `[propext]`; the three plugging theorems report no axioms. No `sorry`, `admit`, custom axiom, or `unsafe` declaration was found.

## Independent review and adjudication

Fresh reviewer `/root/call_context_r3_review` returned **CLEAN**, with no blocking, major, or minor findings. The reviewer independently checked the final source/prefix and dependency hashes, all ten successful output hashes, the eight complete JSONL records, retry sequence, all nine signatures and axiom output. It verified every `TypedCall` constructor path, both expose views, request instance/payload and lifted continuation, bind/request substitution lifting, unchanged adapter/computation consumers, and all candidate frame/adapter cases with arbitrary `Suffix`.

The reviewer did not run Lean, tests, or Git and did not write or delegate. Requested model/effort: `gpt-6.1-sol/medium`; observed model/effort: `UNKNOWN/UNKNOWN`; exact elapsed time was not measured. It used the primary-supplied baseline diff. Reviewer's STOP and cessation were received before adjudication.

## Remaining boundaries, resources, and Git

The r3 formal dependency and candidate gates are closed for the exact frozen statements. The theorem does not establish that source evaluation contexts are represented by this syntax, that runtime execution preserves these typing derivations, any source/native relation, operation/effect preservation, operational Call A/B, or original inference A/B. The broader semantics and type-inference goal remains active and open. `NO_SAFE_CODE_SLICE` remains the approved implementation finding for dependent runtime work; no Rust or production gate changed.

The 900-second author grant was exhausted by the initial phase plus its one authorized feedback continuation; exact active author time was unavailable, so the full remaining 300 seconds was conservatively charged. Luna used seven of eight permitted Lean invocations and stayed within the 600-second verification cap. Review stayed within its 600-second cap; exact elapsed was unmeasured. No unused budget carries forward.

Research checkpoint commit `ba6012da5` froze the repair, handoff, complete compiler receipts, and current state before review; it was pushed normally to `origin/research/simple-sub-intrusion`. Follow-on commits record review runtime state. Luna remains sole integrator and will commit/push this outcome with the final current-state closure. No unrelated untracked paths were staged or changed.
