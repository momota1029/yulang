# Yulang3 Codex-only orchestration migration plan

- Status: Proposed（ユーザ確認待ち。実装着手の権限はこの文書単独では与えない）
- Date: 2026-08-30
- Target: `yulang3` branch only
- Scope: repository operating policy, agent roles, design authority, workflow records, test-safety policy, and historical incident placement
- Compiler behavior: no change
- Drafted-by: primary planning agent（provenance only; authority is created by user approval）

## 0. 結論

Yulang3 の運用を、Claude が Codex MCP を監督する二層構造から、primary Codex と役割別
Codex subagent による Codex-only 構造へ移行する。

移行の中心はモデル名の置換ではない。現状の `AGENTS.md` と `CLAUDE.md` に混在する次の五種類を
別の正本へ分離することである。

1. ユーザーが承認した設計判断。
2. Yulang 固有の compiler engineering 規範。
3. agent の役割、情報境界、レビュー topology。
4. 現在有効なテスト・git・資源安全規則。
5. 過去の環境事故、失敗例、モデル挙動の記録。

最終構成では、権威は「どのモデルが書いたか」ではなく「ユーザーがどの scope の判断を承認したか」
から生じる。producer は自分の成果物を独立査読済みと宣言できず、reviewer は read-only のまま
findings を返す。deterministic check と意味的な査読を別物として扱う。

## 1. 現状と移行理由

### 1.1 `AGENTS.md`

現行 `AGENTS.md` は約 24 KB あり、以下を同時に担っている。

- authority order と user-approved design の扱い。
- `tasks/current.md`、日報、handoff、仕様の読み順。
- docs 本文の writing guide routing。
- compiler engineering、module 分割、performance、diagnostics、testing、bug fixing。
- chasa 固有 idiom。
- agent の報告、対話的承認、ユーザー向け口調。
- 巨大な最終 self-check list。

内容の大部分は有用だが、root の agent map と project engineering rule が同居している。
Codex は毎 task で無関係な規範まで受け取り、個別 rule の正本と適用範囲が見えにくい。

### 1.2 `CLAUDE.md`

現行 `CLAUDE.md` は約 49 KB あり、次が混在する。

- Claude → Codex MCP の first-action、visibility、sandbox、prompt template。
- codex-flow、MCP capability、progress notification 等の host-specific plumbing。
- Claude/Codex の役割分担、commit/push、long-task slicing。
- Sol/Terra/Luna の旧 model routing。
- Fable 5、Sonnet 5、Codex に基づく設計文書起案・署名規則。
- Yulang2 `infer` crate のメモリ事故と古い skip list。
- tasks/daily log の運用。

MCP plumbing は Codex-only 化後には不要である。一方、事故記録や design authority の教訓まで
削除すると知識を失う。廃止、現行 rule 化、historical incident 化を分ける必要がある。

### 1.3 operational state files

`tasks/current.md` は約 42 KB あり、「現在地」と完了済み gate の詳細履歴が混在する。
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md` は約 1.78 MB あり、全文を毎 task の入口に
するには大きい。`notes/design/` には status と scope を一覧する index がない。

さらに、少なくとも `tasks/current.md` には user-local `.claude/.../memory` への参照がある。
Codex-only runtime から読めない外部メモリを active authority または必須知識にしてはならない。

### 1.4 current branch state

本計画の基点は `yulang3` commit `2aafbb913123586204b799751201e162df5abdf5` である。
`declaration.rs` module split plan は P14 まで完了済みであり、本 migration はその implementation
sequence に割り込まない。compiler source、Cargo graph、grammar behavior、fixture、diagnostic を変更しない。

## 2. 移行後の authority model

判断が衝突した場合は次の順を用いる。

1. ユーザーの現在の明示指示。
2. scope が一致する `Authoritative` design decision。
3. `rules/` の hard repository rule。
4. 現行コードが明示する invariant、public contract、承認済み test expectation。
5. 既存の局所設計・命名・test convention。
6. 一般的な compiler engineering practice。
7. model intuition。

`Drafted-by`、モデル名、署名は provenance であり authority の根拠ではない。

### 2.1 新 design document header

新規または更新する design document は最低限次を持つ。

```text
Status: Draft | Reviewed | Authoritative | Superseded
Scope: <decision scope>
Approved-by: user | none
Approved-at: <date | none>
Drafted-by: architect | external contributor | other provenance
Reviewed-by: <roles or human reviewers>
Supersedes: <documents/sections | none>
```

状態遷移は次のとおりとする。

```text
Draft -> Reviewed -> Authoritative -> Superseded
```

- `Draft`: 起案中。実装の根拠にしない。
- `Reviewed`: 独立査読済みだが user approval 前。
- `Authoritative`: scope 内で user が承認した正本。
- `Superseded`: 後の Authoritative decision に置換済み。

### 2.2 legacy design compatibility

既存文書の本文と署名は歴史的 provenance として機械的に書き換えない。
次の既存形式は grandfathered `Authoritative` として読む。

- `ユーザ承認済み` または同義の status が明記されている。
- 対象 scope が文書から同定できる。
- `著者: Claude (Fable 5)`、Sol 起案 + Sonnet 査読、外部 PR 起案等の旧署名形式を持つ。

旧署名に含まれるモデル名は将来の role routing を指定しない。新しい変更は新 header に従う。

## 3. target repository topology

```text
AGENTS.md                         # compact map, user-visible communication, hard routing entry
.codex/
  config.toml
  hooks.json                     # only verified, cheap lifecycle hooks
  agents/
    architect.toml
    implementer.toml
    compiler-referee.toml
    spec-auditor.toml
    regression-auditor.toml
    performance-auditor.toml
    docs-writer.toml
rules/
  INDEX.md
  agent-orchestration.md
  design-authority.md
  workflow.md
  compiler-engineering.md
  parser-chasa.md
  bug-fixing.md
  performance.md
  diagnostics.md
  testing.md
  documentation.md
  git-and-concurrency.md
  codex-quirks.md
notes/
  design/
    INDEX.md                     # authority/scope/locator map; source documents remain canonical
  incidents/
    README.md
    legacy-yulang2-infer-memory.md
    ...                         # dated, scoped incidents only
  progress/
tasks/
  current.md                    # navigation and immediate work only
```

`rules/` は現在有効な norm、`notes/incidents/` は過去に起きた fact、`notes/design/` は承認済みまたは
審査中の decision を保持する。incident から rule を導く場合も両方を同じ文書へ混ぜない。

## 4. agent topology

### 4.1 primary agent

primary Codex は user-facing orchestrator とし、次を担う。

- request の理解、task classification、scope と authority の確定。
- specialist role の選択、入力境界、write permission、stop condition の指定。
- user decision の収集と Authoritative status の確定。
- reviewer findings の現物照合、採否、修正指示。
- staging、commit、push、concurrency safety。
- user-visible Japanese communication。

primary の再読は integration check であり、independent review の一票に数えない。

### 4.2 specialist roles

| role | default model / effort | mode | responsibility |
|---|---|---|---|
| `architect` | Sol / high | read-only | architecture、responsibility boundary、gate/phase、rollback、design proposal |
| `implementer` | Sol / high | workspace-write | confirmed design または accepted finding の最小実装 |
| `compiler_referee` | Sol / high | read-only | correctness、root cause、invariant、ownership、soundness、counterexample |
| `spec_auditor` | Terra / high | read-only | Authoritative design、public contract、test expectation との exact conformance |
| `regression_auditor` | Terra / high | read-only | sibling case、call site、CST/AST parity、fixture、public surface、unrelated regression |
| `performance_auditor` | Terra / high | read-only | traversal、allocation、clone、hot-path branch、work count、resource-risk |
| `docs_writer` | Terra / high | workspace-write | `web/docs/`、README、release note 等の public prose |

model と effort は execution configuration であり authority ではない。task が role の能力を超えた場合は
primary が fresh higher-effort session へ reroute する。旧 Level 1–4 または Claude-side tier policy は
active routing として使わない。

### 4.3 write and review boundaries

- ordinary source/design/internal-rule write は `implementer` が confirmed scope に従って行う。
- public documentation write は `docs_writer` が行う。
- reviewer はすべて read-only とし、自分の finding を自分で修正しない。
- subagent は stage、commit、push を行わない。primary が明示 path だけを stage する。
- 同じ worktree で二つの write-capable agent を並列に走らせない。
- 複数の write-capable primary session を並行する場合は session ごとに別 git worktree を使う。
- producer の自己説明、成功期待、以前の review verdict は fresh reviewer の根拠にしない。
- subagent report は concise technical English、user-visible primary response は root `AGENTS.md` の日本語口調に従う。

## 5. task classification and routing

primary は task ごとに次の五軸を判定する。

| axis | values | meaning |
|---|---|---|
| `authority` | `none / existing / new-decision` | confirmed design の有無、user decision の要否 |
| `behavior` | `none / intended / uncertain` | observable compiler behavior を変えるか |
| `scope` | `local / cross-layer` | 一責務内か parser→HIR→types 等を跨ぐか |
| `performance` | `cold / hot / unknown` | hot path、scan、allocation 等に触れるか |
| `surface` | `internal / public / docs` | public API、language semantics、public prose へ出るか |

### 5.1 routing matrix

| task | pre-write | writer | mandatory post-review |
|---|---|---|---|
| file lookup / repository status | primary or built-in explorer | none | none |
| read-only root-cause investigation | built-in explorer; `architect` only if a design choice appears | none | `compiler_referee` when the conclusion is load-bearing |
| typo / exact rename / mechanical edit | none | `implementer` | `regression_auditor` or deterministic diff check, proportional to scope |
| next gate of an Authoritative plan | none; do not redesign | `implementer` | `spec_auditor` + `regression_auditor` |
| bug fix | explorer; `architect` if owner/invariant is uncertain | `implementer` | `compiler_referee` + `regression_auditor` |
| parser recovery / CST / AST behavior | `architect` unless already fully specified | `implementer` | `compiler_referee` + `spec_auditor` + `regression_auditor` |
| new syntax / language feature | `architect` -> user approval | `implementer` | previous three + `performance_auditor` when hot-path relevant |
| HIR / types / core semantics | `architect` | `implementer` | `compiler_referee` + `spec_auditor` + `regression_auditor` |
| performance optimization | explorer -> `architect` | `implementer` | `performance_auditor` + `compiler_referee` + `regression_auditor` |
| pure refactor / module split | no architect when an Authoritative plan exists | `implementer` | `spec_auditor` + `regression_auditor` |
| test expectation / snapshot change | `spec_auditor` before write | `implementer` | `regression_auditor` |
| new or changed design document | `architect` | `implementer` materializes reviewed text | `compiler_referee`; add `performance_auditor` when relevant; then user approval |
| `web/docs/`, README, release prose | `spec_auditor` when technical contract is involved | `docs_writer` | `spec_auditor` |
| orchestration / repository rule | primary or `architect` | `implementer` | fresh `spec_auditor` |

### 5.2 `architect` trigger

`architect` is mandatory when any of the following holds.

```text
authority = new-decision
OR behavior = uncertain
OR scope = cross-layer
```

A confirmed Authoritative design that specifies the current gate must not be reopened merely because a fresh agent prefers another design.
Deviation is reported as a decision point, not silently implemented.

### 5.3 bug-fix choreography

```text
Diagnosis:
  explorer -> root cause -> owning layer -> sibling cases -> broken invariant
Repair:
  implementer -> general fix -> generalized regression test
Adversarial review:
  compiler_referee -> cause or symptom? -> sibling counterexample?
Regression review:
  regression_auditor -> unrelated surfaces and neighboring cases
```

`compiler_referee` must explicitly answer whether the patch fixes the cause or only the observed symptom.

### 5.4 test-expectation gate

An expected diagnostic, snapshot, golden output, asserted type/effect/residual, or intention-bearing test name must not be
changed merely to make current output green. `spec_auditor` first determines one of:

- implementation bug; expectation remains authoritative,
- confirmed specification change; expectation may change,
- unresolved authority conflict; stop for user decision.

## 6. source-to-destination migration map

### 6.1 current `AGENTS.md`

| current section | destination | action |
|---|---|---|
| document purpose | root `AGENTS.md` + `rules/compiler-engineering.md` intro | keep a short map at root; move detail |
| 優先順位 | `rules/design-authority.md` | make approval model-neutral |
| 作業前に見るもの / handoff | `rules/workflow.md` | retain no-reinvestigation and failed-approach rules |
| ドキュメントサイトの本文 | `rules/documentation.md` | point to both existing style guides |
| 基本方針 | `rules/compiler-engineering.md` | retain as hard engineering principles |
| chasa parser combinator idioms | `rules/parser-chasa.md` | preserve verbatim semantics and lifetimes guidance |
| ファイル構成 / module 分割 | `rules/compiler-engineering.md` | combine around entrypoint/responsibility/facade rules |
| 性能方針 | `rules/performance.md` | separate current norm from old incidents |
| バグ修正 / 修正範囲の節度 | `rules/bug-fixing.md` | preserve cause-first and one-cause/one-change policy |
| 実験的規則・最適化 | `rules/compiler-engineering.md` + `rules/performance.md` | split ownership and hot-path questions |
| diagnostics | `rules/diagnostics.md` | preserve structured cause/span before rendering rule |
| テスト / expectation | `rules/testing.md` | preserve expectation authority gate |
| 変更の進め方 | `rules/workflow.md` + `rules/compiler-engineering.md` | route by task type |
| コードコメント | `rules/compiler-engineering.md` | preserve decision-not-paraphrase rule |
| 出力・報告 / 対話的承認 | `rules/agent-orchestration.md` | adapt to primary/subagent boundary |
| 口調 / 行動 | root `AGENTS.md` | user-visible primary only |
| セルフチェック | distribute to each rule's checklist | do not retain one universal mega-checklist |
| Gemini が適合判定する | retire | replace with role-based audits; keep history in git |

### 6.2 current `CLAUDE.md`

| current section | destination | action |
|---|---|---|
| Codex MCP first / visibility / sandbox | none | retire as obsolete transport plumbing |
| codex-flow plugin notes | none or historical incident if still independently useful | do not make active Codex-only policy |
| MCP version/capability/progress rules | none | retire host-specific supervisor plumbing |
| large `infer` memory incidents | `notes/incidents/legacy-yulang2-infer-memory.md` | preserve dates, commands, causes, scope; mark legacy |
| general resource-safety lesson | `rules/testing.md` | narrow-first, thread cap, no blind full-suite run |
| Role split / exceptions / pass-through | `rules/agent-orchestration.md` | replace products with roles |
| delegation prompt/template/default targets | `.codex/agents/*.toml` + orchestration rule | remove MCP request boilerplate |
| documentation prose | `rules/documentation.md` | retain guide routing |
| commit and push split | `rules/git-and-concurrency.md` | primary owns git; subagents own no commits |
| long-task slicing / 30-minute limit / after-return / stuck | `rules/workflow.md` | retain coherent slices and progress; retire universal MCP-specific 30-minute hard stop |
| model routing policy | `.codex/config.toml` + agent files | role-first routing; no active tier essay |
| design priority / Fable absence | `rules/design-authority.md` | authority from user approval; preserve legacy compatibility only |
| current authoritative docs list | `notes/design/INDEX.md` | one locator map, not a second source of semantics |
| tasks / daily-log policy | `rules/workflow.md` | current = navigation, progress = history |

### 6.3 external `.claude` dependencies

Implementation must run a repository-wide census for:

```text
CLAUDE.md
Claude
Fable
Codex MCP
.codex-flow
.claude/
/home/.../.claude/
Level 1 / Level 2 / Level 3 / Level 4
model-tier names used as active policy
```

Every hit is classified as one of:

1. active operational rule: rewrite to role-based policy,
2. Authoritative legacy provenance: keep, covered by compatibility rule,
3. historical progress/commit narrative: keep unchanged,
4. external memory containing durable knowledge: move the knowledge into `rules/` or `notes/incidents/`,
5. obsolete transport plumbing: delete.

No global string replacement is allowed. Historical text and design provenance must not be rewritten into false history.

## 7. design index and task records

### 7.1 `notes/design/INDEX.md`

The index records only navigation and authority metadata:

- title/path,
- status,
- scope,
- approval date,
- supersession relation,
- key section locators,
- active gate or implementation state when applicable.

It does not paraphrase enough semantics to become a competing design source. Large documents remain canonical.

Initial entries include at least:

- `docs/yulang3-architecture.md`,
- `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`,
- `notes/design/2026-08-20-phase2-parser-fixture-schema.md`,
- `notes/design/2026-08-30-declaration-module-split-plan.md`, marked completed.

### 7.2 `tasks/current.md`

Future contract:

```text
current objective
applicable Authoritative design
active gate or immediate operation
next action
blockers / decision points
known residuals that affect the next action
```

Completed gate narratives, detailed test counts, and retrospective incident explanations move to `notes/progress/` or git history.

The initial orchestration migration does not perform a lossy rewrite of the current 42 KB file. Compaction is a separately reviewed
follow-up after the new index and workflow rule exist.

### 7.3 incidents

Incident records state:

- date and affected branch/generation,
- exact command or operation,
- observed resource/failure behavior,
- verified cause,
- mitigation that was valid in that environment,
- whether the lesson remains active for Yulang3.

The legacy `infer` skip list must not be presented as a current Yulang3 command recipe because the present workspace does not contain
that crate. The reusable rule is extracted; the old command details remain historical evidence.

## 8. deterministic verification and hooks

### 8.1 separation of checks and review

Deterministic verification includes:

- format checking,
- dependency-graph checking,
- compilation,
- focused tests,
- fixture/golden comparison,
- benchmark/work-count measurement where specified.

Judgment review includes:

- correctness and invariant review,
- design conformance,
- regression reasoning,
- performance-design review.

A green command does not count as an independent review, and reviewer agreement does not replace tests.

### 8.2 v1 hooks

Do not automatically run broad Cargo tests on every edit or subagent stop.

Proposed v1 hooks are deliberately cheap:

- `SessionStart`: report branch, dirty state, `tasks/current.md`, and `notes/design/INDEX.md` entry points.
- `SubagentStop` for write roles: run `git diff --check` and report changed paths; do not stage or commit.

Project-local hooks require a current-environment schema check and a local smoke test before merge. If hook behavior is not verified,
ship the role/rule migration without hooks rather than guessing.

### 8.3 future safe test entrypoint

A future, separately approved change may add:

```text
cargo xtask verify --scope <crate-or-area> --level <focused|workspace|soak>
```

It may encode thread limits, safe test filters, resource monitoring, and the established fmt/graph/check sequence. This tooling and any
CI expansion are outside the orchestration migration to keep compiler behavior and build policy unchanged.

## 9. implementation phases and commit plan

### Phase 0 — proposed design（this document）

- add only this migration plan on a review branch,
- do not modify active `AGENTS.md`, `CLAUDE.md`, source, CI, or tasks,
- obtain user approval before implementation.

### Phase 1 — role runtime and orchestration skeleton

Commit: `Add Codex-native role runtime`

- add `.codex/config.toml`, seven agent files, and verified minimal hooks if available,
- add `rules/agent-orchestration.md` and `rules/INDEX.md`,
- leave current `AGENTS.md` and `CLAUDE.md` in place temporarily,
- document that new runtime does not yet supersede all old policy until the migration branch is complete.

### Phase 2 — extract engineering rules and rewrite root map

Commit: `Extract Yulang compiler engineering rules`

- create compiler, parser, bug-fix, performance, diagnostics, testing, documentation, and workflow rules,
- move each active `AGENTS.md` section according to §6.1,
- replace root `AGENTS.md` with compact routing map plus user-visible communication rules,
- retain every technical invariant; do not summarize away exact chasa or expectation rules.

### Phase 3 — model-neutral design authority and navigation

Commit: `Make Yulang design authority model-neutral`

- add `rules/design-authority.md`,
- add `notes/design/INDEX.md`,
- grandfather existing approved documents without rewriting their authorship,
- add current/task/progress contract,
- census external `.claude` memory references and migrate any active durable knowledge.

### Phase 4 — preserve incidents and retire supervisor plumbing

Commit: `Retire Claude and MCP orchestration policy`

- create scoped historical incident records,
- extract only current generalized safety rules,
- add `rules/git-and-concurrency.md` and `rules/codex-quirks.md`,
- delete `CLAUDE.md`,
- remove obsolete codex-flow/MCP-only ignore entries or references if present,
- leave historical commit messages, progress notes, and approved design signatures intact.

### Phase 5 — migration audit and cleanup

Commit: `Audit Codex-only policy migration`

- run the legacy-name/external-memory census,
- verify every active source section has one authoritative destination,
- validate TOML, JSON, and helper-script syntax,
- confirm no `crates/**`, Cargo manifest, lockfile, fixture, CI workflow, or public docs content changed,
- run fresh `spec_auditor` and `regression_auditor` on the policy migration,
- update indexes and migration record with accepted findings.

The implementation branch is merged into `yulang3` only after all phases are present. Intermediate partial policy is not merged.

## 10. acceptance criteria

The migration is complete only when all of the following hold.

1. `AGENTS.md` is a compact map, not the sole copy of compiler rules.
2. The seven specialist agents exist with correct read/write boundaries.
3. Every active rule from old `AGENTS.md` has a destination and no material invariant is lost.
4. Active behavior no longer depends on `CLAUDE.md`, Codex MCP, codex-flow, Fable availability, or Claude-side routing.
5. Existing approved design documents remain historically accurate and authoritative within their scopes.
6. New authority is created only by explicit user approval, not by model authorship.
7. `notes/design/INDEX.md` makes current authority locatable without replacing source documents.
8. Current testing rules do not present obsolete Yulang2 `infer` commands as Yulang3 recipes.
9. Durable knowledge required for current work is not stored only in user-local `.claude` memory.
10. Subagents cannot claim independent review of their own work and do not own git integration.
11. No compiler source, Cargo graph, language behavior, fixtures, CI semantics, or public documentation behavior changes.
12. Local Codex config/agent/hook smoke tests pass in the actual installed environment before merge.
13. Fresh policy review reports no accepted BLOCKING or major finding after the final change.

## 11. risks and controls

### Codex configuration drift

Custom-agent or hook schemas may differ from remembered documentation. Verify the installed Codex version and actual project-scoped
configuration behavior. Do not land guessed fields.

### partial-policy conflict

During development branch phases, old and new policy may conflict. The branch is not used for ordinary compiler work and is merged only
as a complete unit. `yulang3` remains active and unchanged until then.

### historical falsification

Mechanical replacement of Claude/Fable/model names would falsify provenance. Use classification, not global replacement.

### rule loss through summarization

Exact parser lifetime rules, expectation rules, and bug-fix prohibitions are load-bearing. Migration review compares old and new rules
section by section rather than relying on a prose summary.

### automatic test cost

Hooks must not launch broad tests. Scope-specific verification remains an explicit task until a safe `xtask verify` contract is separately
approved.

### rollback

The migration is delivered as a reviewable branch/PR with policy-only commits. A single merge revert restores the previous operating
files; no compiler source rollback is involved.

## 12. fixed decisions and deferred follow-ups

### Fixed by this proposal

- target only `yulang3`, never `main`,
- primary Sol with user-facing Japanese communication,
- seven specialist roles listed in §4,
- reviewer read-only and producer/reviewer thread separation,
- user approval as design authority,
- role-first routing matrix in §5,
- root map plus detailed `rules/`,
- incident/history separation,
- no compiler behavior or broad-test-hook change.

### Deferred to separate design/implementation

- `cargo xtask verify` and resource-guard implementation,
- CI test expansion,
- one-time compaction of `tasks/current.md`,
- relocation of every historical external-memory reference that is not active,
- deeper restructuring of the 1.78 MB parser architecture document,
- changes to public documentation style guides.

## 13. approval gate

After user review, change the header to:

```text
Status: Authoritative
Approved-by: user
Approved-at: 2026-08-30
```

Only then create the implementation branch from the current `yulang3` head and execute Phases 1–5. If `yulang3` advances before
implementation begins, rebase the migration plan against the new head and recheck active task/design state before writing policy files.
