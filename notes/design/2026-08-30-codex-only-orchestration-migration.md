# Yulang3 Codex-only orchestration migration plan

- Status: Proposed（方向性はユーザ承認済み、本文の最終承認待ち）
- Date: 2026-08-30
- Scope: `yulang3` branch の agent orchestration、設計権威、開発規範、検証・事故記録の配置
- Base inspected: `2aafbb913123586204b799751201e162df5abdf5`
- Compiler behavior: zero change
- Drafted-by: primary agent
- Implementation gate: 本文を `Authoritative` へ変更するユーザ承認まで実装を開始しない

## 0. 目的

現在の `AGENTS.md` と `CLAUDE.md` には、次の異なる責務が混在している。

1. ユーザーとの会話規則。
2. compiler engineering の恒久規範。
3. 設計文書の権威と承認手続。
4. Claude から Codex MCP を呼ぶための transport 固有規則。
5. model tier の動的 routing。
6. 過去の test / memory incident と、その時点の回避コマンド。
7. task、handoff、日報、commit、push の運用。

Codex-only 化では、これらを一つの巨大 prompt へ移し替えない。primary Codex と specialist agents の役割を分け、恒久規範、設計正本、事故記録、deterministic verification を別の正本へ配置する。

この移行は compiler、parser、HIR、type system、backend、diagnostics、公開言語仕様の挙動を変更しない。`crates/`、`benchmarks/`、`web/` の製品コードまたは site 本文は対象外である。

## 1. 現状診断

### 1.1 `AGENTS.md`

現行 `AGENTS.md` は価値の高い規範を持つが、約 24 KB の単一文書に以下が同居している。

- authority order と作業前 context。
- chasa parser combinator の局所 idiom。
- file / module 構成。
- hot path と performance。
- root-cause bug fixing。
- diagnostics、testing、comment、scope discipline。
- 対話・承認・口調。
- compiler-specific self-checklist。

このうち、口調と top-level routing だけが root `AGENTS.md` の責任である。技術規範は `rules/` へ分離し、`AGENTS.md` は正本への地図にする。

### 1.2 `CLAUDE.md`

現行 `CLAUDE.md` は約 49 KB で、次を同時に担う。

- Claude→Codex MCP first / visibility / sandbox / request template。
- codex-flow と MCP capability の環境固有事項。
- progress、30 分停止、slice、commit / push responsibility。
- Sol / Terra / Luna の動的 routing。
- Fable 5 / Sonnet 5 / Codex による設計文書起案手続。
- design authority と authoritative document list。
- yulang2 `infer` crate の memory incident と skip list。
- documentation prose、task、daily log の運用。

Codex-only 実行では MCP supervisor plumbing、Fable 代替手順、Level / tier routing は active policy として不要になる。事故記録は消さず、historical incident へ移す。

### 1.3 `.claude/`

`.claude/settings.local.json` は `Bash(cargo run *)` の Claude permission だけを持つ。Codex-only 化後の正本にはならないため退役する。

### 1.4 移行開始条件

`declaration.rs` module split plan は P14 まで完了し、`tasks/current.md` に完了が記録された。この migration は、その refactor の途中へ割り込まず、完了後の `yulang3` HEAD から別 branch で行う。

## 2. 固定する決定

1. 対象は `momota1029/yulang` の `yulang3` branch だけとする。`main` は変更しない。
2. primary agent は `gpt-5.6-sol` / `high` とする。
3. ユーザーとの直接会話にだけ、現行 `AGENTS.md` の日本語口調規則を適用する。
4. subagent の内部報告は concise technical English とする。
5. 成果物の register は対象文書の規則に従い、会話口調を継承しない。
6. specialist は `architect`、`implementer`、`compiler_referee`、`spec_auditor`、`regression_auditor`、`performance_auditor`、`docs_writer` の七役とする。
7. repository mapping には Codex built-in `explorer` を使い、custom explorer は追加しない。
8. code または design の reviewer は read-only とする。通常の code write は `implementer`、公開 docs write は `docs_writer` だけが行う。
9. subagent は stage、commit、push を行わない。primary agent が git integration を行う。
10. design authority の根拠は model 名または署名者ではなく、明示された scope に対するユーザー承認とする。
11. compiler code、test expectation、fixture、public behavior は migration 中に変更しない。
12. v1 では automatic test / build hook を導入しない。安全な `xtask verify` entrypoint の設計は別 task とする。
13. `tasks/current.md` の内容整理と CI test 拡張は migration から分離する。

## 3. 権威モデル

### 3.1 優先順位

同じ scope について判断が衝突する場合、次の順で扱う。

1. 現在のユーザーによる明示決定。
2. その scope を明示して `Authoritative` となった design / spec。
3. active repository rules。
4. 現行コードが表現する invariant と、意図が確認された test contract。
5. 一般的な実装慣習または model intuition。

上位の項目でも、対象 scope 外の判断を支配しない。広い architecture document と、後から承認された狭い addendum が衝突する場合は、狭い addendum が `Supersedes` を明示した範囲だけで優先する。

### 3.2 design status

新規 design document は次の状態機械を使う。

```text
Draft → Reviewed → Authoritative → Superseded
```

- `Draft`: 起案中。実装を拘束しない。
- `Reviewed`: independent review を通したが、ユーザー承認前。
- `Authoritative`: scope と decision がユーザー承認済み。
- `Superseded`: 後続文書へ権威を移した。履歴として削除しない。

推奨 header:

```text
Status: Authoritative
Scope: <authority scope>
Approved-by: user
Approved-at: YYYY-MM-DD
Drafted-by: architect
Reviewed-by: compiler_referee, spec_auditor
Supersedes: <document or none>
```

`Drafted-by` と `Reviewed-by` は provenance であり、authority の源泉ではない。

### 3.3 legacy compatibility

既存文書は署名を書き換えない。

- 「ユーザ承認済み」と明記された既存文書は、宣言された scope で grandfathered `Authoritative` として扱う。
- `著者: Claude (Fable 5)`、`Codex gpt-5.6-sol が起案`、`Claude Sonnet 5 が査読` 等は historical provenance として保持する。
- 起案 model の利用可否により authority が消失または変化することはない。
- 既存文書を変更する場合は、新 status header を持つ addendum または後続版を作る。署名だけを現代化する commit は作らない。

## 4. target topology

```text
User
  │
  ▼
Primary Codex — Sol / high
  │
  ├── built-in explorer
  ├── architect
  ├── implementer
  ├── compiler_referee
  ├── spec_auditor
  ├── regression_auditor
  ├── performance_auditor
  └── docs_writer
```

primary agent は user interface、task classification、authority resolution、review adjudication、git integration を担う。producer の自己評価または primary 自身の再読を independent review の一票に数えない。

## 5. specialist roles

| role | model / effort | sandbox | responsibility |
|---|---|---|---|
| `architect` | Sol / high | read-only | responsibility boundary、design、phase / gate、invariant、rollback condition を提案する |
| `implementer` | Sol / high | workspace-write | confirmed design または accepted findings だけを実装する |
| `compiler_referee` | Sol / high | read-only | semantics、soundness、root cause、IR invariant、edge case を敵対的に検証する |
| `spec_auditor` | Terra / high | read-only | authoritative design、language spec、test contract と diff の exact conformance を監査する |
| `regression_auditor` | Terra / high | read-only | sibling case、public call site、CST / AST parity、fixture、diagnostics、unrelated behavior の回帰を探す |
| `performance_auditor` | Terra / high | read-only | traversal、allocation、clone、cache、inner-loop branch、resource-heavy verification を監査する |
| `docs_writer` | Terra / high | workspace-write | `web/docs/`、README、user-facing guide を既存 style guide に従って書く |

`performance_auditor` が architecture-level decision を必要とすると判断した場合、自分で決定せず `architect` へ escalate する。

`architect` は code を編集しない。完成した design text を report として起案できるが、primary agent が review と user approval を経て repository へ記録する。

`docs_writer` は authoritative design document を確定しない。design document の prose 整形を担当する場合も、decision は `architect` report と primary adjudication から変更しない。

## 6. task classification

primary agent は write 前に次の五軸を分類する。

| axis | values | question |
|---|---|---|
| `authority` | `none / existing / new-decision` | confirmed design があるか、新しい判断が必要か |
| `behavior` | `none / intended / uncertain` | observable compiler behavior を変えるか |
| `scope` | `local / cross-layer` | 一責務内か、parser→HIR→types 等を跨ぐか |
| `performance` | `cold / hot / unknown` | hot path、再走査、allocation、resource risk に触れるか |
| `surface` | `internal / public / docs` | public API、language behavior、公開文書に現れるか |

`architect` は次のいずれかで必須とする。

```text
authority = new-decision
OR behavior = uncertain
OR scope = cross-layer
```

既存 Authoritative design が実装方法と gate を十分に決めている場合、architect を再起動して再設計しない。

## 7. routing matrix

| task | pre-write | writer | mandatory post-review |
|---|---|---|---|
| file / symbol / current-state lookup | primary または built-in `explorer` | — | — |
| read-only root-cause investigation | built-in `explorer`; open-ended なら `architect` | — | 難しい意味論なら `compiler_referee` |
| typo、format、fully specified rename | — | `implementer` | `regression_auditor` |
| Authoritative plan の既定 gate | — | `implementer` | `spec_auditor` + `regression_auditor` |
| pure refactor / module split | existing design がなければ `architect` | `implementer` | `spec_auditor` + `regression_auditor` |
| bug fix | explorer; root cause / owner が不明なら `architect` | `implementer` | `compiler_referee` + `regression_auditor` |
| parser grammar / recovery / CST / AST change | 未決定なら `architect` + user approval | `implementer` | `compiler_referee` + `spec_auditor` + `regression_auditor` |
| HIR / type / core semantics | `architect` + user approval | `implementer` | `compiler_referee` + `spec_auditor` + `regression_auditor` |
| public API / language behavior | `architect` + user approval | `implementer` | `compiler_referee` + `spec_auditor` + `regression_auditor` |
| performance optimization | explorer → `architect` | `implementer` | `performance_auditor` + `compiler_referee` + `regression_auditor` |
| test expectation / snapshot / golden update | write 前に `spec_auditor` | `implementer` | `regression_auditor` |
| new / changed design document | `architect` | primary records reviewed draft | `compiler_referee`; exact scope は `spec_auditor`; 最後に user approval |
| `web/docs/` / README | 必要なら `spec_auditor` | `docs_writer` | `spec_auditor`; executable example は `regression_auditor` |
| orchestration / repository rule change | primary または `architect` | primary | fresh `spec_auditor` |

### 7.1 test expectation gate

`assert_eq!` の期待値、snapshot、golden、fixture の expected diagnostics、test 名が表す contract を変更するときは、実装前に `spec_auditor` が次を判定する。

1. expected behavior が authoritative design / spec から導出できるか。
2. failure は implementation bug か、意図した spec change か。
3. expectation を変える場合、その理由と approval が記録されているか。

「現在の出力に合わせる」ことだけを理由に expected output を更新しない。

### 7.2 performance trigger

次のいずれかを追加・変更する場合は `performance_auditor` を必須とする。

- scan / traversal。
- nontrivial allocation または clone。
- cache / memoization / invalidation。
- hash map、table、index の再構築。
- inner-loop branch。
- recursive algorithm または worklist。
- parallelism、locking、thread count。
- benchmark-motivated code。
- 大量メモリまたは長時間を消費し得る test / verification command。

## 8. information boundaries

### 8.1 producer / reviewer separation

- `implementer` と `docs_writer` は自分の成果物を independent review 済みと宣言しない。
- reviewer は file を修正しない。finding と最小 closure condition だけを返す。
- accepted finding の修正は fresh `implementer` thread へ渡す。
- 修正後は fresh reviewer を割り当てる。

### 8.2 reviewer input

`compiler_referee`:

- target code、direct dependencies、authoritative design、relevant tests を読む。
- implementer の自己説明または「この修正は正しい」という report を初回 review 前に読まない。

`spec_auditor`:

- authoritative design / spec、target diff、test contract を読む。
- implementation convenience を設計変更の根拠にしない。

`regression_auditor`:

- before / after、public call sites、sibling cases、fixtures、diagnostics を読む。
- design に書かれた「zero behavior change」を事実として仮定しない。

`performance_auditor`:

- changed path、surrounding loops / ownership、metrics / benchmark があれば読む。
- implementer の performance claim を evidence として扱わない。

### 8.3 parallelism

独立した read-only review は最大 thread 数の範囲で並列化してよい。報告は全員の読了前に相互共有しない。

同じ working tree 上で write-capable agent を並列に走らせない。複数の write task を同時に進める必要がある場合は、session ごとに別 git worktree を使う。

## 9. target file layout

```text
AGENTS.md
.codex/
  config.toml
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
  testing.md
  documentation.md
  git-concurrency.md
  codex-quirks.md
notes/design/
  INDEX.md
notes/incidents/
  README.md
  yulang2-infer-test-memory.md
```

v1 では `.codex/hooks.json` を作らない。automatic hook は safe verification entrypoint が確定してから別 design で追加する。

## 10. `AGENTS.md` migration map

| current section | destination | action |
|---|---|---|
| document purpose | root `AGENTS.md` | 一段落の repository purpose へ圧縮 |
| 優先順位 | `rules/design-authority.md`; root は pointer | model 署名を authority 条件から除く |
| 作業前に見るもの / handoff | `rules/workflow.md` | confirmed fact / failed approach / forbidden action の継承規則を保持 |
| ドキュメントサイトの本文 | `rules/documentation.md` | 二つの style guide を必須入力として保持 |
| 基本方針 | `rules/compiler-engineering.md` | responsibility、entrypoint、recomputation 回避を保持 |
| chasa parser combinator idioms | `rules/parser-chasa.md` | 具体的 idiom を verbatim-level で保持 |
| ファイル構成 / module 分割 | `rules/compiler-engineering.md` | main-first、hub / child module、曖昧名禁止を保持 |
| 性能方針 | `rules/performance.md` | hot path と禁止パターンを保持 |
| バグ修正の方針 | `rules/bug-fixing.md` | root-cause workflow と temporary workaround 条件を保持 |
| 修正範囲の節度 | `rules/bug-fixing.md` + `rules/workflow.md` | one cause / one change、format-only separation を保持 |
| 実験的な規則・最適化 | `rules/compiler-engineering.md` + `rules/performance.md` | ownership、entrypoint、removability を保持 |
| diagnostics | `rules/compiler-engineering.md` | structured cause と presentation separation を保持 |
| テスト | `rules/testing.md` | expected-output protection を最優先項目として保持 |
| 変更の進め方 | `rules/workflow.md` | entrypoint→core→helper→checks の順を保持 |
| コードコメント | `rules/compiler-engineering.md` | decision comment と useless comment の区別を保持 |
| 出力・報告 | `rules/agent-orchestration.md` | role handoff schema へ変換 |
| 対話的な承認・権限確認 | root `AGENTS.md` + `rules/agent-orchestration.md` | noninteractive subagent と user decision gate を分離 |
| 口調 / 行動 | root `AGENTS.md` | user-visible primary にだけ適用 |
| セルフチェック | 各 rule の checklist + root communication check | 50項目超の一括 list を責務別に分解 |
| Gemini が判定 | 廃止 | active reviewer を `spec_auditor` 等へ置換 |

## 11. `CLAUDE.md` migration map

| current section | destination | action |
|---|---|---|
| Codex MCP first / visibility / sandbox | 廃止 | Codex-only primary では supervisor transport が存在しない |
| codex-flow plugin notes | `notes/incidents/` または git history | active rule から除去。yulang3 runtime に必要な現行知識だけ別途再検証する |
| MCP capability / progress notification | 廃止 | Codex-native session の通常 progress と `rules/workflow.md` へ置換 |
| role split / exceptions / request template | `rules/agent-orchestration.md` | specialist role と bounded handoff contract へ置換 |
| default delegation targets | routing matrix | task type から role を決める |
| commit / push split | `rules/git-concurrency.md` | primary が stage / commit / push を所有。subagent commit を廃止 |
| small / large task slicing | `rules/workflow.md` | authoritative gate と coherent slice を基準に再定義 |
| hard 30-minute stop | 廃止 | transport workaround としては退役。milestone reporting は保持 |
| after return / stuck / summary | `rules/agent-orchestration.md` | escalation と handoff schema へ統合 |
| Sol / Terra / Luna dynamic routing | `.codex/agents/*.toml` | role-specific fixed model へ置換。旧 Level / tier 名で routing しない |
| documentation site prose | `rules/documentation.md` | style guide contract を保持 |
| design authority / Fable absence | `rules/design-authority.md` | model-based authority を廃止し、user approval へ一本化 |
| current authoritative docs list | `notes/design/INDEX.md` | scope / status / supersedes を索引化 |
| task / daily log | `rules/workflow.md` | current navigation と history を分離 |
| yulang2 infer memory incidents | `notes/incidents/yulang2-infer-test-memory.md` | historical と明記し、skip list を yulang3 active rule にしない |

migration 完了時に `CLAUDE.md` と `.claude/` を削除する。`.old`、archive copy、replacement symlink は作らない。Git history が旧 policy の正本である。

## 12. testing and incident policy

### 12.1 active testing rule

`rules/testing.md` は current workspace に対して次だけを active rule とする。

- 最小の relevant test から始める。
- test expectation を implementation output に合わせない。
- behavior change には direct regression と sibling case を用意する。
- unscoped / potentially heavy suite を、resource characteristic を確認せず実行しない。
- test command の安全性が不明なら、先に current test inventory と resource profile を調べる。
- full verification は focused checks の代わりではなく、focused checks 後の別 gate とする。

### 12.2 historical incident

現行 `CLAUDE.md` の `infer` memory incident は yulang2 の特定 crate / test 名に依存し、現在の workspace member には `infer` crate が存在しない。したがって次の形で保存する。

- exact date、command、RSS、root cause、fix commit、lesson を incident record に残す。
- file 冒頭に `Historical yulang2 incident; not an active yulang3 command policy` と明記する。
- old skip list を current agent prompt または `rules/testing.md` へコピーしない。
- current yulang3 に同種事故が出た場合は、新 incident と current mitigation を別記録する。

### 12.3 safe verifier

`cargo xtask verify <scope>` のような safe entrypoint は有望だが、この migration では実装しない。必要な test matrix、thread limit、resource guard、CI との関係を別 Authoritative design で決める。

## 13. design and task indexes

### 13.1 `notes/design/INDEX.md`

INDEX は design の要約を正本化しない。次だけを持つ。

- document path。
- status。
- authority scope。
- approved date。
- supersedes / superseded-by。
- relevant section locator。
- active / completed gate。

巨大 design document を毎 task 全文読む代わりに、INDEX から該当 document / section へ移動する。INDEX が本文と衝突した場合は本文が勝つ。

initial entries:

- `docs/yulang3-architecture.md`。
- `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`。
- `notes/design/2026-08-20-phase2-parser-fixture-schema.md`。
- `notes/design/2026-08-30-declaration-module-split-plan.md`（completed）。
- 本 migration plan。

### 13.2 `tasks/current.md`

migration 中は既存内容を変更しない。別 follow-up で次の contract へ整理する。

`tasks/current.md` に残すもの:

- current objective。
- authoritative design / section。
- active gate。
- immediate next action。
- blockers / decision points。
- known residuals。

完了 gate、長い commit history、過去の test count、詳細な review chronology は `notes/progress/` へ移す。目標は navigation file であり、historical ledger ではない。

## 14. actual migration commit plan

plan approval 後、当時の最新 `yulang3` HEAD から `codex-only-orchestration` branch を新しく切る。この plan branch を実装 branch として継続しない。

### Commit 1 — Extract durable rules and indexes

追加:

- `rules/INDEX.md`。
- `rules/design-authority.md`。
- `rules/workflow.md`。
- `rules/compiler-engineering.md`。
- `rules/parser-chasa.md`。
- `rules/bug-fixing.md`。
- `rules/performance.md`。
- `rules/testing.md`。
- `rules/documentation.md`。
- `rules/git-concurrency.md`。
- `rules/codex-quirks.md`。
- `notes/design/INDEX.md`。
- `notes/incidents/README.md`。
- `notes/incidents/yulang2-infer-test-memory.md`。

この commit では active policy を切り替えない。現行文書から durable knowledge を移し、欠落を review できる状態にする。

### Commit 2 — Add Codex-native role configuration

追加:

- `.codex/config.toml`。
- 七つの `.codex/agents/*.toml`。
- `rules/agent-orchestration.md`。

設定:

- primary: Sol / high。
- max concurrent read-only review: 6。
- default subagent: Terra / medium。
- role-specific model / effort / sandbox は各 TOML が上書きする。
- hooks は作らない。

### Commit 3 — Switch active policy atomically

変更:

- root `AGENTS.md` を compact map + communication contract に再構成。
- `CLAUDE.md` を削除。
- `.claude/` を削除。

この commit 以後、新しい role / rule topology だけが active policy となる。

### Commit 4 — Residual reference and compatibility audit

active files に対して次を監査する。

- `CLAUDE.md` への live link。
- `Claude must`、`Codex MCP first`、`Fable 5 unavailable` 等の active instruction。
- Level 1–4 / Sol-Terra-Luna tier による live routing。
- subagent commit / push instruction。
- model signature を authority 条件とする文言。

historical design provenance、progress note、commit message、incident record は機械的に書き換えない。必要な場合は `rules/design-authority.md` の compatibility section で吸収する。

### Separate follow-ups

以下は migration PR に混ぜない。

1. `tasks/current.md` の navigation 化。
2. `cargo xtask verify` safe runner。
3. CI への focused test / nightly test 追加。
4. resource monitor / hook。
5. design INDEX の精密 section locator 整備。

## 15. validation

migration PR は少なくとも次を確認する。

### 15.1 scope

- `crates/`、`benchmarks/`、`web/` の製品 code / prose diff がない。
- `Cargo.toml`、`Cargo.lock` の変更がない。
- test expectation、fixture、snapshot の変更がない。

### 15.2 configuration

- `.codex/config.toml` と agent TOML が parse 可能。
- role 名、sandbox、model、effort が target matrix と一致。
- reviewer が read-only、`implementer` / `docs_writer` だけが write-enabled。
- hooks が存在しない。

### 15.3 policy references

active root / `rules/` / `.codex/` を検索し、次が live instruction として残っていないことを確認する。

- `CLAUDE.md`。
- `Codex MCP first`。
- `Claude must`。
- `著者: Claude` を authority condition とする文言。
- `Level 1`–`Level 4` model routing。
- subagent による stage / commit / push。

歴史記録内の一致は失敗にしない。

### 15.4 repository baseline

policy-only migration だが、意図しない repository effect がないことを示すため、可能なら次を実行する。

```text
cargo fmt --check
cargo xtask check-graph
cargo check --workspace
```

full test は migration の correctness signal を増やさず、現在は安全な共通 entrypoint も未設計なので必須にしない。

## 16. rollback

migration は policy / configuration / documentation だけなので、merge commit または migration commits の revert で戻せる。旧 `AGENTS.md`、`CLAUDE.md`、`.claude/` は Git history に残る。rollback のための duplicate file を working tree に保持しない。

## 17. completion condition

次をすべて満たした時点で Codex-only migration 完了とする。

1. root `AGENTS.md` が map と user-visible communication contract に限定されている。
2. 七 specialist role が project-scoped config として定義されている。
3. design authority が user approval を根拠としている。
4. durable engineering policy が `rules/` に分離されている。
5. yulang2 incident が active yulang3 command policy から分離されている。
6. `CLAUDE.md` と `.claude/` が active tree から退役している。
7. active policy に Claude→Codex MCP plumbing または legacy model routing が残っていない。
8. compiler behavior、tests、public docs content に変更がない。
9. independent review と validation を通過している。
