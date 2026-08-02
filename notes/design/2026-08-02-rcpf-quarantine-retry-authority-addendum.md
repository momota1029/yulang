# RCPF 追補: factored replay quarantine 時の production authority

日付: 2026-08-02

状態: **ユーザ承認済み（2026-08-02）**

著者: Claude (Sonnet 5)、Codex `gpt-5.6-sol`（xhigh）の調査・設計提案に基づき統合・記述。

**署名についての注記**: このリポジトリの正本文書は通常 Claude (Fable 5) が起案する
慣習だが、[[2026-08-01-dpn-root-claim-and-cycle-safety-addendum]] と同様の理由
（Fable 5 が一時的に利用できない状況）により、本書も Codex Sol XHigh の調査・
設計提案を Claude (Sonnet 5、本セッションの監督エージェント) が検証・統合して
文書化した。

本書は `notes/design/2026-08-02-replay-claim-parent-factorization.md`
（以下 RCPF 文書）の未決定事項——RCPF-C 以降、production consumer が
factored representation の quarantine（`ReplayFactoredShadowStatus::Failed`）
にどう応答すべきか——を埋める追補である。RCPF 文書の中核決定（§6 の抽象モデル、
§7 の admission algorithm、§10 の 23 invariant、§11 の段階的移行計画）を
改廃するものではなく、**quarantine 発生時の production authority の選び方**
という一点だけを補う。

## 0. 本書が下す決定の要約

1. RCPF-C〜E では、1 回の compilation attempt（1 つの `ConstraintMachine` /
   `TypeBounds` の lifetime）に対して replay read authority を **1 つだけ**選ぶ。
   `Factored`（通常経路）と `LegacyRollback(reason)`（quarantine 後の再実行）の
   二択で、同一 attempt 内でクエリ単位・レコード単位に混在させない。
2. `ReplayFactoredShadowStatus::Failed(reason)` が発生した attempt は
   **terminal failed attempt** として扱い、その attempt が生成した
   scheme・projectability・diagnostic・epoch/cache publication を一切外部へ
   commit せず破棄する。compilation unit を新しい machine で
   `LegacyRollback` authority に固定して clean retry する。
3. retry を提供できない呼び出し環境では hard compilation error とする。
   `Failed` を `projectable = true` 側へ吸収する fail-open は行わない。
4. RCPF-F（legacy ledger 物理撤去）の着手前提に、
   「C〜E soak 期間中の organic `Failed` 発生数がゼロだったこと」を追加する。
   F 着地後は factored write/read failure を hard error とする。

## 1. 背景

RCPF-A（`b21c62ab`〜`0136c434`）は factored writer を panic-free 化し、
書き込み経路の失敗は全て `ReplayFactoredResult<T> = Result<T,
ReplayFactoredShadowFailure>` で表現される。失敗時は
`replay_factored_shadow_status` が `Failed(reason)` へ遷移し、この quarantine
はその compilation の残り全体について恒久的である（un-quarantine 経路は無い）。

RCPF-B（`0136c434`〜`061af82b`）は factored representation
（`ParentSetArena` / `ReplayOccurrenceStore` / `ReplayResultSummary` /
`ReplayClauseProjection`）を legacy flat ledger（`claim_parents_by_constraint`）
と並走して dual-write し、B3 はこの 2 つの一致を検査する opt-in event-boundary
oracle を追加した。ここまでは shadow-only であり、`Failed` は shadow の
帳簿処理を止めるだけで、production の正しさには一切影響しない。

RCPF-C（未着手）は `eval_constraint_uncached` の replay source を legacy flat
iterator から `ReplayOccurrenceStore::by_result` / `occurrence()` へ切り替える
production direct cutover である。この切替後、初めて `Failed` が production
の結果に影響しうる状態になる。RCPF 文書 §11 の C/D/E それぞれの記述は
「legacy adapter へ戻せる」という **slice rollback**（実装のロールバック）を
述べているが、**runtime での record 単位 fallback**（同一 compilation 内で
一部は factored、一部は legacy で評価を続ける）を承認しているわけではない。
この区別が本書の主題である。

## 2. なぜ record 単位 fallback が採れないか

`Failed` は「該当 query の値が単に無い」という意味ではない。
allocation failure・parent-set/occurrence store の corruption・legacy との
oracle mismatch のいずれかを含み、いずれの場合も **quarantine が検出される
以前に factored 側へ書かれた内容の完全性を保証できない**。mismatch の場合は
特に、「検出された時点より前の factored read は正しかった」と仮定する根拠が
存在しない。

さらに、現在の実装では legacy admission とその publication の後に shadow
observer が走る（A4 の atomic mutation batch の後段）。record 単位 fallback を
安全に行うには、factored の commit と health/oracle 判定を production の
after-view 公開より前に完了させる必要があるが、そうしたとしても
「同一 attempt 内で一部の record は factored 権威、別の record は legacy
権威」という状態は、RCPF §10 の複数 invariant（exact equivalence 前提、
snapshot/view 契約、insertion-order invariance）を弱めずには成立しない。

したがって、fallback の粒度は record/query 単位ではなく、
**compilation attempt 単位**でなければならない。

## 3. 決定の詳細

### 3.1 Authority の型

```text
ReplayReadAuthority =
    Factored
  | LegacyRollback(failure_reason)
```

通常の attempt は `Factored` authority で開始する。RCPF-C〜E の evaluator・
upper claim materialization・projection・clause-link・attribution・exact
membership・portable adapter は、同一 attempt 内で同じ authority を使う。

### 3.2 Quarantine 発生時の挙動

`ReplayFactoredShadowStatus::Failed(reason)` が発生した machine は
terminal failed attempt となる。

- その machine から得られた factored evaluation・round・before/after
  comparison の結果を破棄する。
- scheme・projectability・diagnostic・epoch/cache publication を外部へ
  commit しない。
- compilation unit を新しい machine で最初から再実行する。
- retry は `LegacyRollback(reason)` authority に固定し、RCPF-C〜E の
  全 replay consumer を既存 legacy adapter へ戻す。
- retry 中は factored writer/oracle を無効化し、同じ failure を再発させない。
- clean retry を提供できない呼び出し環境（retry コストが許容できない、
  machine を再構築する経路が無い等）では hard compilation error とする。

同じ machine の途中から authority を切り替えることはしない。過去に
factored data から得た memo・inclusion decision・generalization cache・
diagnostic input を個別に探して無効化する repair pass も導入しない
（failed machine を丸ごと破棄すれば repair 自体が不要になる）。

### 3.3 Failure detection の境界

factored writer・summary・clause projection・oracle の failure 判定は、
該当 admission event の factored state を production consumer へ見せる前に
完了させる。正常な event の順序は次のようになる。

```text
before round（直前の完全な state に対する評価）
factored preflight/commit
factored health/oracle 判定
after round（新しい完全な state に対する評価）
epoch/cache publication
```

factored commit または health 判定が失敗した場合、after round と
publication へは進まず、attempt 全体を中止する。

`SchemeProjectionEvaluator` 自体も、一部の occurrence を factored で評価した
後に局所的に legacy iterator へ継続してはならない。factored query API が
corruption/error を返した場合、top-level query 全体を `Err` とし、attempt
rollback を要求する。bool の `true`（projectable）へ吸収してはならない。

### 3.4 粒度

authority は query 単位・record 単位ではなく、compilation attempt 単位で
固定する。evaluation round はその authority を構築時に latch し、同一 round
内で authority を再確認・変更しない。before/after は従来どおり別 round と
するが、同一 attempt の authority は共通とする。

これにより、factored を読んだ partial compilation に対する遡及的な memo
invalidation は不要になる。failed attempt の round-local memo・machine-local
cache・epoch state は machine ごと破棄される。

### 3.5 RCPF-C〜E の landing policy

legacy retry は correctness recovery であり、RCPF gate の成功としては
数えない。confirmed workload で自然発生（fault injection ではない）した
`Failed` は、legacy retry によって最終出力が正しくなっても RCPF slice の
failure として記録し、原因を修正するまで次 stage へ進まない。

通常の production path は factored の direct read であり、query 単位の
production dual-read を恒常的に維持するものではない（B1〜B3 の shadow
dual-write とは別物である——shadow dual-write は quarantine 検出のために
残り続けるが、production の読み取り経路自体は authority 一本化される）。

### 3.6 RCPF-F の追加前提条件

F の着手前提に、最後の writer/consumer 変更後に実施した C〜E soak 期間に
ついて、次を要求する。

```text
organic ReplayFactoredShadowStatus::Failed 発生数 == 0
legacy rollback retry 発生数 == 0
unexplained factored read error 発生数 == 0
```

対象ワークロードには full infer test、pinned test、cache on/off、
insertion-order 系 fixture、std lowering、portable provenance 系
characterization、wall-time/RSS 計測ワークロードを含める。failure が
見つかった場合は原因を修正した上で soak を最初から取り直す。

この gate は必要条件であって、将来の allocation failure や corruption が
構造的に不可能であることまでは証明しない。F 着地後（legacy ledger と
adapter を物理削除した後）は、factored write/read failure を hard
compilation error として扱う。この段階では legacy retry という代替手段が
存在しないため、fail-open 方向への逃げ道は無い。

### 3.7 Fail-open との関係

本書の legacy retry は、MPC/DPN の `projectable = true` fail-open とは
異なる。不完全な factored metadata から projectability を肯定的に推測する
ものではなく、**完全な legacy relation を通常の評価規則で再実行する
representation rollback** である。

§8.5 の metadata fail-open を `ReplayFactoredShadowStatus::Failed` の処理に
流用しない。retry が行えない場合は hard error とし、confirmed path・
rejected path のいずれについても、不完全な factored metadata から
projectability を肯定しない。

## 4. Invariant / stop condition との整合性

RCPF 文書 §10 の 23 invariant、§11 の各 stage の stop condition、§12 の
性能 gate・stop condition について、以下の観点で本書の decision と照合した。

- **Exact carrier identity・legacy/factored exact relation equivalence**:
  retry は legacy exact carrier をそのまま使い、failed factored carrier から
  推測しない。
- **Consumer equivalence**: mismatch を等価と再解釈せず、`Failed` attempt を
  成功状態として継続させず破棄する。
- **Insertion-order invariance / no-claim passthrough**: retry は
  event-time の legacy snapshot を admission stream から再構築し、live
  endpoint から補修しない。同一 attempt 内で source を混在させないため、
  順序契約は legacy 側のものがそのまま適用される。
- **Diagnostic input/order 契約**: failed attempt の diagnostic を外部
  commit せず、成功した legacy retry の既存 diagnostic source/順序だけを
  公開する。
- **DPN の Record/Constraint/RootCoverage 評価規則**: 本書は Replay source
  adapter の選択だけを扱い、DPN の評価規則自体には触れない。
- **Tri-color cycle safety**: failed round の evaluator state を共有せず、
  retry は fresh evaluator から始めるため、cycle guard の規則は変わらない。
- **§11.1 の stop condition（confirmed path の fail-open 含む）**:
  `Failed -> projectable` の変換を行わないため、confirmed-path fail-open は
  発火しない。authority を event/round の途中で切り替えないため、query
  順依存も導入しない。
- **§12 の性能 gate**: failed/retried run を factored correctness census の
  PASS として数えない。legacy retry は例外経路であり、RCPF-F の構造・圧縮
  gate を満たしたことにはしない。

## 5. 波及する文書（本書 landing 後に更新。本書では編集しない）

- `notes/design/2026-08-02-replay-claim-parent-factorization.md`
  （RCPF 文書）: §11 の RCPF-C/D/E 節に、production authority の選択規則
  として本書への参照を追記する。§11 の RCPF-F 節に、本書 §3.6 の soak
  前提条件を追記する。

---

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査・設計提案を統合）

ユーザ承認済み（2026-08-02）。本書は設計判断の正本として扱う。
実装は RCPF 文書 §11 の RCPF-C1〜C3 スライス（本書 §3 の反映を含む）に
従って着手してよい。
