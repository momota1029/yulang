# RCPF-E 追補: claimed attribution の source-partitioned union と A1 preflight の event-local ordering

日付: 2026-08-05

状態: **ユーザ承認済み（2026-08-05）**

著者: Claude (Sonnet 5)、Codex `gpt-5.6-sol`（xhigh）の調査・設計提案に基づき統合・記述。

**署名についての注記**: このリポジトリの正本文書は通常 Claude (Fable 5) が起案する
慣習だが、[[2026-08-01-dpn-root-claim-and-cycle-safety-addendum]] 以降の一連の
追補と同様の理由（Fable 5 が一時的に利用できない状況）により、本書も Codex Sol
XHigh の調査・設計提案を Claude (Sonnet 5、本セッションの監督エージェント) が
検証・統合して文書化した。

本書は `notes/design/2026-08-02-replay-claim-parent-factorization.md`
（以下 RCPF 文書）§11 の RCPF-E（clause-link consumer の production cutover）に
ついて、実装スライス2（production cutover 本体）で発見された2つの意味論的
ギャップを埋める追補である。RCPF 文書の中核決定・23 invariant・16 stop
condition を改廃するものではなく、E の実装可能性を回復するための **attribution
の分類方法** と **A1 preflight の読み取りタイミング** の2点だけを補う。

## 0. 本書が下す決定の要約

1. `SchemeProjectionProofSupport::Claimed(claim)` の attribution は、書き込み側
   （writer boundary）で「canonical replay parent 由来」と「Original /
   structural / reduction / evidence 由来」の2系統へ分類し、別々の集合へ記録
   する。読み取り側（read-time）でのkind dispatchは、root canonicalization が
   provenance を消去しているため不可能——これは実装できない案として棄却する。
2. `Factored` authority 下の claimed attribution 判定は、上記2集合の union
   （`replay_attributed(record, root) OR flat_retained_attributed(record,
   root)`）とする。`LegacyRollback` authority 下は現行の all-source flat
   集合をそのまま使う（oracle として維持）。
3. A1 preflight（`register_claim_parent_clause_links_mutation` 経路の
   already-registered 判定）は、その admission event が始まる前の安定した
   pre-event view に対して行う。同一 event の Phase B（factored occurrence /
   parent-set / clause projection / attribution の commit）を先取りして
   読んではならない。
4. Factored A1 の読み取りが失敗した場合でも、Phase A（legacy flat
   mutation）は無条件に実行される——RCPF-D addendum §3.3 で確立した
   「Phase A は常に無条件」規律をそのまま維持する。factored 側の失敗は
   attempt を terminal 化し、Phase B 以降・evaluation・publication を
   スキップして `LegacyRollback` で clean retry するだけであり、Phase A
   自体をスキップしてはならない（stashed WIP の実際のバグはここにあった）。
5. RCPF-E の production cutover 着手前提として、5 source（Original /
   ReplayConstraint / ReplayEvidence / StructuralConstraint /
   ReductionRouteConstraint）を横断する attribution matrix test と、
   Factored / LegacyRollback 間の parity oracle を追加し、green にする。

## 1. 背景

RCPF-E slice 1（`9e580410`、factored clause-link read adapter追加、挙動
中立）は安全に着地した。続く slice 2（production cutover 本体）の実装中、
scoped `constraints::` test で既知4件を超える23件の新規 failure が発生し、
安全側に停止した（Codex `gpt-5.6-sol` xhigh、2026-08-05）。壊れた WIP は
`git stash`（`stash@{0}`、メッセージ "WIP RCPF-E slice 2: blocked on
claimed-attribution routing and A1 factored authority-view stabilization
gaps"）として保存され、production コードには一切影響していない。HEAD は
`9e580410` のまま。

続く読み取り専用の深掘り調査（Codex `gpt-5.6-sol` xhigh）で、23件の failure
は独立した23個の意味論バグではなく、2つの機構的な原因に collapse することが
判明した。

## 2. Gap 1: claimed attribution の source 分類

### 2.1 調査結果

production には `UpperReplayClaimLineage` が5種類存在する。

```text
Original
ReplayConstraint       (canonical replay claim parent 由来)
ReplayEvidence
StructuralConstraint
ReductionRouteConstraint
```

これらが `RecordProofClause` へ写像される経路は次の通り。

```text
Original                  -> Standalone
canonical replay claim parent -> ReplayConjunction
StructuralConstraint       -> DerivedUnary(Structural)
ReductionRouteConstraint   -> DerivedUnary(ReductionRoute)
ReplayEvidence             -> ReplayConjunction
```

`SchemeProjectionProofSupport::Claimed(claim)` は読み取り時に `claim` を
`canonical_coverage_root` へ正規化してから attribution を問い合わせる。この
正規化は provenance を消去する——正規化後の root だけからは、元の claim が
`Original` だったのか `ReplayEvidence` だったのかを復元できない。また
`ReplayEvidence` と canonical replay claim parent はどちらも `ReplayConjunction`
という同じ clause 形状を経由するため、clause 形状からの逆算も不可能。

したがって「読み取り側で kind に応じて factored/flat を出し分ける」という
案（当初 slice 2 が暗黙に前提していた設計）は成立しない。stashed WIP が
factored 側で `Ok(true)`（fail-open/projectable）、legacy 側で `Ok(false)`
と食い違ったのは、`ReplayClauseProjection::replay_attributed_claim_supports`
が canonical replay-occurrence 由来の attribution しか保持しておらず、
Original / structural / reduction / evidence 由来の link が factored 側から
単純に消えていたためである。

### 2.2 決定した設計

分類は読み取り時ではなく **writer boundary** で行う。

- `ReplayClauseProjection::replay_attributed_claim_supports`
  （既存、変更なし）: canonical replay parent 由来の attribution のみを持つ。
- 新設: flat-retained attribution summary。Original / structural /
  reduction / evidence 由来の attribution を保持する（保持先の具体的な
  データ構造——既存 `attributed_claim_supports` の部分集合ビューとするか
  新規集合とするか——は実装スライスで決定してよい。本書が固定するのは
  「この4 source は factored replay summary に混ぜない」という分類方針の
  みである）。

`Factored` authority 下での claimed attribution 判定:

```text
replay_attributed(record, root) OR flat_retained_attributed(record, root)
```

`LegacyRollback` authority 下は現行の all-source flat
`TypeBounds::attributed_claim_supports` をそのまま使う。

E の間（本 addendum のスライスが green になるまで）は、この
all-source flat 集合を oracle として維持し、次を要求する。

```text
legacy all-source attribution == replay attribution ∪ flat-retained attribution
```

### 2.3 invariant への影響

- exact clause/link identity は変更しない。
- attribution は既存の existential `(record, root)` 問い合わせのままで、
  新しい runtime provenance tag や公開 API 変更を必要としない。
- evidence は `ReplayOccurrenceStore` / result summary / canonical claim-parent
  relation へは入らない——RCPF 文書 §7.8 の禁止事項はそのまま維持される。
  §7.10 の「source-neutral facade」は、flat-retained 側を追加した union
  として実現する。

### 2.4 文書上の明確化（弱化ではない）

- §6.9 / §8.5: claimed attribution の consumer view は「replay-factored と
  flat-retained の union」であると明記する。
- §7.8: 禁止対象は replay occurrence / result summary へ evidence を
  混入させないことであり、flat-retained 側（source-neutral facade の
  非 replay 半分）に evidence が寄与すること自体は禁止されていない、と
  明確化する。

## 3. Gap 2: A1 preflight の authority-view 安定化

### 3.1 調査結果

`ReplayAdmissionPublicationFence` は「既に評価済みの publication intent」の
外部公開を遅延させる機構であり、**評価に使う入力の読み取りタイミングは
制御していない**。stashed WIP のパニックは次の順序不整合が原因だった。

```text
Phase A: flat link mutation を commit
   ↓（factored projection はまだ commit されていない）
after-evaluation が Factored attribution/link view を読む
   ↓
"clause-link batch preflight must agree with exact-key insertion" で矛盾
```

RCPF-D addendum の Phase A/B/C 順序規律（Phase A = legacy、常に無条件 /
Phase B = factored commit + health / Phase C = factored 依存の derived
mutation、health 成功時のみ）はこの問題の前例だが、E の A1 preflight は
その規律が適用される前——同一 event の Phase B 完了より前——に factored
view を読んでしまっていた。

さらに、stashed WIP の failure path 自体にもバグがあった。Factored A1 の
読み取りが失敗した場合に Phase A へ進む前に return してしまっており、
「Phase A は常に無条件」という既存規律に違反していた。

### 3.2 決定した設計

A1 preflight は、その admission event が始まる前の **安定した pre-event
view** に対して行う。新しい event で初めて追加される link は、この
pre-event view では当然「不在」と判定されて構わない（それが正しい
already-registered = false の判定である）。

event 処理の順序:

```text
1. A1 を pre-event view（attempt に latch された authority）に対して実行
2. Phase A: legacy flat mutation を常に無条件で commit
3. 評価前の ClauseLinkBatchAdmissionSnapshot を（未評価のまま）保持
4. Phase B: factored occurrence / parent-set / clause projection /
   attribution を commit
5. Phase B が成功した場合のみ、保持していた snapshot を「封印」する:
   a. after-view の clause-link 評価を実行
   b. 評価結果を publication intent へ変換
   c. 既存 publication fence へ append
6. Phase C（factored 依存の derived mutation）、oracle 照合、publication
   を継続
```

API 設計として、この順序を誤用しにくい形にする——たとえば「未評価の
pending snapshot」を、Phase B 成功後にのみ呼び出せる専用の sealing
関数だけが消費できるようにする、といった形。具体的な型/関数分割は
実装スライスの裁量とする。

### 3.3 Factored A1 失敗時の挙動

Factored A1 の読み取りが失敗した場合:

- attempt を terminal failed として mark する
  （既存 quarantine addendum §3.2 の規律に従う）。
- **Phase A の legacy flat mutation は無条件に実行する**——failed attempt
  の legacy/oracle state を保全するためであり、これをスキップしてはならない。
- Phase B 由来の derived work・after-evaluation・publication はスキップする。
- machine を破棄し、`LegacyRollback` authority で clean retry する。

これは fail-open でも production authority の混在でもない——failed attempt
から生き残る出力は存在しない（quarantine addendum §3.2 の「terminal failed
attempt は丸ごと破棄」がそのまま適用される）。stashed WIP はこの点を
誤っており、Phase A 自体を条件付きにしてしまっていた。

### 3.4 test infrastructure の是正

新規 failure の一部は、`#[cfg(test)]` の legacy-only replay admission
helper が、authority がデフォルトで `Factored` な machine 上で呼ばれていた
ことに起因する mixed state だった。これは以前は clause-link consumer が
まだ flat storage を読んでいたため許容されていたが、E がこの前提を崩した。

- legacy-only replay helper は `LegacyRollback` authority を要求するよう
  変更する。
- factored fixture は、既存の完全な dual-write admission helper を使う。

これは production 挙動の変更ではなく、test fixture が RCPF-C 以降ずっと
要求されていた authority 一貫性（quarantine addendum §3.4「粒度は
compilation attempt 単位」）に追いついていなかった穴を塞ぐものである。

## 4. invariant / stop condition との整合性

RCPF 文書 §10 の23 invariant、quarantine addendum の attempt-level
authority 規律、D addendum の Phase A/B/C 順序規律について、以下の観点で
照合した。

- **invariant 2（等価性が任意の到達可能状態で成立する、という文言）**:
  既に承認済みの D の Phase A/B 設計自体が、factored commit 前の
  transaction-local な中間状態を一時的に持つ。本書はこの既存の解釈——
  「等価性は complete event boundary と全ての consumer-visible view で
  成立する」という意味であり、命令単位の全ての中間状態を指すものではない
  ——を明文で再確認するに留め、新たな解釈を導入しない。もし「任意の
  到達可能状態」を命令単位の意味で厳密に取るべきだという判断があれば、
  それは D の既存設計自体の再検討を要する別問題であり、本書の範囲外として
  ユーザーの判断を仰ぐ。
- **exact carrier identity・legacy/factored exact relation equivalence**:
  変更しない。attribution 分類はexact link の identity を変えない、
  どちらの集合に属するかを分けるだけ。
- **stop condition #4（exact-link mismatch）**: 分類は書き込み側で
  一意に決まる（writer boundary で tag するため）。同一 exact link が
  複数 source から矛盾した分類で登録される事態は oracle mismatch として
  検出し、静かに分類を変更しない（§2.2 の union は「両方の集合を
  OR で見る」だけであり、分類の優先順位や上書きを持ち込まない）。
- **stop condition #5（confirmed-path fail-open）**: A1 の失敗時は
  attempt 全体を terminal 化して retry するのみで、`projectable = true`
  への吸収は行わない（quarantine addendum §3.3 と同じ）。
- **stop condition #7（mixed before/after view）**: A1 は event 開始前の
  pre-event view に固定し、同一 event の Phase B 結果を先取りしない。
- **stop condition #9（exact no-op での allocation/publication）**:
  pre-event view による A1 は、新規性の無い重複 event で余分な allocation
  を発生させない（既存の already-registered 判定をそのまま保つ）。
- **stop condition #14（pinned expectation の変更）**: 本書のスライスは
  既知4件以外の pinned test 期待値を変更しない。

## 5. 実装スコープの粗見積り

Codex の調査時点での粗見積り（実装スライスで精密化してよい）。

- Gap 1（attribution 分類）: 約260〜450行（テスト含む）。
  `crates/infer/src/constraints/mod.rs`、
  `crates/infer/src/constraints/machine/bounds.rs`、
  `crates/infer/src/constraints/replay_factored.rs`。
- Gap 2（A1 event-local ordering）: 約300〜550行（テスト含む）。
  主に `crates/infer/src/constraints/machine/bounds.rs` と
  `crates/infer/src/constraints/mod.rs`。追加で必要になる機構は
  scoped されたこれらのファイル内に収まる見込みで、RCPF-E の scope 外
  （他の crate や他のsubsystem）への波及は調査時点で確認されていない。

## 6. 実装スライス（提案）

1. **E2a**: writer boundary での attribution 分類（Gap 1 の書き込み側）。
   flat-retained summary の追加、5-source attribution matrix test の追加。
   production cutover はまだ行わない（挙動中立、既存 legacy 経路を維持）。
2. **E2b**: Factored/LegacyRollback union の read 経路実装 + oracle
   （legacy all-source == replay ∪ flat-retained）を green にする。
3. **E2c**: A1 の pre-event view 化（Gap 2 の読み取りタイミング是正）+
   snapshot sealing の Phase B 後移動。
4. **E2d**: Factored A1 失敗時の Phase A 無条件維持の是正 + test
   infrastructure の authority 一貫性是正（§3.4）。
5. **E2e**: production cutover 本体——`support_has_clause_link` /
   `flat_fail_open` の読み取りを factored 経路へ切り替える。E2a〜E2d が
   全て green であることを前提とする。

各スライスは既存の long-task slicing policy に従い、
`cargo test -p infer --lib constraints:: -- --test-threads=4`
（既知4件のみが残ることを確認）を都度実行してから commit する。

## 7. 波及する文書（本書 landing 後に更新。本書では編集しない）

- `notes/design/2026-08-02-replay-claim-parent-factorization.md`
  （RCPF 文書）: §11 の RCPF-E 節に、本書への参照と E2a〜E2e のスライス
  構成を追記する。

---

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査・設計提案を統合）

ユーザ承認済み（2026-08-05）。本書は設計判断の正本として扱う。
RCPF 文書 §11 の RCPF-E 節の実装は本書 §6 の E2a〜E2e スライスに従って
着手してよい。
