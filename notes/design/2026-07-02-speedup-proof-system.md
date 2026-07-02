# 高速化証明系の翻訳と評価

作成日: 2026-07-02
著者: Claude (Fable 5) — ユーザの依頼「実装が独自に育てた高速化証明（plan/cert）の
oracle を、設計者が理解できる言葉に翻訳し、可能ならより速い証明を提案する」に基づく。
状態: **ユーザ承認済み（2026-07-02）**。内容は整然として採用すべきとの判断を受け、
実装指示書 [2026-07-02-static-route-promotion-plan.md](2026-07-02-static-route-promotion-plan.md)
に落とした（提案 1・2 が対象。提案 3 は VM高速化計画 Phase 3 に合流、
提案 4 は別指示書待ち）。

対象コード: `crates/evidence-vm/src/`（runtime.rs, lib.rs, runtime/stats.rs）。
参照メモ: notes/design/2026-06-30-VM高速化計画.md、
2026-06-30-evidence-vm-next-speedup-execution-plan.md、
evidence-vm-native-close-invariants.md、2026-06-30-known-state-handler-plan.md。

---

## 1. 証明系の全体像 — 四種類の主張と、一つの検証プロセス

実装が「plan」「cert」「invariant」と呼んでいるものは、整理すると
**四種類の異なる主張**に分かれる。これらは互いに独立で、組み合わせて初めて
fast path を許可する。

| # | 種類 | 主張の形 | 許可される近道 | 実装上の姿 |
|---|------|---------|--------------|-----------|
| 1 | **経路の証明** | 「この operation call は、この handler に届く」 | generic request（継続の具象化 + 探索）を省き、direct 経路に乗せる | `EvidenceRouteCert`（runtime.rs:501）: `None` / `StaticDirect` / `ProviderGrant(id)` |
| 2 | **形の証明** | 「この handler の腕は、継続 k を特定の規律でしか使わない」 | 腕の規律に応じて継続 capture 自体を省く | `EvidenceVmHandlerArmClass`（lib.rs:120）: Value / Abortive / **TailResumptive** / OneShotYield / MultiShotYield / MayEscapeYield / Fallback |
| 3 | **帳簿の証明** | 「marker close の legacy 帳簿処理を飛ばしても hygiene（衛生性）が保たれる」 | `close_marker_frame` の legacy 経路を native close に置換 | `NativeProviderPair` / `NativeProviderPrefixBoundary` / `NativeProviderEnvForeignBoundary`（runtime.rs:4318-4376、判定は provider_marker_close_decision 9455-9548） |
| 4 | **意味の証明** | 「この handler は特定の**代数**（例: state 代数）を実装している」 | 操作の意味を直接実行（get/set を runtime state frame への読み書きに置換） | `KnownHandlerPlan::State`（known-state-handler-plan 参照） |

これらを横断するのが **shadow 方式**: 候補ロジックを本実行と並走させ、
mismatch 0 を確認してから実行に昇格させる。これは証明ではなく
**証明候補の経験的検証プロセス**である（数学で言えば、予想を反例探索にかけている段階）。

重要な設計判断が一つ既に正しく行われている: known-state-handler-plan は
「type/evidence route と handler の意味の証明は**別の事実**」と明記している。
同じ row・同じ型の handler でも set を無視したり k を二回呼んだりできるから、
経路の証明（#1）だけでは意味の直接実行（#4）を正当化できない。
この分離は保存すべき骨格である。

## 2. Koka との対応 — 何を輸入し、何がずれているか

参照論文系譜: Xie & Leijen, *Effect Handlers, Evidently* (ICFP 2020) /
*Generalized Evidence Passing* (ICFP 2021)。Koka の高速化は二本柱:

1. **evidence passing**: handler の探索を実行時にやらない。関数は自分が使う
   effect の evidence（handler への参照 + marker）を**ベクタで受け取り**、
   operation は O(1) で自分の handler を引く。
2. **tail-resumptive 最適化**: handler の腕が「k を末尾で一回だけ呼ぶ」形
   （`op(x, k) -> k e` で e が k を含まない）なら、継続を capture せず
   **その場で関数呼び出しとして実行してよい**、という定理。Koka の計測では
   実用コードの operation の大半がこの形。

Yulang の evidence VM は名前どおりこの系譜を意図している。対応表:

| Koka | Yulang 実装 | 位置 |
|------|------------|------|
| evidence vector | `EvidenceProviderGrant`（demand_slot/provider_slot/handler_id/scope_id/hygiene_baseline） | runtime.rs:529-546 |
| marker（handler 一意性） | `EvidenceValueMarker`（Frame/AddId）+ marker plan | runtime.rs:642 付近 |
| tail-resumptive 判定 | `EvidenceVmHandlerArmClass::TailResumptive` → `EvidenceDirectTailResumptive` signal | lib.rs:120 / runtime.rs:4580 |
| （Koka にない）handler 衛生性 | `EvidenceSignalHygiene`（guard_ids / handler_boundary / permission_visibility） | runtime.rs:3951 付近 |

**ずれの本質**: Koka はこの分類と evidence 解決を**コンパイル時に**行い、
生成コードには検査が残らない。Yulang は同じ分類を持っているのに、
その正当性確認を**実行時の cert 発行 + gate 検査**（`provider_grant_gate_passes`、
runtime.rs:8378 付近）として払っている。さらに Yulang 固有の衛生性
（handler 汚染防止、2026-05 の衛生性事件の再発防止）が gate 条件に編み込まれて
いるため、検査が Koka より重い。

つまり現状は「**Koka が静的に済ませる証明を、動的に毎回再演している**」状態。
これは間違いではなく、意味論が動いていた時期の正しい安全策だった。
しかし意味論が固まりつつある今、証明の置き場所を動かせる。

## 3. 各 cert の定理形式への言い換え

実装内部語彙を、主張・条件・結論の形に翻訳する。

### 3.1 EvidenceRouteCert::ProviderGrant

> **主張**: operation call c の時点で、provider env に grant g が
> unshadowed で存在するならば、c は g.handler_id の handler に届く。
> **条件検査**（gate、実行時・signal 毎）: scope_id が active であること、
> hygiene_baseline（marker_plan_len / active_add_id_len / active_handler_frame_len）
> 以降に遮蔽が積まれていないこと。
> **結論**: generic request を作らず direct 経路（DirectTailResumptive /
> DirectAbortive / routed yield）へ。

dirty になる理由は counter で分類されている
（`route_cert_provider_grant_dirty_scope / add_id / handler / missing`）。
baseline 比較による遮蔽検出は堅実な設計で、意味論的に一般化する（質 B、§4）。

### 3.2 EvidenceVmHandlerArmClass（形の証明）

> **主張**（TailResumptive の場合）: 腕の本体が `k e`（e は k 非含有・末尾位置）
> であるならば、operation は「handler 側の関数をその場で呼んで戻る」ことと
> 観測等価である。継続の具象化・unwinding・再構築は不要。

これは Koka の定理そのもので、**分類は lowering 時に静的に済んでいる**。
7 値分類（Value / Abortive / TailResumptive / OneShotYield / MultiShotYield /
MayEscapeYield / Fallback）は Koka の 2 値（tail-resumptive か否か）より細かく、
将来の最適化（OneShotYield = Bruggeman の move 最適化対象）の受け皿として良い設計。

### 3.3 Native close 三兄弟（帳簿の証明）

> **主張**（NativeProviderPair の場合）: DirectTailResumptive signal s が
> provider guard-boundary permission を運び、resume_plan に handler_path がなく、
> marker slice に carry-after-frame AddId がなく、legacy bridge でも
> resume delta でもないならば、`close_marker_frame` の legacy 処理を
> 省略した close は legacy close と観測等価である。

Prefix / EnvForeignBoundary はこの主張の handler_path あり版・foreign-family 版で、
条件が 6〜11 項目に増える。**注意すべき点**: EnvForeignBoundary の条件には
「nearest ProviderEnv が Then の第一枝の深さ 1 にある」という項目が含まれる。
これは nondet/showcase という代表ワークロードの**観察された木の形**であって、
意味論からの帰結ではない（§4 の質 C）。

### 3.4 KnownHandlerPlan::State（意味の証明）

> **主張**: handler h が state 代数
> `get(), k -> run(state, k(state))` / `set(new), k -> run(new, k(()))`
> の形（1 状態引数、1 計算引数、単一衛生 family、guard なし、k を
> ちょうど一回・非エスケープで使用、同一 handler への再入）であるならば、
> h の下の get/set は runtime state frame への読み書きと観測等価であり、
> 継続 capture 時は frame を snapshot/fork すればよい。

これは四種の中で最も強い形の証明（handler の**意味**まで特定する）で、
2 秒 → 数 ms 級の獲物（`for` + local ref の破滅的経路）を狙う。
snapshot/fork 意味論は state の純粋継続スレッディング
（[[project_state_purity]]）と一致しており、健全性の根拠が明快。

## 4. 評価 — 証明の「質」は三段階ある

この oracle の証明たちは、健全性の**根拠の由来**で三つに分けられる。

- **質 A（意味論的）**: 主張が言語の意味論から一般に成り立つ。
  arm 分類（3.2）、state 代数証明（3.4）、grant gate の遮蔽検出（3.1）。
  新しいワークロードでもそのまま正しい。
- **質 B（構造的）**: 主張は一般に成り立つが、確認を実行時に払っている。
  route cert の gate 検査、shadow 方式全般。正しいが、検査コストが利得を削る。
- **質 C（観察的）**: 代表ワークロードで観察された形をそのまま条件に昇格した。
  native close の「Then 第一枝・深さ 1」条項、foreign-family の半々分布に
  依存した分岐設計。**健全ではある**（条件を毎回検査して外れたら fallback
  するから）が、(i) 一般化せず coverage が新ワークロードで崩れる、
  (ii) 条件リストが長く検査自体が高い、(iii) 条件の「なぜ」が意味論に
  接地していないため、変更のたびに shadow phase をやり直すしかない。

**病理の命名**: この oracle の弱点は不健全性ではなく、
**「観察の不変条件への昇格」が証明を重く・脆くしていること**である。
実例は文書に既に残っている——duplicate marker scope skip は counter を半減させて
実時間を悪化させ、later-grant native close は visible-compatible なのに遅かった。
どちらも「検査と表現のコスト」が「省いた仕事」を食った例で、
cert の条件が長くなるほどこの逆転は起きやすい。

もう一つの構造的観察: 質 C の cert 群（native close 三兄弟）が塞いでいる穴は、
すべて「**継続の木に marker/provider が経路依存の形で積まれている**」ことに
由来する。木の形が単純なら（= delta が事前計算されていれば）、
これらの cert は不要になる。つまり三兄弟は、木構造 runtime の**症状**への
対症療法であり、VM高速化計画 Phase 3（MarkerDelta / ProviderDelta sidecar）が
根治に相当する。この診断は既存計画と一致しており、計画の優先順位は正しい。

## 5. 提案 — より速い証明へ

中心命題:

> **一番速い証明は、実行時に検査されない証明である。
> 発行をコンパイル時（mono / specialize）へ移し、検査を消滅させる。**

Yulang には Koka にない武器が二つある。principal な effect row 推論
（注釈が capability 宣言に縮退するほど主型が強い）と、
monomorphization パイプライン（specialize）。mono 後の世界では row は閉じ、
call site ごとに「どの handler に届くか」が静的に決まるケースが大半になる。
これを使う。

### 提案 1: 静的 route 昇格 — cert の発行を mono 時に前倒す

現状 `StaticDirect` は既にあるが、`ProviderGrant` の gate 検査
（scope / baseline 比較）は signal 毎に走る。mono / specialize の時点で

```text
call site の effect family × その位置で静的に既知の handler 群
```

が一意に解決するなら、**gate 検査なしの direct call** に落とす
（Koka の "evidently" 定理の適用そのもの）。解決しない call site だけが
現行の動的 cert に残る。arm 分類（質 A）は既に静的なので、
`TailResumptive × 静的解決` の組は「ただの関数呼び出し + handler 環境の受け渡し」
までコンパイルできる——これは FFI 決定文書 §F6 の sync tier が host operation に
ついて主張したことの、**Yulang 内 handler への一般化**でもある。

衛生性はここで消えない: 静的解決の条件に「介在しうる遮蔽（AddId / handler
boundary）が静的に存在しない」を含める。判定できない場所は動的に残す。
つまり衛生性事件の再発防止は「動的検査」から「静的に安全な場所の特定 +
残りは従来どおり」に置き換わる。

### 提案 2: evidence slot の静的インデックス化 — 探索の消滅

`active_add_id_scans` や nearest-ProviderEnv 探索が hot counter に出ている =
evidence がまだ**探索**されている。row 型から effect family ごとの
evidence slot 番号を静的に割り当てれば（mono 後は row が閉じるので slot は定数）、
lookup は配列添字になる。Generalized Evidence Passing の中核で、
これが入ると質 C の cert が守っていた「木を歩いて provider を探す」コスト自体が
消え、三兄弟の存在理由が縮む。

### 提案 3: native close 三兄弟を scope-delta の正規化に置換する

Phase 3（MarkerDelta / ProviderDelta）を「個別最適化」ではなく
**証明の再編**として実行することを提案する。marker/provider の enter/exit を
列（自由モノイド）として持ち、正規化規則（隣接する enter/exit の相殺、
交換可能な要素の整列）を**一度だけ**意味論に対して証明する。すると:

- 三兄弟の条件リスト（各 6〜11 項目）は「正規形がこのパターンに落ちる」
  という判定に退化し、実行は「事前計算済み delta の適用」になる
- 「Then 第一枝・深さ 1」のような木の形の条件は、正規化が木を潰すので消える
- 新しい close パターンが必要になっても、cert を増やすのではなく
  正規化規則の適用範囲が自動的に覆う

これは既存 Phase 3 計画の実装内容とほぼ同じで、違いは
「delta を cert の隣に足す」のではなく「delta を正規形として定義し、
三兄弟を正規形パターン判定に吸収して**退役**させる」という到達点の設定。

### 提案 4: handler 代数のカタログ化 — State の次は Fold

KnownHandlerPlan::State の証明形式（代数の形 + 継続規律 + snapshot/fork）は
**テンプレート**として一般化できる。優先順位つきの候補:

1. **Fold / accumulate 代数** — Yulang はコレクションも for/each/undet も
   Fold + effect で組んでいる（[[project_core_roles]]）。Fold handler の
   certificate は `for` ループ本体の直接実行を許し、言語の中心 idiom を直撃する。
   State より獲物が大きい可能性が高い。
2. **Reader 代数**（get のみ、set なし）— 条件が State の部分集合で、証明が軽い。
   config / 環境の引き回しが直接読みになる。
3. **Except 代数**（abortive のみ）— arm 分類 Abortive と組み合わせて、
   error effect の throw を「unwinding なしの early return」に落とす。
   error-handling-plan の `?` 記法とちょうど噛み合う。

### 提案 5: 検査の三層化 — signal 毎の検査を最後の手段にする

cert の各条件を「mono 時に決まる / handler entry 時に決まる / signal 毎にしか
決まらない」に分類し直し、上の層で決まるものを下で再検査しない。
現行の gate 条件のうち baseline 比較は handler entry 時に前計算できる部分が
ありそうに見える（要計測）。これは提案 1・2 の漸進版として、
大工事の前に単独でも効く。

### 優先順位の私見

**本命は提案 1 + 2**（Koka 系譜の王道で、infer の強さがそのまま速度になる。
mono/specialize が既にあるから、必要なのは新しい解析ではなく既存分類の配管）。
提案 3 は Phase 3 と同一工事なので合流させる。提案 4 の Fold は
known-state の Stage 7（user handler 認識）より先にやる価値がある——
compiler-generated な Fold（for 脱糖）から始めれば、State と同じく
「コンパイラが証明書を発行する」形で安全に入るから。

## 6. 実装しないと分からないこと

- mono 時静的解決の被覆率（call site の何割が閉じた row を持つか）。
  これが低ければ提案 1 の利得は薄い。まず**計測だけの pass** を specialize に
  足して被覆率を出すのが最初の一手（shadow 方式の伝統に従う）。
- 提案 2 の slot 割り当てと、既存の provider env 表現の互換コスト。
- 提案 3 の正規化が、hygiene の全ケース（guard_mask / resume_delta /
  handler_boundary）を本当に代数の中で表せるか。表せない残余があれば、
  その残余だけが動的検査に残る。
- Fold 代数の腕形が、現行 std の for/each 脱糖の実形と一致しているか。

## 7. この文書の扱い

これは翻訳と提案であり、決定ではない。次の段階分けを推奨する:

1. §1〜4（翻訳・評価）をユーザが読み、oracle の理解が設計者に移る
2. 提案のうち採用するものを選び、採用分だけを署名付き決定文書に昇格する
3. 最初の実装一手は「提案 1 の被覆率計測 pass」（挙動変更なし・数字が出る）

---

*署名: この文書は Claude (Fable 5) が 2026-07-02 に、実装側 oracle
（cert / plan / invariant 群）のコード調査と既存設計メモの読解に基づいて
作成した解説・提案である。決定文書ではないため正本一覧には加えないが、
記述の正確性への異議・提案の採否はユーザの判断に従う。 — Claude (Fable 5)*
