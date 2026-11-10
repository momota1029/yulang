# B4 主定理と、サイクル 100 までの部品の差（監督役の読み取り, 2026-11-11）

状態: 監督役（Claude）が、dot の報告・設計ノート・モジュール名を読んで作った見積もり。**Lean の証明の中身を精読したものではない**（宣言の成否と報告の主張だけ）。数字は感覚であり、約束ではない。dot の報告は「橋 5 本のまま」としか書かないので、橋の中身の進み具合を、承認済みの主定理（`2026-11-08-b4-main-statement-draft.md`）の 5 項に対応づけて見直した。

## 主定理の 5 項と、部品の対応

### (1) 飽和の存在と停止 — 進み具合: 半分くらい
- **ある**: 有限な仕事領域の計算（`CommonRoleSourceTemplateClosure`、`GeneratedWhereClosure`、`IntervalWorkClosure`）。停止の尺度（Paterson 的な下降、`MaterializationProgress`: materialize した Goal の変化回数の上限が元 Goal から計算できる）。診断ツリーの再利用つき実行版（`FrontierReplay`）。有限フィードバックの収束（`FiniteFeedback`、`MixedEvidenceClosure`: 関連型と ordinary の交互閉包）。実 solver との接続（`CheckedOrdinaryReplay`、`EvidenceReplay`）。
- **足りない**: (a) 実 solver が状態列を作る driver と、その列の停止（今は caller の batch、または scalar 断片の内部生成まで）。(b) materialization が **int だけ**（一般の Form の state 更新は翻訳が無い）。(c) K2 の一般 driver。(d) 「不変の状態のあとに新証拠が来る」場合の扱い（plateau を停止条件にできない）。

### (2) 正確性（Sat の分類 = 独立な Classify） — 進み具合: 3 分の 1 くらい
- **ある**: 狭い断片の `resolve_exact`（`SettledResolver`）。first-order と区間の診断ツリー（`GeneratedWhereClosure`、`GuardedIntervalFrontier`）と、全ノード列の到達可能性（`FrontierReachability`）。候補を分けた plan（`GuardedIntervalPlans`: 候補は選択、where の子は連言）。診断ツリーから ordinary グラフへの接続（`FrontierGraphs`）。断片内の「保留」の正確な特徴づけ。
- **足りない**: **4 分類（selected / pending / ambiguous / rejected）そのものの帰納的な判断**と、実行版との iff（診断ツリーまでは来たが、分類への写像は未着手。質問ノートの境界 1 は回答済み: 子の結果を保持する未完成の診断ツリー）。一般の状態（絞り込み後）での候補の消滅。

### (3) 順序独立 — 進み具合: 6 割くらい
- **ある**: where の兄弟の順序（`PathOrder`、`SiblingOrders`、`SourceRoleObligations` の where 並べ替え不変性）、clause／仮定の並べ替え・重複（`NamedSourceEntry.run_source_congr`）、ソース名の単射な付け替え（`NamedSourceRenaming`、`FiniteSourceRenaming`）。
- **足りない**: **visible な impl の列の並べ替え**（候補の順序）、辞書の観察同値 `DictionaryEquivalent`（質問ノートの境界 2 は回答済み: ソース義務の正準な順序で比べる方向）。

### (4) 辞書の健全性 — 進み具合: ほぼ手つかず（5% 未満）
- **ある**: 成功の判断の独立な側（`SourceStateDischarge` の role 義務の検査）。
- **足りない**: 辞書の構成と、全モデルでの健全性。橋 5。

### (5) 拒否の正しさ（偽の拒否が無い） — 進み具合: 3 分の 1 くらい
- **ある**: スカラー・構造の矛盾の証明書（有向の上下界、同 head の再帰、外側の rigid な head）と、枝刈りの保存。K2 の `regularAt` が追記で保たれること（`AllocatedGraph`）。診断で「outside」を落とさないこと。
- **足りない**: K2 の拒否規則を分類に組み込むこと。候補が全部消える理由（iii）が、分類の判断と iff であること。

## 橋 1（実ソースから Lean の需要を作る側） — 進み具合: 4 分の 1 くらい
サイクル 77〜88 で、入力を 1 つずつ内側の計算に変えた: 名前の割り当て、スロットの写像、テンプレート関数、where の clause の抽出（raw 入力から検査つきで）、ソース式（literal・変数・let、明示スカラー注釈）、`Source n` の計算（サイクル 101）。**残り**: 一般の宣言・式からの lowering（`Roles.Impl` に where の関連等式の入れ物が無い、というサイクル 84 の発見）、パーサ AST との接続、非スカラー・多引数・effect。

## 残りの作業パッケージ（粗い列挙）

1. 状態更新 driver: 実 solver が状態列を作り、それが停止する（(1)(a)）。
2. materialization を一般の Form へ（(1)(b)）。
3. 4 分類の帰納的な判断と、診断ツリーからの写像、実行版との iff（(2)）。
4. K2 を分類に入れる（(2)(5)）。
5. 候補の順序独立と、辞書の観察同値（(3)）。
6. 辞書の構成と全モデルでの健全性（(4)）。
7. 宣言のモデルに where の関連等式の入れ物を足し（T13 の Lean）、宣言から需要を生成する（橋 1）。
8. 上を 1 つの `B4Statement` に束ねる。

## 時間の見積もり（不確かさが大きい）
ここ数日の速さは、1 サイクル（約 10 分）で 1 つの部分目標。パッケージ 1〜8 は、それぞれ数サイクルから十数サイクル。**足し合わせて数十サイクル（1 サイクル 1 時間なら数日〜1 週間）が楽観的な線**。ただし、これまでに 3 回、モデルそのものが違っていたと分かったことがあり（点モデルから区間、引数の行、候補ガード）、同じことが起きれば、見積もりは動く。橋 1 と (4) が最も不確か。

## この見積もりの使い方
- 数字は、サイクルごとの報告の「進み具合」と突き合わせて更新する。
- 大きく外れたら（例: パッケージ 3 の着手が 20 サイクル遅れる）、設計を見直す合図にする。
