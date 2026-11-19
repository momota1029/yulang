# Cycle 266: 実遷移の有限圧縮と、候補経路を与えたときの停止・モデル対応

実開始 **2026-11-19 05:30:24 UTC**。最終取りまとめ **2026-11-19T06:20:29 UTC**（50.08 分。上限 06:25:24 UTC）。25 分の時点では、単一路の逆対応、実 239/240 回帰、異なる終点を持つ経路族の定理は未到達だった。次の定期枠は先取りしない。起点は公開済み 265 の `1b113cfd9`、統合版は `a2927fae2bd94a46c36a064f2fb523b1b43463e8`。最新の ACTIVE、I-51〜53、凍結範囲を照合。以前の 265 の復旧公開は変更していない。

## 到達した部分目標

1. **実 source Step と、有限表現の checked write（健全性・完全性の部分）**。任意の固定 owner/output basis と旧 Step について、射影が変わらなければ有限書き込みは空、変われば厳密な一歩になる。 `GeneralRebaseCompression266` は明示的な書き込み結果の被覆のもとで旧 trace の厳密な変化数を保存する。 `GeneralRebaseCheckedLocal266.checked_install` と `.checked_merge` は、それぞれ供給済み実 install と影響する旧 plan のみを読む merge を、支持の閉包のもとで checked write へ接続。 `GeneralRebaseProspectiveChecked266.source_checked_installs` は、source 由来の一つの basis で到達後の選択済み候補、role 一意性、joint residual model、既存のガードと novelty を前提に、実 install・終点モデル存在を保つ。候補探索ではない。実 compound-where は `GeneralRebaseCertifiedFixture266` で一回の厳密な書き込み。
2. **厳密な一辺仕様と逆方向の範囲（健全性・完全性の部分）**。 `GeneralRebaseProjectionObserver266.step_exact` は任意の固定 basis 上の一辺 iff。有限な射影候補上で数学的な実辺証人の存在を古典的に選ぶ仕様で、到達可能性を証人の型に入れていない。全体の replay は同じ具体代表からの `Liftable`、または stutter をはさんだ `WeakLiftable` が必要。仕様側停止は任意の実 suffix でも射影が変わらないことを意味し、旧 source の normal form とは異なる。
3. **供給済みの実経路を実行する有限コンパイラ（健全性・完全性の部分）**。 `GeneralRebaseCertifiedPathCount266.exact_run` と `GeneralRebaseCertifiedReverse266.replay_iff` は任意の composable な実証明付き一本の経路の射影始点から、任意の有限 run が同じ経路の prefix に対応することを iff で示す。strict count は射影が変わる辺の数であり、元の辺の数や cut の一意性ではない。 `.settle_with_exact_budget` は末尾射影への停止とその厳密な回数を示す。 `GeneralRebasePathFamily266.every_terminal`。供給済み非空の同じ始点・終点の経路族を一つの表にすると、どの maximal finite run も同じ終点射影に至る。 `GeneralRebaseProjectedFamily266.every_terminal` は具体終点が相違しても終点射影が共通なら成立する。混成 run 全体が一つの具体履歴に持ち上がるとは主張しない。
4. **単調な規則と同じ終点（補助・条件つき意味保存）**。 `GeneralRebasePersistentObserver266.settle_minimal` は提案された事実の pending 中の持続を前提に、すべての terminal run の同一性と least refinement を得る。 `GeneralRebasePositiveMeaning266.least_saturated` は実行できる正の有限規則の最小閉包。 `GeneralRebaseEdgeRules266.run_covered` は供給された任意の表から得た規則の過大近似、 `.sound_iff` は pointwise rule validity の明示条件。各経路が同じ終点射影を持つ場合は `GeneralRebaseProjectedFamilyMeaning266.rules_settle` が有限表 scheduler と同一の終点を出すが、各ステップ・提案・回数は同一とは限らない。非持続な提案では、同じ unordered Step を持つ閉 observer さえ順序で結果が違う有限反例を `GeneralRebaseTransientClosed266.counterexample` で確認。旧 source の反例とは別。
5. **有限終点と元の journal の関係（条件つき意味保存）**。 `GeneralRebasePathFamilyMeaning266.source_family_meaning` と `GeneralRebaseProjectedFamilyMeaning266.source_models` は、実 Initial から一つの有限 basis をとり、最後まで供給済みの経路について ledger 同期と支持被覆を到達性から導く。各 concrete endpoint について、その journal の remainder を保持し、assignment ごとの代表両立条件を仮定すれば、両 scheduler の算出値を読むモデルが元の journal モデルと iff。別履歴同士で出力射影が同じでも、full model が等しいとは主張しない。
6. **反復の回帰（停止性の部分）**。 `GeneralRebaseRecurrence266.version239` / `.version240`: 任意の固定 basis で実反復のある段階以降、各ラウンドの証明付き経路はどれも全辺が stutter、有限実行は 0 回の厳密な書き込み。旧 source の `Acc` は同じ各段階で偽のまま。 `GeneralRebaseProjectedFamilyRegression266.actual_collision` は、実239で0ラウンドと1ラウンドの具体終点が異なるが射影が等しくなり、両 scheduler が同じ射影に停止する例。strict な枝分かれの試験ではない。旧239 の全 Step を射影 rank＋全 stutter 減少 rank で下げることも不可能と証明した。

## 検証・公開

新規 **36 Lean モジュール**、監査対象 **218 名前付き宣言**（定理数ではない）。モジュール一覧・宣言名は [検証ディレクトリ](../verification/cycle266/) の `*-modules.txt`、`*-declarations.txt` と初回の `modules.txt`、`declarations.txt`。I-53 の36行を `lean/Yulang.lean` の末尾に追加して全行照合。I-51 に従い6本とも `Yulang.*` だけを import。凍結された監査本体・README・spec・plan は変更なし。

- 公式 Lean 4.35.0。環境リセット後に前周の公開を復元し、最初は依存の `Main` を拾えなかったため依存抽出を修正。以後の最終焦点ビルドは36件、参照依存集合2014、exit 0。実行は `REBUILD_CYCLE266=1 python notes/verification/cycle266/focused-build.py <新規36モジュール>`。各ルートを `lean --trust=0 -DwarningAsError=true -R ...` で検査。 [最終ビルドログ](../verification/cycle266/final-build.txt)・[依存ファイル SHA-256 台帳](../verification/cycle266/dependency-sha256.json)。
- `cd lean && lake env lean --trust=0 -DwarningAsError=true -R . Audit/<今回の各ファイル>.lean` は6本とも exit 0。標準3公理の部分集合のみを確認（[要約](../verification/cycle266/final-axiom-summary.txt)）。別の読み取りレビューも行い、証明と報告の範囲を照合。独立環境の再ビルドではない。
- `bash tools/verify-lean.sh . a2927fae2bd94a46c36a064f2fb523b1b43463e8 --no-build`（差分のみ）exit 0、[全ログ](../verification/cycle266/final-diff-gate.txt)。初回は docstring の英単語一語が禁止語の字句検査に触れ、文言だけ変更して焦点ビルド・各監査を再実行した。全リポジトリのビルド、全公理ゲート、CI、実機テストは未実行。
- 開始および各10分の心拍。途中公開は `038f0b2d`、`a7bfb0ac`、`38b0310b`、`0b18a6c8`、`cf449bd1` を tree 照合済み。最終公開は差分 **92 ファイル**（前周の確定 tree 比較）。中断なし。使用量の枠は不明。
- Yulang2: 既存の `work/dots-audit/notes/audit/x-oracle.md` の where / K2 関連事例を確認。今回の有限 scheduler は Lean 上の後継表現で、Yulang2 の実機挙動として直接照合はしていない。新しい言語意味の判断・質問ノートはなし。

## 残り（B4 の側）

I-52 の新有限表現の厳密な測度、供給済み経路に対する再生、実239/240の投影停止を前進。旧 kernel の停止性、complete source compiler、モデルを持ち上げる双方向の一般対応を閉じたとはしていない。 `B4SkeletonV8.B4Bridges` は14フィールド（12 operational＋2 production）。この周は新しい一般 `SourceBoundary` への14フィールドの実装を追加していない。残りの優先パッケージは以下の3本。既存の局所版の証明は撤回しない。

1. **有限かつ実行可能な current candidate / packet 発見**: 実 Initial からの全到達状態における提案被覆と joint guards を証明し、caller-supplied Path/Edge を外す。
2. **一般後継 relation の source 代表・モデル対応**: 同じ射影で別代表へではなく、実 reachable 同代表からの stutter-aware lift と、履歴 remainder をそのまま持たない圧縮の意味保存を示す。一般 `progress`/`execution`/`halted` へ接続。
3. **局所分類、Permitted、Frame/EvidenceNode および全モデル健全性の移植**: operational fields と production fields を、一般 `resolve_exact`/B4 のまま接続する。M1 の健全性・完全性・主型性全体は未完。
