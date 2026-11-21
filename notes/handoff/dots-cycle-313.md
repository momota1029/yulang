# C313: 初回の実据付を一般に構成し、型推論健全性の次の境界を絞る

開始 2026-11-21 04:30 UTC / 13:30 JST。C312 完了 `07220bfaf5d53dbe2757b87887ff33d68049d75c`、
integration `af2ac2ebd8aff9088fc65fc3eb85e799f71600e6` の standing orders / inbox を開き直した。
I-55 の (4) を優先し、(2) の新しい一般橋・停止性には手を広げていない。

## 一般の初回据付と辞書（(4b) の履歴なし枝）

任意の checked source registry と、**据付履歴が空の任意の実到達状態**を取り、
妥当モデルが存在し、実 Local が選択した現 frame が与えられれば、**一つの割当て**で
全 journal、現 head、class 出力、実 where の上下端・順序付き子の実中心・計算出力を
満たす。実 `Residual` と `Installable` まで証明した。ルートの型形状、capture の多重性、
where の個数、算出出力の有無に追加前提はない。`GeneralVersionedCompiledFirstInstall313.joint / installable`。
同じ状態が Stable で、同一モデルで順序付き子の辞書証拠が与えられたときには
親辞書と実生成辺も返す（`node_and_edges`）。飽和の停止は述べていない。

- 据付前は実 refresh・reobserve・equate があっても full Models は初期 source Models と
  同じ。初期 source は妥当モデルごとの ground 実入力を既に持つ。成功した構文検査から
  scalar・structural・nominal の実 constructor tests を再帰的に作る。実選択の sharing
  から、過去辞書なしに全 actual binder を同じモデル上で読む。
  点 binder はその読み取りだけで正しく、private binder は境界側の名前と分離する。
  `GeneralVersionedBeforeFirstInstall313.models_exact`、
  `GeneralVersionedFiniteInspectionTests313.inspect_tests / many_tests`、
  `GeneralVersionedFirstGroundHead313.head`。
- 複合 where 入力の下端・上端・実中心は kind、clause、引数位置で分離する。
  変数に正規化される join は actual だけでなく lower/upper でも同じ変数値になる。
  算出 where 出力は正確に purpose-5 target を共有する場合にだけ意味上の整合が必要。
  実 compiler は clause ID とローカル出力式 ID を対にしているので、checked registry
  からこの整合は自動。新しい言語制約は追加しない。
  `GeneralVersionedCompoundRows313.coherent_address`、
  `GeneralVersionedNormalizedVariable313.normalized_value`、
  `GeneralVersionedFirstComputed313.exact`、
  `GeneralVersionedCompiledFirstInstall313.compiled_outputs_unique`。
- **閉じた実回帰**: 二つの複合 where clause でローカル式 ID 17 を再利用し、
  幅に開いた空レコードと厳密な空レコードをそれぞれ計算。実 compiler 後の target は異なり、
  checked / reachable / selected / 実 mixed install Step と、その後の一つの
  モデルに両方の出力が載ることを Lean で確認。
  `GeneralVersionedCollisionRegression313.step / two_outputs_same_model`。
  非コンパイル生データの slot 衝突は、source 反例ではない。

## 全到達路の保護集約と新しい owner（(4a)、(4b) の土台）

- 任意の有限 support は、1 座標だけを変えて Models の真偽が変わり得る座標に絞れる。
  これが最小の意味的 support。集約の保護はその座標か実 report の読み出しに限定される。
  正当な refresh で反射的な原子を追記しても無関係な座標は保護されない。
  逆に実 scalar・structural・nominal の既知 head は、妥当モデルがあるとき必須座標であり、
  正当に refresh して既知にできる座標は refresh 前から必須だった。
  `GeneralVersionedEssentialSupport313.support_iff`、
  `GeneralVersionedEssentialAggregates313.sufficient_iff / harmless_not_protected`、
  `GeneralVersionedObservedEssential313.known / refreshed_essential`。
- 保護集約は、実履歴の同じ ID **または**現モデルでその等式が既に成立する証明で賄える。
  この二択を実 alias の旧候補 `Prepared` と選択鍵の互換性までつないだ。
  予約だけではどちらの証明にもならない。
  `GeneralVersionedSemanticEntryChoice313.sound / prepared / choice`。
- 実 raw domain の新しい ID は初期 source の範囲内か、実 install が予約した数値 owner
  に由来する。現在の report は base の実 slot のみを読む。履歴 packet の raw domain は
  後続へ保存。過去に据え付けていない数値 owner の ID は実登録済み center と現 head の
  origin にも現れない。その owner の purpose-8 binder を保護する残りの場所は、選んだ
  意味的 journal support だけ。すべての一般 journal support に関する不在は未証明。
  元の root では履歴ありでも source の ground test を回収できる。
  `GeneralVersionedTraceDomain313.origin`、`GeneralVersionedRawReportDomain313.reads_slots`、
  `GeneralVersionedHistoricalDomain313.reached`、`GeneralVersionedUnseenOwnerCenters313.avoids`、
  `GeneralVersionedUnseenBinder313.protected_iff`、`GeneralVersionedReachableRootGround313.tests`。

## I-55 の残り（未証明インターフェース群）

- **(4) 2 本。** **(4a)** 過去 install がある任意の non-replay alias に対して、実 report または
  意味的 Models に必要な各集約 target の正確な owner・宣言鍵・その名前の版の履歴か、
  同じ現モデルで既に成立する集約式を供給する。**(4b)** 任意の過去 install 後に、実生成子の
  constructor tests・保護 private binder/集約・内部書込みを一つの現モデルで供給する。
  **初回据付の一般枝は今回完了**したが、他の owner の install 後に初めて現れる子の枝や
  refresh/merge 後の保護全体は別なので、全体の群数は減らしていない。
- **(2) 2 本。** **(2a)** 実履歴付き Local 行を生成する一般 source observer/compiler。
  **(2b)** Sat が成功して返った場合だけ、実 mixed Step 経路、返却地点の停止証拠、
  返却木と宣言的 Local/Classify の一致を与える橋。今回は未変更。

これは定理の未証明入力群の本数で、残り補題数の予測ではない。
言語仕様・受理条件は変更なし。Rust/CI 未実行、全体 Lake 未実行。使用枠残量は不明。
質問ノートなし（ローカル ID の重なりは実 compiler が解消済み）。
[設計と次の候補](../design/2026-11-21-cycle313-semantic-aggregate-producers.md) /
[検証ログ](../verification/cycle313/verification.md)。

## 検証と公開

29 新規 Lean モジュールの focused `lake build --wfail` と各ソース `--trust=0`
は終了 0。11 本の単独監査も終了 0（433 検査出力、重複含む）。
公理は通常の 3 個のみ。diff gate `--no-build` は終了 0。
barrel に 29 import を同じ公開に追記。通常の公開先は `work/dots-main` のみ。
所要時間と最終読戻し pin は完了 heartbeat に記録する。
本周期の差分は heartbeat を除き 64 ファイル（29 モジュール、11 独立監査、
barrel、設計・報告、検証資料）。公開時は前の正確な branch head を指定し、強制更新しない。
