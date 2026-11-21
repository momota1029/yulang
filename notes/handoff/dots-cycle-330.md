# C330: 支持付きの実観測を、正確な子と書込みに繋ぐ

## 最初に読んだもの
`integration/m1-final` の固定点 `753a99f9e0675dd1bb03c769cf1f9cf7ed6da9ab` の standing orders、inbox と仕様 §4.3・§6.3、`work/dots-main` の C329 完了点 `2e2244dccd5317220ddc19edfc069ac696034b50` を照合した。I-56 の宣言的健全性と I-58 の「独立に照合した後、実中心を等式で共有」を前提とした。I-57 の二ファイルは変更せず、監査には独立モジュールを使った。枠は 21:30 UTC、実開始 21:33:15 UTC。作業中の再読で integration `2733c493c8e4e2b143363fc9a282f51560ea0baf` の I-59 と改訂 spec §6.3／§6.5 を確認し、承認済みの根 K2 の規則だけを追加した。

## (4) 宣言的型推論／辞書健全性
- **任意個の不変 nominal 引数と混合 head。** 支持のある実端点名から、引数が 0 個の場合も含めて中心を有限に構成する。pair/variant の共変部分と組み合わせても、上端を実中心にすることなく、順序付き出現列を供給する。任意長の引数列で、すでに実 trace がある引数、対応する端点から構成できる引数、閉じた支持付き record の実残余を混ぜて、C329 の反復等式・実子列・定義関係式の通常コンパイラに渡す。`ArityPlan330.extract`、`ArityRun330.build`、`ObserverSource330.compile`（以下モジュール名の `GeneralDeclarative` は省略）。二引数 nominal の実例では `3=4` が追加され、従来満たしていた割当て一つが反復条件で除かれる。子は実引数区間 `(9,10,11)` と固定出力先 `5` を持ち、別の具体的割当てで同じ辞書の再帰 Evidence が得られる。
- **record の実残余と支持の境界。** 実根から認可された alias と保存済みの record RHS をたどり、同名の隠れたラベルの消去、要求順、幅終端／厳密空終端の違いを保持したまま残余を構成した。直に埋め込まれた複合 payload の変数束縛では、新しい必要名だけを同時に確保し、既存名は再利用する。`RecordSpine330.exact_subtraction`、`RecordPoints330.observed`。実根の支持付き endpoint では末尾名が `13` だが、閉じた残余は `16 = {8: 4 | exactEmpty}` であり、ルートは `6=16` を書き、実子には payload 名 `3` を渡して `5=3` を書く。現在の候補ガードに新しい読戻し式を出所として加えず、具体モデルと全モデルの再帰 Evidence を確認した（`RecordElection330.protected_tail`）。
- **不透明 record における正確な不足。** 既知の同ラベル両端に挟まれた正規型でも、必須／任意 field への二つの観測結果が一致するとは限らない。両射影が既知の範囲で、その一致と同ラベルの単一 literal record 表示可能性が同値である。表示ができても通常等式だけでは、隠れた同ラベルが残余にあるかを固定できない。旧名・保護名の一致する二つのモデルが実際に異なる残余を持つ。また、複合 payload を inline で持つ実 RHS は、lower-known と正確な実読取りを持つが、「フィールドと tail がともに名前で保存されること」を前提とする旧 `Trace` には証拠がない。`RecordSplit330.obstruction`、`RecordReconstruct330.exact`、`RecordTail330.does_not_fix_remainder`、`RecordInline330.endpoint_gap`。これは旧観測関係の不足であり、仕様上の拒否・pending や安定した選定の反例ではない。さらに、任意の位置にある visible field を両方の支持付き閉じた端点から読めば、中心の全体が不透明でも各モデルでその必須 field の区間が得られる（`RecordPayloads330.opaque_payload`）。両端で実コンパイラの順序付き field リストが読めれば、その項目から最初に見える元の出現を直接復元し、追加の field 証明を仮定せず同じ区間結果を得る（`RecordConsumption330.from_ordered_endpoints`）。このモデルごとの payload は、中心全体の source spine や共通の論理 tail 名を与えない。未知の残余は仮定で埋めない。
- **現在の行を証明で読む。** 同じ固定名に関する ordinary 拘束・区間・行を現在状態から導出できれば、独立に計算したバッチの行が文字通り保存されていなくても、各々の現在モデルで出力と ordered child list を確認できる。実選定例では root の `6=5` は現在表になく、`6=10, 5=10` から導く。固定出力先と実子を変えず、独立の現在ガードと具体モデル／同じモデル上の Evidence がある。`CurrentReceipt330.complete/dictionary`、`CurrentResult330.accepted_without_literal`。支持行と区間証明の運搬は、モデル集合の一致と区別した。その情報が両方向で実際に揃うと、lower-known と positive endpoint 観測の同値が得られ、再結合の例では保留中の出力出所を使わずにこの条件を確認した（`GuardView330.positive_exact`、`GuardCurrent330.actual_guards`）。K2 は現在表で個別に確認し、モデルが同値というだけで診断や支持を運んでいない。

**残り 1 群。** 任意の承認済み安定 source 選定について、独立な propagation・現在の支持から該当する実観測を生成し、実際の write／scope／子順序／固定 RHS の receipt が得られるという一般定理。今回の混合 source producer は上記の可観測範囲に限る。旧 positive trace では届かない inline spelling、未知 tail、候補保留の独立した完全性は一括して済ませていない。下記 I-59 の承認済みの根 K2 に限り、実際の優先順位を取り込んだ。それより広い診断完全性は示していない。

## I-59: 片付いていない出力しか根拠がないが、普通の根が循環する場合

同じ引数で「支持付き観測には頭がない」「普通の頭の行は未完了出力で実在する」「普通の構造グラフの根そのものが循環上にある」を検査する場合を、旧宣言的規則の `rejected` の別理由として足した。C321 の実例（唯一の普通行 `0 = nominal[0]`）を使い、候補の照合も子の生成も不要で一枚の rejected 診断になることを確認した。ここでの根は既存の正規化グラフの lower 根であり、別引数の循環や深い候補検査を根の代りに使わない。根が循環上にないときと `selected(k, ds)` の判定は旧関係とまったく同じで、現在 receipt 版の任意モデルの辞書健全性はこの拡張にも成立する（`UnfinishedRoot330.actual_i59`、`selected_old_exact`、`dictionary_sound`）。一般の全 K2 観測や solver への実装は主張しない。

## (2) 成功停止を前提とする部分正当性
**残り 2 群。** (a) 任意の現行の成功停止から、現在状態・支持・解決済み子の正確な宣言的投影を得る、(b) その解決全体の辞書とすべての関連出力を、同じモデル／固定名で結ぶ。今回は (4) を優先した。停止性、物理 solver／journal、Rust 実行の検証は対象外。

## 検証と次の狙い
`notes/verification/cycle330/` に限定 Lake build、変更ソースの直接 kernel 再検査、独立 audit と axiom 制限、宣言依存境界、差分・statement index、実例の独立再検査を置いた。Lean 4.35.0 で 34 追加モジュールと 9 独立監査を直接 trust 0 で検査し、GitHub の固定ソースと全追加モジュール／監査のバイト一致を確認して再実行した。再開時は最新指示を再読し、具体的な次の接続は「候補の成否を結果から逆算せず、元の inline RHS から直接、正規化後の支持付き候補観測を作り、同じ source 実中心と書込みを結ぶ」。今回の `RecordInline330.endpoint_gap` は、その接続で必要な最小の綴り差を特定する。
