この周に閉じた C の行: **なし**。C14 は未完（`primitives_only_cannot_add_genuine_nonpoint_record_selection422`、`same_model_endpoints_support_both_projected_channels422`）。

## C14 で分かったこと

仕様 §6.3 の `Pick {x:'a,..'rest}` について、元の二つの根拠付き record 端点を読む独立した検査と、同じ適合モデルで field・残余の区間を保存する証明を追加しました。実例では引数の三つ組は `(0,1,2)`、field 端点は `(3,4)`、residual 端点は `(5,6)`。中心 1 の record 行がなくても端点の読取りは成立し、元の `type out = 'a` に対応する B6 の実 binder も存在します。

- `primitives_only_cannot_add_genuine_nonpoint_record_selection422`: この元要求で中心の record 行がなく、ある適合モデルで上下端点が非同値なら、**任意の**局所規則集合 `R` に対して、固定された `Classifies R` は選択を作れません。固定 `SourceHead` の全構成から証明しました。既存の普通形は中心行か、実質的に両端点を同じ型に固定する証拠を要求します。既存の R13 公開入口でも、この実例の選択報告は任意の証人で通りません。型エラーや保留の判定を足したわけではありません。
- `same_model_endpoints_support_both_projected_channels422`: 任意のこの端点読取りと元の適合モデルで、実中心の required/optional の field 両射影がそれぞれ元の field 端点に挟まれ、同じ実中心の mask residual も元の残余区間に挟まれます。これを literal record の再構築や exact delete の一般証明と同一視しません。
- `fresh_record_model_extension_exactly_when_channels_agree422`: 元の ordinary State を拡張し、既存名・元の結果先を保持した literal record 行を **別の** State と割当てで構成できるのは、元の fit と required/optional 射影の同値がある場合に限ります。実例の二つの適合モデルでは可能ですが、同じ原要求の第三の適合モデルで一致に失敗します。新しい名前で literal record 行を足す方法は全モデルで通用しません。一方、行を足さずに実 projection/mask を別の適合割当ての未使用名に表すことは、この第三モデルを含めて可能で、元の制約座標・結果先を保持します。それと、既存の元モデル・元入口でその名前の意味や選択証拠が既にあることは別です。

元の B6 本体をそのまま使う `original_B6_binder_yields_required_projection_and_exact_addresses422` も追加しました。実例では、元の出現 `[61,422]`、宣言 1、出力 0、固定先 12 を保ちながら、三つの適合モデルで RHS の投影値はそれぞれ `int`、`int | bool`、`top` になります。固定先にその値が既に保持されることは別の証明です。

次の実装候補は、中心の literal 再構築を前提とせず、両端点に基づく projection/mask を表せる内部の head 証拠と、その同じ binder の元 B6 本体・固定出力をつなぐことです。固定証拠型・I-65 の命題・既存 checker は変更していません。第三の適合モデルでは旧 `HeadMeaning` の literal record 同値そのものが偽であり、分類の名称や構成子を足すだけでは直りません。新しい言語仕様の問いは見つかっていません。

## 検証・公開

[設計と反例](../design/dots-cycle-422-record-endpoints.md)・[再生と対照](../design/dots-cycle-422-c14-verification.md)・[C の一覧](../design/dots-cycle-422-c-coverage.md)。技術ピン `2d74668d6979bcad61851c422db0a858a6aed57e`、Lean tree `eeb7776992d0875822bcb8291c583583b1acfb90` を byte-for-byte で照合。新規 Lean 9、独立 audit 7、既存 barrel import のみ追記、設計・検証・一覧 3、心拍・報告の **計 22 パス**。凍結 2 ファイルは内容未読、blob ID 一致。

Lean 4.35.0 `lake env lean --trust=0 -DwarningAsError=true` の独立差分再生は三つの範囲すべて exit 0。広い範囲も C409–422 の差分に限定（source 130、旧補助依存 3 を含む、audit 71）。今回の公理出力は 36 種、標準のみ。旧の 42 + 13 対照と追加の元 locator・根／下位フィールドの K2・結果先未保持の対照も検査。使用量の枠は不明。

最終確認時の `integration/m1-final` は `2c89fd40a05965ea8438cd8c169ecf7e2e096a6f`、`integration/types` は `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-74 の Inbox は `b99a214965f1e236ab62e6cffa13b77b617543cb`。C421 までの exact Lean tree 一致を確認しました。C422 の追加証明はこの報告時点では work/dots-main です。

外側の W/Hold の実行、同じ元 State での C14 の R14 追加・checker 分岐・健全性、任意の exact residual deletion は未完。Rust・repo 全体・完全性・停止性・NoFalseRejection は未検証。C15 には進んでいません。開始 `2026-11-25T17:30:22.816Z`。

- 最終照合開始 `2026-11-25T18:20:26.972Z`（50 分経過）。

**C の残り: 9 行（C14–C22）。**
