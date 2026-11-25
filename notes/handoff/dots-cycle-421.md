この周に閉じた C の行: **C13**（`dictionary_sound_R13`、`RepeatedCenters421.check_sound`）。

## 結果

`impl R 't 't` の可視一候補に、元の非点区間二本を渡す実 `R` 需要を扱いました。候補を決める段階では、由来のある元の下端と区間制約、宣言番号、両方の元の根の K2 だけを使います。選択した後に、元の実中心 1 と 4 の等式を照合します。保持済みの等式で整合すれば第一出現の区間全体を共有捕捉として選択し、同じタグの実中心が int/bool で等式が矛盾するなら型エラーとして拒否します。整合するが等式が未保持の場合は証人が不足しており、検査器は `false` を返します。それ自体を言語上の拒否や保留とはしません。既定の報告型に診断名は増やさず、拒否の根拠が型の不整合か根 K2 かを証拠で区別します。

- `actual_conflict_makes_selected_batch_unsatisfiable421`: 実要求の選択 `a` とその不整合証拠があれば、任意のモデルについて、この状態に正確な実中心等式だけを追加した状態はその割当てに適合しない。例は追加前には実際に適合する。逆に `exact_post_equation_preserves_every_compatible_current_model421` は、同じ型で整合する post 読み取りがあるなら、既存の任意の適合割当てが追加後にも適合することを示す。
- `only_exact_post_outcome_reports_on_original_repeated_choice421`: 任意のこの元要求・選択・認証済み post 結果・報告について、同じ状態で報告が分類の証拠を持つのは、verdict、木、台帳がその post 結果の正確な報告に等しいとき、かつそのときに限る。`incompatible_request_selects_no_R13_dictionary421` により、古い選択規則でこの不整合を回避できない。両引数の根 K2 は元の旧分岐を保つ。
- `dictionary_sound_R13`: 任意の状態・要求・辞書で、新しい局所規則和 `R13` がその辞書を選択するなら、同じ適合モデルすべてで従来と同じ `DictionaryEvidence` が得られる。`RepeatedCenters421.check_sound`: 任意の要求・報告・証人を入口が通したなら、元の分類と、任意の同じ適合モデルでの同じ報告の意味・出力の証拠を返す。旧 witness は全入力でそのまま委譲し、目標の意味は変えていません。

## 検証・公開

[適用範囲と再現方法](../design/dots-cycle-421-c13-verification.md)・[C の一覧](../design/dots-cycle-421-c-coverage.md)。新規ソース 10 と独立 audit 7、`lean/Yulang.lean` import だけ追記、設計・検証・一覧 3、心拍とこの報告の計 23 パス。凍結 2 ファイルは ID 一致、内容は未読。技術ピン `2ca91ca23c76b3ee4d52522c78643bcd3a12a670` の Lean tree `0683c008ffbb1a4527f24f602efc6b3aa3503e3c` から変更なし。

独立に取得し直した正確な Git bytes を Lean 4.35.0 `lake env lean --trust=0 -DwarningAsError=true` で再生し、3 スコープとも exit 0。最広スコープは C409–421 に限りソース 118 / audit 64、定理 564 種の公理出力は標準のみ。現在の公開入口で以前の 42 対照と今回の 13 対照もカーネルで再生し、期待値に一致。さらに実中心の適合・等式・根 K2 の 8 組（24 照合）と、元の locator の 47 照合を、上記の補助 harness で分けて確認しました。実行環境の一時切断後、同じ許可済み環境が復帰して再生を完了しました。使用量の枠は不明です。

最終確認時の `integration/m1-final` は `2c584f7f1555e9f4e9ab057f9028b6591c2deb01`、`integration/types` は `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-74 の Inbox は `b99a214965f1e236ab62e6cffa13b77b617543cb`。C420 までの exact Lean tree 一致を確認しました。C421 の実装はこの報告時点では work/dots-main です。

元の `P/Foo → where` から R 需要までを生成すること、任意の候補集合・記号型・他のタグ、Rust・repo 全体ビルド・完全性・NoFalseRejection・停止性は今回未検証。新しい仕様判断は不要で、質問ノートはありません。開始 `2026-11-25T16:30:16.548Z`。次の候補は C14 の、根拠付き record の両端点で選択し元の非点捕捉を保持する場合です。

- 最終照合開始 `2026-11-25T17:20:21.177Z`（50 分経過）。

**C の残り: 9 行（C14–C22）。**
