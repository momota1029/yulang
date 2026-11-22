# dots-main cycle 344: 版付き where の実コミットからの再現

- 作業開始: 2026-11-22 11:32:01 UTC。指示は `integration/m1-final` の `7dfbbfd750423300b6acaf57232c39b57ffa6c91` で確認。I-62 に従い旧 Local 対応は作業対象外（証明済みの意味ではない）。
- 前回: `2e21a129c2c2aa0b362e551be0206e651db11ced`。証明・独立監査の固定点: `cdb926848bd4a24ca776c4084d4b202a002d1e04`。

## 今回確認したこと

`GeneralDeclarativePackageBoundary344.actual` は版付き隔離試作の任意の実 `InstallStep`、正当なコミット後モデル、および既存の実 `Ready` から通常コンパイラが読める証拠を構成する。where 入力、関連出力とルート出力の実バッチを同じ割当てで満たし、生の全ジャーナルと依頼者指定の既存名を保つ。名前の存在や旧 Elected から Ready を仮定しない。明示出力に加え、既存の default は実入力の `center` を使用。コミット済み版を選ぶのであって、同名の最新行で置き換えない。

- 追加された stamp、物理サイト、子の順序と固定出力先を実コミット差分から得る。ソース作者順は生コンパイラの canonical 順と並べ替えの関係で、無条件にリスト一致とはしない。別名クラスの現時点リクエスト列は出生時の選択と混同しない。
- 生パケットが保持する作者側の引数を再生し、正規化後の ordinary compound row との意味一致を `lower`、`actual`、`upper` 各モードで検証。入れ子の不変 nominal では actual を読む。レコードの隠れた同名フィールドを落とす際、正規化で不要になった生の場所は証拠として要求しない。既存の独立した作者由来ソース行はその由来を保って拡張するが、コンパイラの出力から作者由来を新設しない。
- C319 の実際の旧コミット → nominal 再観測 → 現コミットでは、stamp 順 0→1 と別々の物理サイト 1→2 を保ったまま、一つの最終モデルで両方の証拠を再検証した。旧版の下端・上端は非点、現版はこの例では同値で、元の固定出力先名 4 を保つ（`PhysicalJoint344.both_receipts`）。
- 同じ C316 例について、旧版は実際に成功停止して選択診断も持つが、版付き投影に stamp がなく新規 `InstallStep` ではないため、この producer は使えない。孤立した版付き修正版には実 Step があり、任意のその正当なコミット後モデルで上記再現が成立する（`OriginalReplay344.contrast`）。既存の実行器の挙動は変更していない。

## 残り

- **(4) 1群**：独立に支持された全ての現行 I-61 規則から、入れ子／複合の open/closed・非点観測を生成し、現在の選択・実中心・同モデル辞書証拠につなぐ一般 producer。今回示したモード正規化・実バッチ再生は観測の支持や全ケースの Ready を生成しない。
- **(2) 2群**：①任意の実 raw 成功停止について、現行物理版と作者由来／Ready／固定出力を結ぶ証拠。②その成功停止から最新宣言的診断と receipt への一般投影（子の完全な並び・閉包を含む）。今回の仮定付き版付きコミットと具体 C319 証拠は、未版付けの一般成功停止に持ち上がらない。
- 次は実 raw 成功停止から「現行の」パケット／作者由来を得る箇所と、そこで集め直した現行 alias クラス出力に対する `RequestsDeclared` を分けて確認する。後者と現行解釈の `Coverage` が得られれば、既存の `ready_of_wf` が使える。出生時の出力列、旧行の昇格、固定出力の振り替えで代用しない。停止性、Rust 実行、全体ビルド、独立の作者性一般は今回の対象外。

## 検証と公開

- Lean 4.35.0。28 モジュール対象の Lake ビルド成功（依存スケジュール 3517 jobs）。固定 commit の detached 照合で 28 ソースと 5 独立 audit を各 `lean --trust=0 -DwarningAsError=true`、名前付き 54 定理は標準許可公理のみ。scope に含まれる非プラットフォーム宣言 102,991 件の公理 gate も合格。
- 固定 commit は C343 から 41 変更パスを全バイト照合。差分チェッカー（凍結除外、ビルドなし）合格。barrel の元 323,099 bytes は完全一致、今回の import 28 行だけ追加。凍結 `lean/Audit.lean`、`lean/README.md` は C343、指示元、固定 commit の blob ID が同一。内容は展開・検査していない。
- ログ: [focused Lake](../verification/cycle344/focused-lake.txt)、[exact source/audit](../verification/cycle344/exact-trust0.txt)、[named axioms](../verification/cycle344/exact-named-axioms.txt)、[scope axiom gate](../verification/cycle344/scoped-axioms.txt)、[diff-only](../verification/cycle344/diff-only-full.txt)、[bounded read-footprint smoke](../verification/cycle344/polar-smoke.md)。
- 最終報告コミットの公開開始: 2026-11-22T12:22:03.043Z（実作業開始から 50.03 分）。対象は `work/dots-main` のみ。既存意味論・integration は未変更。
