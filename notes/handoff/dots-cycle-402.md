# dots-main 第402周（I-72 / I-65 Step 1）

**閉じた補題なし・分けた補題なし。** C380 から引き継いだ残件は 14 件（未証明 3、部分証明 11）のままです。integration/m1-final の一般定理は未証明です。

- 前回基点 `2ba2d98ba79df13f49170bc80e887707aab33ea5`。I-72 は integration/m1-final の `07831a8ae5fc56c5154cc31f163b9bd7256ea66e`、inbox blob `2684940d16dd1b4f8aa76788a2719010b04a3bf4` で確認しました。I-72 確認後は以前の I-71 の作業を止め、新指示の定義と組立に切り替えました。
- **切替前に検証済み:** [実際の共変 join のソース](../design/dots-cycle-402-i71-join-origin.md)。C357 のソースで選ばれた root から、元の宣言位置、where の順序、二つの元の束縛の merged center を保持する pre-output frame を取り出しました。join に限定した有限 trace では、実際の辞書について同じ frame と、供給された B6 の型付き RHS の同一モデルでの読み取りを照合しました。一般の候補選択・B6 入力の生成・任意の端点三つ組の証明ではありません。
- **I-72 の定義と組立:** [固定の目標](../design/dots-cycle-402-i72-fixed-goal.md)・[組立の境界](../design/dots-cycle-402-i72-assembly-boundary.md)。Lean で B6 の型付き RHS 木を元の出現位置に保持する State、有限の source completion、同一モデルの再帰的 DictionaryEvidence、全 State・request・選択辞書・適合モデルを量化する `I72.DictionarySound R` を記述しました。S01–S12 と S13 の五つの既存末端を命題として命名し、組立の型を確認しました。B6 の木を旧来の平坦な列に変換せず、元の順序・位置を保持し、RHS の読み取りと固定出力先を満たすことを区別しています。
- **Checked（暫定インターフェース内）:** `I72.assemble_remaining` の残る前提は S02–S08、S13bbba、S13bbbb の九つです。これは `SourcePrimitives` / `SourceSpecification` をパラメータとする組立上の数です。一般の独立した全候補規則を実装したことにも、実際の integration の残件が九つになったことにもなりません。有限 support では指定した元の序数からその位置の実証拠を取得でき、未絞り込みの root K2 から出力を完了できず、独立した基底がない族は自己参照だけで有限に成立しないことも検証しました。実行の停止性は主張していません。
- **次の実装箇所:** 同一 State の実際の候補訪問・優先順・選択・capture と、元の B6 型付き出力を同じ選択の実証拠から生成する規則。固定出力先における同一モデルでの保持も別に未証明です。仕様を補う新しい採否条件は入れておらず、オーナーへの新しい確認事項はありません。I-65 Step 2/3、旧 Local/C334、fixture、停止性には着手していません。

## 照合

- 直前の検証済み Lean スナップショット `329c9b5bcd1c5765841a8c4617225e634611bd76`（Lean subtree `b3280fb1382ada54b190d557d60651020fe15ddf`）。六つのソースと独立監査を公開済み Git バイト列から再構成し、Lean 4.35.0 の `lake env lean --trust=0 -DwarningAsError=true` で検査しました。実際に追記した六つの import をまとめて確認し、監査の公理は標準の `propext`、`Classical.choice`、`Quot.sound` のみ。全リポジトリビルド、Rust、実行試験は未実施です。
- 作業ブランチのみ expected-head・non-force。累積変更 18 パス（ソース 6、監査 6、設計 3、import barrel、心拍、この報告）。固定 I-65 とチェックリストの blob は不変。凍結ファイル二つは blob ID のみ照合し、内容を読み書きしていません。
- 最終照合開始 `2026-11-24T22:20:45.412Z`（50 分経過）。
