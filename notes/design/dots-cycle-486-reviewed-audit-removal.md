# I-99: 初回の削除範囲（重複した独立 Audit 一件）

対象の権威は `d12fff985c2aef3ef298b181251462f8f03c4e37`、Lean tree `9731ca088dbe50869458d94cd80f135be9771c16`。以下の明細以外の既存ファイルや行は消さない。

| 削除するパス | 削除前の blob | 置き換え先 | import の修正 |
|---|---|---|---|
| `lean/Audit/Cycle410I74RootEscape.lean` | `3b4f67388ad054b917321df3adaa99174a39bf62` | 既存の `lean/Audit/Cycle410I74ListEntry.lean`、blob `39253c2e7b9f5da3e93ef1b1cfcfd08fa65b0110`、5 行の同一の検査 | この Audit を import するファイルは 0。集約 import の編集なし |

削除側は import と `open` のほかに検査 5 件のみで、宣言や実行例を含まない。保持側の同じ名前は厳格ビルド前後で同じ完全修飾名 `Yulang.GeneralDeclarativeI65.I72.List410` 下の同じ宣言に解決された: `escape_rows_checked410`、`EscapeRows.sameAlias`、`EscapeRows.escapes`、`EscapeRows.follows`、`checked_escape_refutes_exact_raw_root_K2410`。`sameAlias` に公理依存なし。他の 4 件は propext / Quot.sound のみ。保持する監査全体も標準集合のみ。実装 `lean/Yulang/GeneralDeclarativeI65I74RootEscape410.lean` と既存証明は変更しない。C481 の 18 旧入口と I-65 固定声明も変更しない。

権威 tree の Lean ソース 10,732 パスを blob hash 照合して逆参照を検索、加えて tools の 53 ソース・設定 blob を確認。いずれも `Audit.Cycle410I74RootEscape` への参照なし。既存 umbrella も同参照なし。該当 Audit の直接輸入先が 0 なので、影響確認はその旧監査と代替監査に絞った。代替監査と旧監査の推移的なソース閉包（3,990 パス）の hash は、依存を準備した既存の Lean 4.35.0 の対象と一致。Audit だけを対象にする隔離した Lake 設定で、`--trust=0 -DwarningAsError=true` を使用した。削除前 `lake --no-cache build +Audit.Cycle410I74RootEscape +Audit.Cycle410I74ListEntry` は 3 jobs・終了 0。削除後は旧 Audit のソース・olean の両方がない別ディレクトリで、同じ依存を参照して `lake --no-cache build +Audit.Cycle410I74ListEntry` が 2 jobs・終了 0。全体ビルドではない。標準出力 sha256 は前 `8f6706fc27fd9f41f27873cc5463326533544e6f307289583961a33ee146fc04`、後 `5822cdab994177376fb927172982e289895eef4618a96cc5d400446a5022137e`。

削除だけを比較すると、影響のある監査ファイルは 2→1、Lean ソース全体では 10,732→10,731。削除される宣言は 0、同監査 2 ファイル中の実装宣言数は 0→0。出力される監査件数は重複込み 37→32、実際に検査される異なる宣言は 32→32。G05 追記のファイル・宣言はこの差分に含まない。監督役が統合時の `VERIFY_REVIEWED_REMOVALS` で開けるパスは表の一件だけ。