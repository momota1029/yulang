# C431 C15 の exact scoped Lean replay

基準 integration `9ef86984658f7d5b152d0b56685033d7dc940e0b` / Lean `881d83f60dd5ca7064e241f8a7f71f0a5f7efee1`。C431 の公開候補 `04be83be1baa9d1426f3598cb7a7c0ecf740f9cf` は下の Lean path 5件だけを追加/追記している。確認済みの投影 root tree `f6341c4ad13ba673076b3d256d625a5a83e616bf`、Lean tree `61e9ece31b2888dd90793d631cce25b6cdf21889`。既存 R14、凍結ファイル、lake config は変更しない。基準の Lean tree と対象 path を比較し、一致しない状態に盲目的にコピーしない。

| path | Git blob |
|---|---|
| `lean/Yulang.lean` | `37f65571adfdc1c6061813a96e129bb22720b707` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereRule431.lean` | `e3d303c9f830b10fd4b6f08d26d936980456c475` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereEntry431.lean` | `4e4ebfc1ca7d921d458d4d71db464840d132ab83` |
| `lean/Audit/Cycle431I74StructuralWhereSpec.lean` | `5572c5e0d287d356dd2305da1a8a70f3a64db5ab` |
| `lean/Audit/Cycle431I74StructuralWhereLegacyEndpoint.lean` | `c34420ff93107320bb4c4ee99e3c1330e6ad4dac` |

Lean 4.35.0, `--trust=0 -DwarningAsError=true`。両 production module を Git blob から復元して再ビルド。各 Audit は別々の新規 cwd で、production-only LEAN_PATH、Audit olean ゼロ。新 Audit 2本・旧回帰4本 exit 0、標準公理43表示。旧回帰は C426 R14 endpoint、C427 原構造 readback / raw visits、C428 integrated legacy。新2 Audit は `Yulang.*` のみを import。全体ビルドや Rust は未実行。

追加対照: 独立 scratch の `git mktree --missing` と `git diff-tree --no-renames -r --name-status` が正確に A4/M1（追加 source 2、追加 Audit 2、barrel 追記）を返し、期待 root / Lean tree とも一致。凍結ファイルの内容取得なし。

同じ exact R15 実装を使い、既存 C426 の `cyclicReceiptRoot425` と `knownRawR13Wire426` から、新入口の `.previous (.previous knownRawR13Wire426)` が元の root K2 報告を通し、同じ実要求で `Classifies R15 … .rejected` となることも別の clean cwd で検査した。これは2件の追加ローカル対照（両方 exit 0・標準公理のみ、未登録）。新規の C15 branch が `false` を返す未対応入力が、そのまま診断の生成を意味しないこととは別。
