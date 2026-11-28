# cycle 487: I-100 の 18 旧入口の逆依存を再照合（削除 0）

権威 `dc51fb0613f5df358f1ff4cc86a39dff22981a8b`。I-100 の追加は inbox だけで Lean tree は `9731ca088dbe50869458d94cd80f135be9771c16` のまま。C486 の重複 Audit 1 本は I-100 が受け取ったが、この 18 入口とは無関係。作業ブランチでは前周と同じ一件を再削除したものとして数えない。

権威の 10,732 Lean ソースを exact Git blob hash と照合したうえで、18 入口の直接 import を再走査した。以下の数は集約 import を含む。各入口に少なくとも一つの個別 Audit と、集約以外の production 直接依存があるため、I-100 の「どこからも import されない旧入口」はこの範囲にない。 `lean/Yulang/` の省略名は同名の `.lean` ファイル。

| 旧入口 | 直接 import 数 | 実在する集約以外の production 依存 | 実在する個別 Audit |
|---|---:|---|---|
| `GeneralDeclarativeI65I74RetainedSplitEntry446` | 6 | `GeneralDeclarativeI65I74RetainedLocalHeader446`、`GeneralDeclarativeI65I74SelectedReplay447` | `lean/Audit/Cycle446I74RetainedSplitEntry.lean` |
| `GeneralDeclarativeI65I74WhereSamePhase454` | 3 | `GeneralDeclarativeI65I74WhereSamePhaseSource454` | `lean/Audit/Cycle454I74WhereSamePhase.lean` |
| `GeneralDeclarativeI65I74WhereGuard450` | 5 | `GeneralDeclarativeI65I74WhereLegacy450` | `lean/Audit/Cycle450I74WhereGuard.lean` |
| `GeneralDeclarativeI65I74SelectedEntry447` | 6 | `GeneralDeclarativeI65I74OpaqueRead448`、`GeneralDeclarativeI65I74SelectedExact447` | `lean/Audit/Cycle447I74SelectedEntry.lean` |
| `GeneralDeclarativeI65I74OpaqueEntry448` | 3 | `GeneralDeclarativeI65I74OpaqueVisibility448` | `lean/Audit/Cycle448I74OpaqueEntry.lean` |
| `GeneralDeclarativeI65I74OpaqueWholeEntry448` | 6 | `GeneralDeclarativeI65I74ListSiteRead449`、`GeneralDeclarativeI65I74OpaqueCallSite448`、`GeneralDeclarativeI65I74RecordHeader455` | `lean/Audit/Cycle448I74OpaqueWholeEntry.lean` |
| `GeneralDeclarativeI65I74ListSiteEntry449` | 4 | `GeneralDeclarativeI65I74ListFrameHead449` | `lean/Audit/Cycle449I74ListSiteEntry.lean` |
| `GeneralDeclarativeI65I74ListFrameEntry449` | 5 | `GeneralDeclarativeI65I74ListFrameWireOrder449`、`GeneralDeclarativeI65I74WhereSource450` | `lean/Audit/Cycle449I74ListFrameEntry.lean` |
| `GeneralDeclarativeI65I74WhereGroupedEntry453` | 7 | `GeneralDeclarativeI65I74WhereGroupedSource453` | `lean/Audit/Cycle453I74WhereGroupedEntry.lean` |
| `GeneralDeclarativeI65I74RoutedRecordEntry455` | 5 | `GeneralDeclarativeI65I74MixedNative456` | `lean/Audit/Cycle455I74RoutedRecordEntry.lean` |
| `GeneralDeclarativeI65I74RoutedMixedEntry456` | 5 | `GeneralDeclarativeI65I74RoutedNominalPoint456` | `lean/Audit/Cycle456I74RoutedMixedEntry.lean` |
| `GeneralDeclarativeI65I74RoutedNominalMixedEntry456` | 5 | `GeneralDeclarativeI65I74RoutedReadyHeader457` | `lean/Audit/Cycle456I74RoutedNominalMixedEntry.lean` |
| `GeneralDeclarativeI65I74RoutedReadyRecordEntry457` | 4 | `GeneralDeclarativeI65I74RoutedReadyMixedEntry457` | `lean/Audit/Cycle457I74RoutedReadyRecordEntry.lean` |
| `GeneralDeclarativeI65I74RoutedReadyMixedEntry457` | 5 | `GeneralDeclarativeI65I74InlineVariant458` | `lean/Audit/Cycle457I74RoutedReadyMixedEntry.lean` |
| `GeneralDeclarativeI65I74RoutedInlineVariantEntry458` | 6 | `GeneralDeclarativeI65I74InlineNominalPoint458`、`GeneralDeclarativeI65I74InlinePair458`、`GeneralDeclarativeI65I74InlineStructuralPolicy458` | `lean/Audit/Cycle458I74RoutedInlineVariantEntry.lean` |
| `GeneralDeclarativeI65I74RoutedInlineStructuralEntry458` | 7 | `GeneralDeclarativeI65I74HomogeneousClosedEntry459`、`GeneralDeclarativeI65I74IdenticalTagProjection459`、`GeneralDeclarativeI65I74JointWrittenTrail460`、`GeneralDeclarativeI65I74ProjectedClosedEntry459` | `lean/Audit/Cycle458I74RoutedInlineStructuralEntry.lean` |
| `GeneralDeclarativeI65I74ProjectedClosedEntry459` | 5 | `GeneralDeclarativeI65I74HomogeneousClosedEntry459`、`GeneralDeclarativeI65I74IndependentProjectedField459` | `lean/Audit/Cycle459I74ProjectedClosedEntry.lean` |
| `GeneralDeclarativeI65I74HomogeneousClosedEntry459` | 8 | `GeneralDeclarativeI65I74EligibleFieldStart461`、`GeneralDeclarativeI65I74IndependentHomogeneousField459` | `lean/Audit/Cycle459I74HomogeneousClosedEntry.lean` |

特に `FlatDispatch481` の既存参照、互換および旧健全性の宣言は既存の意味を保持するため残す。削除候補の数を稼ぐために個別 Audit・実呼出しを消したり、置き換えの同値が揃わないまま依存を付け替えたりしない。この周の新たな削除ファイル 0、削除宣言 0、import 移動 0。比較用逆参照リストの sha256 は `9b00fe1973e5c52299cde530ecb236189261c73aae2744400d8d7685b42d47e1`。