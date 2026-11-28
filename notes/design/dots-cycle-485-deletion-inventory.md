# I-98 段階 2: C485 削除準備の照合（削除 0）

権威 `eaef0baeaafc45b3e35c983dfbcd7c1137c1b5e5`、既存 Lean tree `7d628991f34a959ce24f47d9882807477b4a0c2e`。対象は C481 の全入力 Bool同値を持つ18入口。下表の各行は既存の独立 Audit に実際の直接 import があり、全て `lean/Yulang.lean` からも直接 import されている。置き換え列は C481 の証明名であり、その証明に旧入口自体が言及される。削除・import 移動は今回なし。完全な逆依存リストでなく、各候補が不適格なことを示す確認済みの直接依存だけを記す。

| 対応する旧入口のファイル | 平坦側との既存 Bool 互換 | 確認した現行の直接 import |
|---|---|---|
| `lean/Yulang/GeneralDeclarativeI65I74RetainedSplitEntry446.lean` | `retained_same_Bool481` | `lean/Audit/Cycle446I74RetainedSplitEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74WhereSamePhase454.lean` | `rawGrouped_same_Bool481` | `lean/Audit/Cycle454I74WhereSamePhase.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74WhereGuard450.lean` | `guardedWhere_same_Bool481` | `lean/Audit/Cycle450I74WhereGuard.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74SelectedEntry447.lean` | `selected_same_Bool481` | `lean/Audit/Cycle447I74SelectedEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74OpaqueEntry448.lean` | `opaque_same_Bool481` | `lean/Audit/Cycle448I74OpaqueEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74OpaqueWholeEntry448.lean` | `whole_same_Bool481` | `lean/Audit/Cycle448I74OpaqueWholeEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74ListSiteEntry449.lean` | `listSite_same_Bool481` | `lean/Audit/Cycle449I74ListSiteEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74ListFrameEntry449.lean` | `listFrame_same_Bool481` | `lean/Audit/Cycle449I74ListFrameEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74WhereGroupedEntry453.lean` | `grouped_same_Bool481` | `lean/Audit/Cycle453I74WhereGroupedEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74RoutedRecordEntry455.lean` | `fieldRecord_same_Bool481` | `lean/Audit/Cycle455I74RoutedRecordEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74RoutedMixedEntry456.lean` | `fieldMixed_same_Bool481` | `lean/Audit/Cycle456I74RoutedMixedEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74RoutedNominalMixedEntry456.lean` | `fieldNominal_same_Bool481` | `lean/Audit/Cycle456I74RoutedNominalMixedEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74RoutedReadyRecordEntry457.lean` | `fieldReadyRecord_same_Bool481` | `lean/Audit/Cycle457I74RoutedReadyRecordEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74RoutedReadyMixedEntry457.lean` | `fieldReadyMixed_same_Bool481` | `lean/Audit/Cycle457I74RoutedReadyMixedEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74RoutedInlineVariantEntry458.lean` | `fieldVariant_same_Bool481` | `lean/Audit/Cycle458I74RoutedInlineVariantEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74RoutedInlineStructuralEntry458.lean` | `fieldStructural_same_Bool481` | `lean/Audit/Cycle458I74RoutedInlineStructuralEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74ProjectedClosedEntry459.lean` | `fieldProjected_same_Bool481` | `lean/Audit/Cycle459I74ProjectedClosedEntry.lean` |
| `lean/Yulang/GeneralDeclarativeI65I74HomogeneousClosedEntry459.lean` | `fieldHomogeneous_same_Bool481` | `lean/Audit/Cycle459I74HomogeneousClosedEntry.lean` |

- `lean/Yulang/GeneralDeclarativeI65I74FlatDispatch481.lean` は C446 の retained checker を直接呼び、G03 群・G04 の旧 local field leaf 群も直接参照する。C459 の最上位は `...InstalledSameBoolean462.lean` の `factorExisting` 互換・既存健全性に残る。いずれも単に入口の型が平坦になっただけで削除とはならない。
- `lean/Yulang/GeneralDeclarativeI65I74WhereEntry450.lean` は18入口に加えて守る既存 raw where で、`lean/Audit/Cycle450I74WhereEntry.lean` と umbrella に現行直接 import があり、平坦側健全性の guarded where からも実際に呼ばれる。
- 権威の `tools/verify-lean.sh`（blob `127f7383570ee8e459a9e2a904aa601ffb92ab35`）は既存 Lean の削除行が1行でもあれば失敗する。C485 専用のパス限定例外・監督役の全体検証成果は確認できなかった。ユーザーへの再承認は求めず、本周は明細だけ。次は Audit/C481 互換参照の置き換えと、明細を指定した検査の準備を分ける。
- C485 の段階 2 変更だけの前後: 削除ファイル 0、消した宣言 0、既存 import 移動 0。C485 の G04Entry/G05 の新宣言数は別集計とする。
