# Dots cycle 407 — I-73: 規則の和 R₀ の辞書健全性

**I-65 (1): 固定した `DictionarySound R0` を work/dots-main で証明・検証した。integration への取込みは別に確認する。(2)・(3): 未実装。**

- 開始時は I-72（integration `4a5266b2e40ea2a7cca69a2d005a025153663d5c`）で、前回は完了済み C406 `97d56e91f7f2df191f9b511742f75b5045a5047b`。途中で I-73（integration `33b9dda79b70ab67b183b9edcb0cad8e5a576212`、inbox blob `353a3cd10aa7137fc095478c52f615948dbda71e`）を確認し、範囲拡張を停止した。I-72 のうち既に同 branch に出した、全可視の単項候補の元順・別タグ不一致・元 B6 の参照の局所結果（`9cd20701cb5b574ee9b2a6985a9e2bc53e44e788` まで）はそのまま残す。確認以降、未公開の I-72 断片は加えず、R₀ にも入れなかった。

## 証明した固定命題

- [`dictionary_sound_R0 : DictionarySound R0`](https://github.com/momota1029/yulang/blob/00d3757c241a32652454d67c97e708296ca39b9a/lean/Yulang/GeneralDeclarativeI65I73RuleUnion407.lean#L127)。C403〜405 の **8 つの既存の局所規則**を `R0` に合わせた。システムごとの完成済み結果の選言ではない。同じ State の一つの導出で、親、元の関連型出力を作る producer、および順序付き where の子が別の規則族を使ってよい。
- 各局所規則から、同じ原文 Event の `GeneralNode` と固定先の保持を示した。C402 の有限 `SourceTrace / WhereForest / SupportForest` と再帰 lowering はそのまま使い、[実際の混合導出の一つの ledger](https://github.com/momota1029/yulang/blob/00d3757c241a32652454d67c97e708296ca39b9a/lean/Yulang/GeneralDeclarativeI65I73RuleUnion407.lean#L111) から、**任意の State・Request・選ばれた Dictionary・任意の fitting Model** で、定義を変えていない C402 `DictionaryEvidence` を導く。新しい証明を `Classifies` の前提や witness に入れていない。
- 旧各規則の導出は、同じ event、元出力の receipt、要求、診断木を保ったまま R₀ に埋め込める。[`actual_mixed_native_support_enters_variable_rule407`](https://github.com/momota1029/yulang/blob/00d3757c241a32652454d67c97e708296ca39b9a/lean/Yulang/GeneralDeclarativeI65I73RuleUnionSupport407.lean#L49) は、実際の authored-native 系 producer と元の出力、supported-variable の親、別の R₀ where 導出を組み立て、同じモデルで同じ ledger を解釈する。[`R0_original_support_on_one_same_model_ledger407`](https://github.com/momota1029/yulang/blob/00d3757c241a32652454d67c97e708296ca39b9a/lean/Yulang/GeneralDeclarativeI65I73RuleUnionSupport407.lean#L18) は指定した元の出現・出力番号・固定先も保つ。
- [局所診断の競合排除](https://github.com/momota1029/yulang/blob/00d3757c241a32652454d67c97e708296ca39b9a/lean/Yulang/GeneralDeclarativeI65I73RuleUnionPriority407.lean#L54)。可視全体の元構文から、R₀ の選択が表現済みの曖昧さまたは実際に到達した K2 を飛び越さないことを証明した。raw root K2 は支持集合から独立したまま。[完了した実 producer が許す子 K2](https://github.com/momota1029/yulang/blob/00d3757c241a32652454d67c97e708296ca39b9a/lean/Yulang/GeneralDeclarativeI65I73RuleUnionPriority407.lean#L85) は R₀ の正しい固定行から得られる。R₀ を変えず、[二つの局所入口に正規化できること](https://github.com/momota1029/yulang/blob/00d3757c241a32652454d67c97e708296ca39b9a/lean/Yulang/GeneralDeclarativeI65I73RuleUnionNormal407.lean#L78)も確認した。

## C と次の段階

- [C の初期 8 行](../design/dots-cycle-407-i73-coverage-list.md)。C406 の authored lower がない完了出力例は、元の `SourceHead` を要求する固定 C402 Event に入らない。[任意の規則の和では解消しない](https://github.com/momota1029/yulang/blob/00d3757c241a32652454d67c97e708296ca39b9a/lean/Yulang/GeneralDeclarativeI65I73FixedCarrierLimit407.lean#L13)ことを証明したので、結論の違う `ScopedEvidence406` の定理を R₀ の証拠として扱っていない。R₀ の狭さは言語拒否ではなく C。残してある C380 文面・I-65 文の変更や、旧 S13 の追加分割はない。
- [既存 checker の再利用経路](../design/dots-cycle-407-i73-checker-interface.md) と [正の分岐で確認すべき入力](../design/dots-cycle-407-i73-checker-positive-entry.md)。C350 の raw-cycle witness からは fixed State/root への直接の接続が見える。他の旧 checker の受理は、元の出現・B6 型付き本文・固定先・順序付き receipt をもう一度同じ Problem で確認しない限り R₀ の受理にしない。正の入口に C403 の実 variable leaf を調べた。新しい検査器/健全性はまだ実装していない。

## 検証・公開範囲

- 技術 pin `00d3757c241a32652454d67c97e708296ca39b9a`、Lean tree `a7490fbc64b282fbd11a113f93673d4c35b23659`。C407 全 11 新規 Lean ソース・11 独立 Audit を exact Git blob で取り直し、別に用意した生成物ディレクトリで `lake env lean --trust=0 -DwarningAsError=true` を実行（ソース・各 Audit・追加 import 監査、すべて終了 0）。Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。43 宣言の公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
- I-73 分だけの 6 ソース・6 Audit も、C407 I-72 増分の生成物/追加 import なしで exact Git bytes から独立 replay、終了 0。22 宣言、標準公理のみ。開始後の integration の Lean tree は C406 の独立 replay と同一。barrel は旧 prefix を全バイト照合し、末尾に新規 11 import のみ追加。凍結 2 ファイルは blob ID のみ確認、変更なし。新規 Lean に切り詰め・新公理・未実証箇所なし。
- 最終報告と心拍を含め 30 パスを照合し、expected-head non-force で `work/dots-main` のみ更新。全リポジトリ build / `verify-lean.sh` は監督役向けで未実行。Rust/Yulang2、停止性、旧 Local/C334、fixture、言語仕様は対象外。質問なし。使用枠は不明。
- 最終確認時の integration: `33b9dda79b70ab67b183b9edcb0cad8e5a576212`。R₀ の定理ファイルは未掲載。I-73 の (1) 完了扱いは integration 取込み後。
- 最終照合開始 `2026-11-25T03:20:54.774Z`（50 分経過）。
