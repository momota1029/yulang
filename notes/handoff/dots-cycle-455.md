この周に閉じた G の行: **なし。G04 は部分進捗、残り19行。**

# C455 引継ぎ

- 実開始: 2026-11-27 02:30:00.002 UTC。通常完了の下限は 03:20:00.002 UTC。実終了時刻と解放は同コミットの heartbeat に記録。
- 権威: `integration/m1-final@1bfc617f7862599f56986061d890db50f1c5e4ea`（Lean `70c45bac822ff9e58c2b1b1a5a589b41125a732f`）、I-85 採用済みの C454 が基線。この周は G04 のみ。G03b / G05 以降は未着手。
- 検証済み成果: [科学成果の固定コミット](https://github.com/momota1029/yulang/commit/0806a62d68680c657f08376067c770a57b906e35)、Lean `54e8b8050b48e032ca76a6392d9b82776cd3feee`。統合先ではなく `work/dots-main` 上の成果。

## 届いた範囲

§6.3 の実宣言から、単一の可視候補の point 親、where 一つ、親・子とも名前付き出力指定なしの範囲で、有限深さの閉じた名前付き record field の K2 を追跡する。候補側の正規化済み pattern と観測側の実 field を別々の位置で照合する。途中の各地点では raw Alias、元の native syntax、同じ issuer を含む正しい OriginRoute、およびその地点が K2 でないことを再確認する。最後は本当に訪問された非変数 field の raw K2 を検査し、その地点には開くための由来を要求しない。未訪問の field や変数捕獲下の循環はこの診断の根拠にしない。

- 独立した判定は `RecordTraversal455.exact_cycle_visit_iff_finite_wire455` と `RoutedRecord455.routed_field_diagnosis_is_precise_source_trace455`。途中で開く正確な出所は `RecordRoutedOrigin455.routed_open_iff_finite_same_origin_wire455`。原文の分岐した閉 record head と実 where は `RecordTreeHeader455` で照合。
- `RoutedRecord455.actual_routed_field_report_iff_finite_wire455` と `independent_routed_field_derivation_has_cumulative_witness455` は、上記の独立導出から実 occurrence、候補、順序付き field 経路、終点が同じ内部 report になる有限データの witness を与える。
- 累積の入口は **`RoutedRecord455.check_full455`** のみ。`check_full_sound455` は同一の FullState の全 FitsFull について成立する。選択辞書、where 子の検査結果、書込列を捏造しない。以前の witness は全入力で正確な C454 経路へ直接委譲される。開発途中の **`RecordTrail455.check_full455` は非正規の試作**。raw Alias と物理側の Origin だけでは元の論理 site の OriginRoute の証明にならず、正規入口の previous には含めない。
- 同じ実 FitsFull を持つ正例は、実の別名を経由し深さ3で報告する。route 欠落、issuer 違い、raw alias 違い、候補・経路・終点の置換を拒む。中間 field の K2 はその地点で止まる。非先頭の実 field に対する別の深さ3正例では、候補または観測の位置の一方だけをすり替えても false。他の未訪問循環を根拠にしない。

## G04 を開いたままにする理由

任意の bound pattern を通る全域の証明ではない。今回の実経路は閉 record の途中までを対象にしており、nominal・variant 等を途中で開く混在経路や開いた tail の正規入口は未検証。さらに、非先頭 field の binder を保持する実 where の対照例では、全捕獲について CountsCovered、Smaller、StableSmaller が成立しても、既存の固定 ConservativeSmaller は不成立になり、同じ原宣言の DeclarationChecked は構成できない。これは現行の証明入口の制約であり、言語上の拒否を意味しない。次は混在経路を元の索引と由来に結び、非先頭 binder の原宣言を既存契約に沿って扱えるか検証する。spec、既存規則、表示方針は変更していない。

## 確認

公開追加は production 10、独立 Audit 13。凍結対象は ID のみ確認し、旧 production 7,759 ファイル、旧 Audit 2,170 ファイルは全ハッシュ一致。集約は import 10 行の追記のみ。公式 Lean 4.35.0、`--trust=0 -DwarningAsError=true` で、Git の固定バイトの対象再生と独立の production-only Audit を確認。`#print axioms` 66 件は標準公理のみ（または公理なし）、`#guard_msgs` 実行回帰4組。全体ビルド、verify-lean.sh、Rust、parser は未実施。
