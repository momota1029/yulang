# Dots cycle 408 — I-73: 一つの検査器と、受理した報告の健全性

**I-65 (1) は integration で確認して完了。(2) の `check` と (3) の `check_sound` は work/dots-main で実装・検証済み。**

- I-73 inbox `353a3cd10aa7137fc095478c52f615948dbda71e`。開始 integration `bcc13d217bd7d9dd65be080caa01fbb8cec201e1` の [`dictionary_sound_R0`](https://github.com/momota1029/yulang/blob/bcc13d217bd7d9dd65be080caa01fbb8cec201e1/lean/Yulang/GeneralDeclarativeI65I73RuleUnion407.lean#L127) は C407 の exact blob `8af8804db399afe2753bfdb68c55b22b460e6b1f` と一致。R₀ や固定 `DictionaryEvidence`、spec は変更なし。

## 2. 同じ Problem の検査器

- [`check : Problem → Result → Witness → Bool`](https://github.com/momota1029/yulang/blob/37056fbbc1bc8bb0235468b95f4c8fcadb45a0f6/lean/Yulang/GeneralDeclarativeI65I73UnifiedEntry408.lean#L21) を一つにした。公開入口は `Checker408`、先に出した `Check408` はその内部エンジン。Witness は検査すべき元の有限データで、分類・モデル・受理の証明を受け取らない。使う State、元要求、可視候補、宣言表はすべて同じ Problem から読む。
- C350 raw-root K2 は、元の普通制約のグラフで該当の引数からの実下降と閉路を検査。要求に対して rejected tree / verdict、実書込みが空の場合だけ同じ報告として受理する。もう一方は C403 の実際の nullary 選択。全可視リストがちょうど一候補で、同じ元の C349/C357 表が検査を通り、空の引数・head・where・出力の要求に一致することを調べる。候補 ID から出す tree と辞書、書込み列をその報告と比較する。先行実装では C349 の fallback arity=0 が元 role 宣言なしでも通ることを見つけ、その入力をテストで再現した。公開入口は同じ元要求の実 authored role 行も確認し、fallback のみなら false。raw K2 はこの guard に依存しない。
- 未対応は false。実行上の不受理を新しい言語拒否または保留にしない。実書込みがある報告、非空引数・where・他の native／ambiguity 証人はこの checker の対象外。R₀ と spec の差を増減せず、[この checker の別の境界](../design/dots-cycle-408-i73-check-boundary.md) を記録した。

## 3. 同じ報告の健全性

- [`check_sound`](https://github.com/momota1029/yulang/blob/37056fbbc1bc8bb0235468b95f4c8fcadb45a0f6/lean/Yulang/GeneralDeclarativeI65I73UnifiedEntry408.lean#L64) は、任意の Problem / Result / Witness で check が true なら、[`ClassifiedAs`](https://github.com/momota1029/yulang/blob/37056fbbc1bc8bb0235468b95f4c8fcadb45a0f6/lean/Yulang/GeneralDeclarativeI65I73UnifiedReport408.lean#L94) が同じ要求・報告木・summary・元出力順の実 `SourceTrace R0` を与え、同じ State の **任意の fitting Model** で [`ReportEvidence`](https://github.com/momota1029/yulang/blob/37056fbbc1bc8bb0235468b95f4c8fcadb45a0f6/lean/Yulang/GeneralDeclarativeI65I73UnifiedSound408.lean#L35) が成り立つことを示す。選択ノードの head、元の型つき RHS、固定先、成功した子の辞書を同じ木で示す。
- [`accepted_report_fixes_one_trace_before_every_model408`](https://github.com/momota1029/yulang/blob/37056fbbc1bc8bb0235468b95f4c8fcadb45a0f6/lean/Yulang/GeneralDeclarativeI65I73UnifiedLedger408.lean#L56) は同じ導出と書込みをモデルの量化の前に固定する。成功時の出力リストは C402 の canonical ledger と親 / where の順序で一致。型の項を平坦化せず、出現、元宣言の番号、出力番号、固定先と元本文を区別する。非空の書込みを checker 自体が検査するように範囲を増やしてはいない。
- 統合用テストでは同じ入口で既存 C350 閉路と元メタデータから作った C403 nullary 選択が true。後者には実際に fitting Model があり、辞書の証拠も得た。別の辞書、別の診断木、余分な実書込み、候補行を追加、誤った閉路の閉じ方、未対応タグは false。

## 検証と引継ぎ

- exact 技術 pin `37056fbbc1bc8bb0235468b95f4c8fcadb45a0f6`、Lean tree `e56a047896733a1d668f94d44d03fb38fbe110d8`。新規 7 ソース、独立 Audit 9 本、統合テスト用の既存依存 3 本を固定 Git bytes から取り直した。Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` で別の生成物ディレクトリから `lake env lean --trust=0 -DwarningAsError=true`、終了 0。43 宣言、標準 `propext`・`Classical.choice`・`Quot.sound` のみ（部分集合を含む）。独立 audit 内の統合テスト宣言はその audit で検証し、追加 import だけの監査では production 宣言を検証した。Lean の `#eval` でも旧 fallback/公開入口の role なし/role あり/raw K2 が `true / false / true / true`（終了 0）。barrel の旧 prefix 全バイトと新規 7 import を照合。凍結 2 ファイルは blob ID のみで一致。
- 変更は報告・心拍込み 21 パス。expected-head non-force で work/dots-main だけに公開した。次は (2)・(3) の integration での exact 確認。現在の check の対象外を C として扱う。Rust/Yulang2、停止性、旧 C334/Local、全 workspace build や監督役向け `verify-lean.sh` は実行していない。利用枠は不明。
- 最終確認時の integration: `bcc13d217bd7d9dd65be080caa01fbb8cec201e1`。(2)・(3) の正本は未掲載で、作業ブランチの検証済み成果。
- **時間上限による引継ぎ（通常完了ではない）**。実開始 `2026-11-25T03:34:52.000Z` の 50 分到達は `2026-11-25T04:24:52.000Z`。04:25 UTC の上限まで 8 秒しかないため、公開・独立照合前に切り上げた。技術成果の検証は完了しており、この引継ぎで作業者は終了。
- 最終照合開始 `2026-11-25T04:22:11.605Z`（47 分経過）。
