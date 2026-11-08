# X13–X21 Yulang2 oracle（cycle2部分）

基点: Y2 main d4c8bc8fc8a49173180932cd25921a2c41057354、spec integration 3fdd6c3ac。既存binaryを使用、実装変更なし。自己完結名 `list` は標準ライブラリlistではなく同型のrecursive enumとして宣言した。型区間そのものはsurface構文ではないため、下記は直接観測できる範囲と内部unitを明確に分ける。

| ID | 試験入力 | 実際 | spec期待 | 分類・忠実度 |
|---|---|---|---|---|
| X13 | x13-shared-box: 同一xを `box 'b` と `box 'c` を要求する二関数へ渡す | check0, dump0。双方の引数は同じ `box 'b` に合流。既存unit `merge_cons_by_path_combines_interval_lower_and_upper_bounds` PASS | lower/upperを足し交差条件・共起を解く | 局所挙動は一致。直接lower/upper stateをsurfaceから指定できないため完全なX13外側oracleではない。 |
| X14 | x14-nested-lists-self-contained | check0、dumpのbothは `('a & list(list int)) -> 'a`。内部unit constructor_args_propagate_invariant_neutral_bounds PASS | 入れ子を深さ制限なく処理 | 実機で表せない（一般深さ・内部交差条件をCLI出力だけでは観測不可）。有限深さ2の近似例のみ実行した。 |
| X15 | x15-same-head-bounds-self-contained | check0、dump `list(box 'a) -> (list(box 'a) -> ['b] ()) -> ['b] list(box 'a)`。内部unit sandwich_lifts_list_and_reuses_common_interval_var PASS | 同頭constructorを持ち上げる | 局所例は一致。A/B任意区間そのものをsourceで指定していないため完全な外側oracleではない。 |
| X16 | x16-distinct-head-bounds-self-contained | check0、dumpに `list(box 'a | list 'b <: box 'a & list 'b)` が残る | 異頭は区間として残る | 表示上は一致。入力は上下片側だけでなく両区間の合流を起こす近似例。実際にその型の値が存在/実行できるとは主張しない。 |
| X17 | x17-literal-type-self-contained | check1: `|` と `&` に syntax error。dumpはexit0でも誤回復したtuple表示なので採用不可 | 不変内の関数位置も区間 | 実機で表せない（要求されたinterval表示は旧Y2の注釈構文でない）。generated-function-intervalという別の近似例はcheck0で引数・戻りがintに合流するが、元のopen区間とは異なる。 |
| X18 | box/box2/reset/streamの元宣言、record user_id→int castを伴うwiden | check0、dumpは全nominalで不変interval風の型。frozen boxのrunは `user_id({value:7})` を返し変換を確認できない。nocast box int→box textはcheck0/run1 `conflicting type candidates: int vs text` | box/box2/reset/stream共変 | 違う／部分。旧loweringはnominal Applyの全引数をlower_invariant_argへ入れる。CLI受理を宣言variance判定の一致と扱わない。 |
| X19 | chain/left/right宣言。chain user_id→chain intを既存値に適用 | check0/run0。直接注釈の例はchain::link(7,..)、関数経由はchain::link(user_id({value:7}),..) | 不変のためwiden拒否 | 違う。旧実装はこれらsource境界を拒否しない。全nominal一般論・健全性を推論しない。 |
| X20 | phantomの元宣言。phantom int→phantom text（castなし） | check0/run0 `phantom::next(phantom::end)` | unused | 受理挙動は一致。ただしunusedというmetadataをCLIから直接観測していない。 |
| X21 | exact ref宣言＋apply_ref、effectful callback、一般化されたholder field | ref宣言とpure callbackはcheck0。effect callbackはcheck0/run1 `unit vs int`。holder idはint/str両方run成功だが定数1実装もcheck0/run成功でstr入力から1を返す | field-local forall、作成時rigid、使用毎instantiate | 違う／部分。元のsub/return/... sourceは旧構文・prelude依存でそのまま実行不可。refの高階型の受理だけは確認。rigid creation対照のholderはspec同一規則の別例。 |

## 出典と注意

- 最新 spec/06-roles.md §6.5、spec/04-types.md §4.6。具体variance宣言は notes/questions/2026-11-08-b5-declaration-recursive-variance.md の区別例。
- 旧 lowering/mod.rs: SignatureType::Apply は全argumentをlower_invariant_argへ。これは現在specの宣言時variance tableとは別。
- 旧 compact/tests/case_02.rs: interval merge・sandwichのunitを選択実行。constraints/tests/case_01.rsのconstructor invariant propagation unitも実行、計3test PASS。
- CLI dumpはsyntax/type diagnosticsがあってもexit0になる例があり、check/runを併用した。
- 初回の user_id tuple `.0` は旧parserが浮動小数点適用に解釈して失敗。record版へ翻訳した。`use` をbinding名にした試行も予約語で失敗し `apply_ref` に修正。失敗試行は原ログに保持。
- 全sourceとcommand/exit/outputは results.jsonl、unit全文はunit-log.txt。実装・既存testsは変更なし。

追加出典: 旧 web/docs/ja/reference/types.md 211–214 は union/intersection に安定した source 注釈構文が無いと明記。X17 の syntax 拒否は旧資料と整合し、表示式を直接sourceに書けないことを示す。
