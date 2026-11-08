# Cycle 3: 完全性側の受理候補と whole-record spread の境界

基点: 新spec `816ed8f1d`、旧Y2 `d4c8bc8fc`。新specを権威とし、旧実機の成功をLeanの完全性証明とは呼ばない。旧の単一field record表記と新§3.1の末尾comma規則は別であり、下記は旧処理系に通る綴りで試験した。

## 受理して意味のある10候補

全て `--no-prelude check` / `dump --poly` / `run --print-roots` を実行して正常終了した。source・command・stdout・stderr・時間の全文は添付raw logs。IDとsourceはraw内のcase名を参照。

|ID|旧文書の規則|実機run|新spec|Lean対応・限界|
|---|---|---|---|---|
|C3-ACCEPT-01 poly-value|types.md Value restriction: 関数値idの一般化|`[(7, "seven")]`|4.7 一般化|Coreの型判断・一般化断片はあるが、このsurface例をそのままLeanで検証していない|
|C3-ACCEPT-02 width-record|types.md Record: 余分なfieldを持つrecordのprojection|`[(7, "seven")]`|4.3 幅部分型|Common.common_record_iffは局所順序の分解。source parser/runtimeの例との同一性は未検証|
|C3-ACCEPT-03 default-union|types.md Record: defaultがoptionalを作りpayloadとfallbackのunionを返す|`[(1, "wide")]`; scheme `{width?: 'a} -> 'a \| int`|3b.3、4.3|CommonSourcePatternGeneration.generatePattern_exact/defaultFieldは独立pattern判断へのexactness。任意surfaceの完全性とは別|
|C3-ACCEPT-04 curried-pair|functions.md 引数とcurry: partial applicationとC風呼出|`[((7, "seven"), (1, true))]`|3.3、3.4|lambda/applicationの核規則はある。partial application成功のみからcomputed binding一般化を主張しない|
|C3-ACCEPT-05 composed-poly|functions.md lambda/curry、types.md一般化: 高階composeを異型に利用|`[(7, "seven")]`|3.3、4.7|Common.common_arrow_iffは局所比較。全surface高階推論の主型性をこの実行から主張しない|
|C3-ACCEPT-06 nominal-recursive-case|types.md再帰、control-flow.md case: 名前付きtreeを実再帰で処理|`[7]`; scheme `tree -> int`|4.5、4.7、3.7|X12のrole定数body例より実再帰を増やした候補。一般再帰関数の停止性ではない|
|C3-ACCEPT-07 record-first-wins|types.md Record spread/default: 先行baseのxを保持し欠落時fallback|`[(7, 9)]`|4.3先勝ち、spread-default|Common.default_present_record/ default_exactEmptyは局所型法則。全runtime対応は未検証|
|C3-ACCEPT-08 phantom-text|types.md nominal/推論、X20 phantom retag|`[phantom::next(phantom::next(phantom::end))]`|6.5 unused parameter|X20より一段深い具体retag。general nominal variance metadataの検査とは別|
|C3-ACCEPT-09 variant-case-join|types.md推論union、control-flow.md case: some/noneを返して再照合|`[(7, 0)]`|4.5 variant、3.7|Common.common_variant_iffは局所順序。この閉じたsurface例のinfer証明は未実施|
|C3-ACCEPT-10 record-pair-pattern|functions.md lambda/tuple pattern、types.md record|`[(7, "kept")]`|3.4、3b.1、4.3|CommonSourcePatternGeneration.generatePattern_exact等でpair/field構成子を扱うが、これ自体のsurface-to-Lean照合は未実施|

C3-ACCEPT-08は当初 `phantom str` と書いてno-preludeで `str` 型未解決になった。opaque `type text` を宣言した正しい自己完結形で再試験。C3-ACCEPT-09は当初 `if` の標準junctionが未importで失敗したため、同じ有限分岐をcase boolで表現し再試験。初回エラーを「新specの拒否」と数えない。

## 新たに観測した境界: whole spread返値の後段projection

旧types.mdは `keep_input {width, ..input}=input` のspreadが入力全体を返すと明記し、新spec3b.3も同じ。次の旧Y2入力はcheck成功し、dumpは期待したgeneric shapeを表示する:

```yulang
our keep {x, ..whole} = whole
(keep {x: 7, y: "kept"}).y
```

しかしrunは `unsatisfied subtype constraint: {x: 'open2} <: {y: 'open0}` で拒否する。

対照:
- `keep {x:7,y:"kept"}` そのものはrun成功し `{x:7,y:"kept"}` を返す。
- `(keep ...).x` は7。
- body内で直接 `whole.y` を要求すれば `"kept"`。
- 単なるid `our keep whole = whole` の返値に `.y` は `"kept"`。
- 即時lambdaをmonomorphic bindingにした返値の `.y` もrun拒否 (`{x:int} <: {y:...}`)。一般化だけの問題とは断定しない。
- `{..whole}` と再構築して返しても `.y` はrun拒否 (`{} <: {y:...}`)。

したがって、旧matcherのwhole record保持そのものの否定ではなく、返値を後段で使用する境界での拒否を確認した。source specを変えるべきとは提案せず、完全性側の回帰候補として積む。Leanのfield ruleはrestにも同じinputを渡す（CommonSourcePatternTyping.RawTyping.field）ので局所pattern判断は入力全体保持を表すが、この旧Y2のprojection拒否をLeanが再現/排除すると証明したわけではない。

## 実行数と制限

初回10例×3=30呼出、追補9例×3=27呼出、計57呼出。全て20秒上限内、timeoutなし。初回30呼出はYULANG_CACHE_DIR未指定でread-only home cache警告を出したが、コマンドは上記終了値を返した。追補は既存workspace cacheを指定した。これらの警告もraw全文に保存。既存ソース/Lean/spec編集なし、Leanビルドなし、標準prelude対照なし。
