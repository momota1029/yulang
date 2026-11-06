# 要求順序と constructor 観測に残る契約

状態: **問い。未回答部分は言語仕様の変更として扱わない。**
日付: 2026-11-07。決定46・47、既存 Q2 の案1、Q3 の独立 `exactEmpty` を前提にする。

## Q4. constructor の payload 内でも mask を観測するか

**問い:** 要求の文法の `mask` は、pair/field/tag の子に入った後でも独立に使えるか。

例: `P = required 7 bottom`、`B = bottom` とする。既存 data 観測では unmasked な `P` と
`B` は等しいが、mask `[7]` の後は `P` だけが records を許す。
現在の `PresenceMaskedCoalescing` は root の全 mask を調べ、variant の子は unmasked に読むため、
`variant 11 P ≤ variant 11 B` は成り立つが、子の全 mask 比較 `P ≤ B` は成り立たない。

`PresenceConstructorObstructions.MaskedPayload` の `input_model` が4-node入力の独立解を構成する。
`no_closed_cache_preserves_model` は、この解を保存する現行 `Closed` cache が一つもないことを示す。
`no_exact_closed_alternatives` は、同じ graph 上の任意の有限 cache 列に対して完全性を否定する。
これは、別の観測・obligation 表現や graph を拡張する手続きまで否定する定理ではない。

選択肢:

1. **推奨:** 要求の mask を構成子の内部でも許す。新 `ProducerLe` の観測を文脈内まで閉じ、
   子の要求比較を親の要求比較から回収できるようにする。既存の root-mask data モデルは別の投影として残す。
2. root-mask data モデルの観測をそのまま保持し、cache に「子を unmasked に比較する」辺と
   「root を全 mask で比較する」辺を別々に持たせる。coalescer と回収定理もこの区別に合わせて構成する。

**仮の作業前提:** 既存の data 型判断・`Models`・`Closed` は変更しない。
現時点の constructor-bound 定理はどちらの選択にも依存しない。
新たな要求モデルにおける mask の具体的解釈は、その定義と依存する定理の前提に明示する。
選択肢1の最終採用や、全 source への接続をこの問いの記録だけで済ませない。

## Q5. 要求の型変数で `int | str` と `any` を区別するか

**回答済み(2026-11-07): 案1。** 区別する。要求の型変数を有限 rigid 観測列の略記に限定しない。
ユーザーからの注意: これは SubML ではなく **Simple-Sub** である。`case` の pattern に型は書けない。
引数の位置(負)に `int | str` は現れず、`int & str` と推論される。`bool <: int & str` ではないので、
`int | str` を受ける関数に `bool` を渡す例は、普通の型エラーであり、型安全性の問題ではない。
区別が必要になる要求は、型変数に付く role 制約(`'a: Display` のような)など、union-free な要求の語彙の中にある。
要求の語彙に何を含めるか(変数、mask、role 制約)は、モデルの定義として明示する。
以下は質問の記録。


**問い:** union-free な要求に型変数を含めるとき、その変数が受ける型は、有限個の rigid な
観測の共通部分で表せるものに限定するか。それともその範囲を越える未知要求を保持するか。

例: 現在の候補 `ProducerDemand.Environment` は `Nat → List Observation` であり、要求の変数を
任意の有限観測列へ展開する。int と str に共通する rigid な観測は自明な要求しかないので、
この候補では全 rank・全要求環境について `int | str` と `any` の要求が一致する。
`ProducerDemandExpressiveness.distinct_bases_union_equivalent_top` と `mixed_union_accept_iff` が、
任意の行関係についてこの境界を証明する。
これは同じ構成子の union を成分でまとめる決定47だけからは出ない、追加の表現上の境界である。
要求の構文から union を除くことと、変数の意味をこの有限観測列へ限定することを区別する。

選択肢:

1. **推奨:** `int | str` と `any` は区別する。要求の型変数を有限 rigid 観測列の略記へ限定せず、
   構成子のまとめ等式と旧部分型の保存に整合する未知要求として保持する。
   要求の構文には union を追加せず、変数の解釈・束縛・許容する具体化を別に定義する。
   例えば `int ≤ α` と `str ≤ α` の下界を持つ共有変数を、`any` と区別したまま扱える必要がある。
2. finite rigid 観測列で尽くされる要求を採用し、この文脈では `int | str ≡ any` を認める。
   表示で `int | str` を残す場合、それは完全な要求同値の一意な標準形とは別の表示方針とする。

**仮の作業前提:** 既存の証明を消さず、`ProducerRanked` / `ProducerRankedRegular` は有限 rigid 観測に
基づく候補モデルとして公開する。前順序・旧部分型保存・構成子 grouping・同じ旧 scheme の
instance 保存/同値を除く反映は、この具体的な要求解釈についての定理である。
これを変数の解釈まで確定した最終共通モデルとは主張しない。
`ProducerNormalForm.normalize` も成分をまとめる同値保存 pass であって、全同値類の一意な代表を
計算するものではない。open-tail の表現移送と、既存 data モデルの constructor 境界はこの選択に依存しない。

また現在の arrow-domain probe に渡す `Negative` は閉じた union-free 型であり、その内部には
変数/mask を含まない。要求全体には変数/mask があるが、任意の引数型をこの閉じた probe だけで
分離できるという補題は未証明である。これを要求された完全な型変数処理と読み替えない。
閉じた `Negative` 自体を target 引数にする場合だけは、
`ProducerRankedArrowInversion.arrow_negative_argument_iff` が行反射律・推移律の下で
4成分の arrow 比較を完全に回収する。この限定された分解は任意の target 引数の分解とは別である。
