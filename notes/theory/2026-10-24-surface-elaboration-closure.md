# 静的 Yumark の全展開と型導出の構成

Status: research derivation; independent review pending.
Parent: 全表層構文から source 型健全性への接続。
Scope: 下記で定義する静的 Yumark 木と、凍結 lowering の成功経路。
Not claimed: 全 Yumark 構文、parser の正当性、現行推論器の完全性、全言語の証明閉鎖。

## 1. この証明が埋める箇所

[ソース稿](../../docs/yulang-source-type-safety-ja.tex) §14 は Yumark を二引数の builder にする外殻だけを展開し、内部の node を未処理としていた。本稿では静的 node の全場合について、展開関数、型の導出、計算の置かれる場所を与える。任意の「安全な builder」を外から受け取る前提は用いない。

照合対象は Yulang2 の Git object `a58eefc31e22141574b6f20c6a5748151c6d79f1` にある次の二ファイルである。

- `crates/infer/src/lowering/yumark_lit.rs`: `lower_yumark_node`、`lower_yumark_sequence`、`yumark_chain`、`yumark_static_operation`、`lower_yumark_builder_lambda`。
- `lib/std/text/yumark.yu`: `yumark_algebra` と `nil` から `strong` までの builder 定義。

ソース稿の基準は commit `424566114`。上記の古い実装を新しい言語仕様の権威にはしない。そこで実際に定義されている展開を有限の数学的対象として再構成する。commands / inline expressions はこの凍結 lowering 自身が未対応とする。それらは元の全言語目標から除外せず、未完の親義務として残す。

## 2. 型と核の記法

値型を `1, Bool, Int, Str, R, F` とする。`R` は表現型、`F` は format の型であり、任意に固定する。`A → B` は Value entry の callable の実行型射影を表す。この記法だけから効果が空であるとは結論しない。

`App(f,e)` は元の完全 Call である。callee を評価し、引数 `e` を保持した carrier を受領してから Value entry が force する。`f(a,b)` は `App(App(f,a),b)` の略記であり、tuple application ではない。

有限レコード型 `Alg(R)` の各 field は次の型を持つ。

| Field | 型 |
| --- | --- |
| `nil` | `1 → R` |
| `cons` | `R → R → R` |
| `text` | `Str → R` |
| `paragraph`, `list_item_body`, `quote_block`, `emphasis`, `strong` | `R → R` |
| `heading` | `Str → Int → R → R` |
| `blank_line`, `code_fence` | それぞれ `Str → R`, `Str → Str → R` |
| `section_close`, `list_item` | `Str → R → R` |
| `list_block` | `Bool → R → R` |

builder の型を `B(F,R) = F → Alg(R) → R` と置く。各 field の whole effect/profile 契約は、実際の field の型導出に保持する。型射影表の各矢印を一律 pure に置き換えない。

以下の式はすべて普通の Lambda、App、field、literal だけからなる。§3 の外殻 W が新たに生成する二つの binder `f,a` だけに、ソース稿の `GeneratedNeutral` を付す。以下の標準 builder の式に現れる binder は、凍結 library 定義の formal を表す略記であり、元の annotation と provenance を保持する。たとえば `cons` の `head,tail` は元 source の無注釈 formal である。これを GeneratedNeutral に置換してはならない。一般の受領と effect transport も残る。

```text
NIL          = λf. λa. a.nil ()
CONS h t     = λf. λa. a.cons (h f a) (t f a)
TEXT s       = λf. λa. a.text s
UNARY_j c    = λf. λa. a.j (c f a)
HEADING m n c = λf. λa. a.heading m n (c f a)
SECTION m c  = λf. λa. a.section_close m (c f a)
LIST o c     = λf. λa. a.list_block o (c f a)
ITEM m c     = λf. λa. a.list_item m (c f a)
FENCE i b    = λf. λa. a.code_fence i b
```

上の `CONS h t` 等は定義式の略記であり、原 source の実行可能な引数計算を β 展開によって複製する規則ではない。表層展開では解決済みの builder 宣言に普通の App を行う。型導出の際にその宣言 body を上の有限式で検査する。

**補題 Y1（builder 宣言の値型導出）。** 任意の `F,R` について、`NIL : B(F,R)`、`CONS : B(F,R) → B(F,R) → B(F,R)`、`TEXT : Str → B(F,R)` および上記全 builder の対応する curried 型の有限導出を構成できる。

**証明。** `f:F,a:Alg(R)` の環境で、field 除去により `a.nil:1→R`、Unit 導入と App により `a.nil():R`。二度の Lambda 導入で NIL を得る。CONS ではさらに `h,t:B(F,R)` の環境で、二回ずつ App を使って `h f a:R` と `t f a:R` を得る。`a.cons:R→R→R` に二回 App し、四つの Lambda を逆順に導入する。TEXT は `s:Str` と `a.text:Str→R` に同じ操作を行う。

UNARY の各 field は `R→R` なので、帰結 `c f a:R` に一回 App する。HEADING は順に `m:Str`、`n:Int`、`c f a:R` を三回 App する。SECTION/ITEM は `Str,R`、LIST は `Bool,R`、FENCE は `Str,Str` をその順で App する。最後に同じ環境を閉じる Lambda 規則を適用する。すべての field を列挙し、他の構成を仮定していない。□

この補題は値型導出の構成である。全 effect inclusion が成立するという追加の結論は含めない。

## 3. 正規化済み静的木

木は有限で、次の constructor を持つ。

```text
d ::= Seq[d1,…,dk] | Text(s)
    | Paragraph(d) | Emphasis(d) | Strong(d) | Quote(d)
    | Heading(marker,level,d) | SectionClose(marker,d)
    | List(ordered,d) | Item(marker,d) | ItemBody(d)
    | Fence(info,body)
```

`s,marker,info,body` は有限文字列、`level` は凍結 lowering の整数 literal 変換が返す整数、`ordered` は Bool である。`level` を無制限の自然数と見なして機械整数の変換と同一視しない。静的木には source の実行可能な interpolation を入れない。

`E(d)` を次のように定義する。各右辺の App は宣言への通常の source application である。

| 木 | `E` |
| --- | --- |
| `Seq[]` | `NIL` |
| `Seq[d1,…,dk]` | `CONS E(d1) (CONS E(d2) … (CONS E(dk) NIL))` |
| `Text(s)` | `TEXT s` |
| `Paragraph(d)` | `UNARY_paragraph E(d)` |
| `Emphasis(d)`, `Strong(d)`, `Quote(d)` | 対応する `UNARY_j E(d)` |
| `Heading(m,n,d)` | `HEADING m n E(d)` |
| `SectionClose(m,d)` | `SECTION m E(d)` |
| `List(o,d)` | `LIST o E(d)` |
| `Item(m,d)` | `ITEM m E(d)` |
| `ItemBody(d)` | `UNARY_list_item_body E(d)` |
| `Fence(i,b)` | `FENCE i b` |

外殻は `W(d)=λf.λa.E(d) f a` とする。`E(d)` の計算は二つの Lambda の内側にある。

**定理 Y2（静的木からの導出構成と停止）。** 任意の有限静的木 `d` と任意の `F,R` に対し、`E(d):B(F,R)` と `W(d):B(F,R)` の値型導出を構成できる。展開と証明構成はいずれも停止する。

**証明。** 木の node 数への強い帰納法。Text と Fence は literal 導入および Y1 の App で直ちに得る。単一 child の各場合は child の帰納仮説を Y1 の対応引数に入れる。Heading の他の引数は Str/Int、List は Bool、Item/Section は Str の literal 導入である。Seq は列長への帰納を併用し、空列では NIL、非空列では先頭の木の導出と残りの列の導出を CONS の二引数へ入れる。各木再帰は真部分木に進み、列再帰は長さを一つ減らす。宣言 body を再帰的に inline 展開する段階はない。

W は得た導出を `f:F,a:Alg(R)` へ弱化し、二回 App、二回 Lambda 導入する。有限である。□

**系 Y3（表現型を変えて使う値）。** `W(d)` の閉じた生成環境に `F,R` が自由に現れなければ、値に対する全称導入を適用できる。その同じ builder 値を異なる `F,R` で使用する導出が存在する。

**証明。** W は非拡張な Lambda 値である。環境自由変数条件を確認し S-AllI を二度適用する。各使用で S-AllE を対応する instance に適用する。E(d) の計算全体を一般化したり、計算を type abstraction の外へ移したりしない。□

## 4. CST 成功経路との照合

CST からの前処理 `N` は凍結 `lower_yumark_sequence` の有限走査を、型推論から分離して定義する。入力は有限 CST と、その CST から `normalize_yumark_tree_blank_boundaries` が計算する範囲集合である。

1. 各 sequence は左から走査する。structural trivia と認定された token を飛ばす。
2. `YmText`/`Space` および option が許す `YmNewline` を text buffer に連結する。
3. 列挙された syntax token は飛ばす。他の token は未定義として成功導出を作らない。
4. structural blank line と `is_empty_yumark_paragraph` が真の child は飛ばす。他の child の直前に buffer を flush し、対応する node を再帰変換する。
5. flush は option に応じ末尾の CR/LF を除き、空でなければ Text を一つ加える。列の最後でも flush する。

INLINE は newline を含め末尾除去をしない。BLOCK_CONTENT は newline を含め末尾 CR/LF を除く。LINE_CONTENT は newline を含めず末尾 CR/LF を除く。この flush は各 child の前にも行うので、「文書全体の末尾だけを trim する」という別の関数ではない。

`YmDoc` は INLINE、`YmParagraph` は BLOCK_CONTENT、heading/section-close は LINE_CONTENT、list-item/list-item-body は BLOCK_CONTENT、その他の container/list は INLINE を用いる。heading は最初の対応 sigil から marker/level を、list は最初に見つかる item sigil から ordered を得る。code fence は `split_code_fence_node_text` と同じ prefix/newline/最後の close の分割を使う。新しい文字列意味論を加えない。

**定理 Y4（構文木出力の対応）。** 上記関数が成功し、凍結 lowering の各 standard declaration lookup が同じ解決済み identity を返す場合、その lowering が作る builder 用 Expr の構造は `W(N(cst))` と一致する。ただし fresh local binder の alpha 改名と、推論用 annotation を除く。

**証明。** CST の node 数と各 sequence の未走査要素数の辞書式順序に帰納する。node dispatcher の成功枝は §3 の表の node と一対一に対応する。各枝の `yumark_static_operation` は与えられた field ベクトルの順に `make_app` するため、表の curried App と一致する。sequence は上記五分岐を同順に実行する。flush で作る text の値も一致する。`yumark_chain` は逆順 loop で NIL へ CONS を積むため、生成木は右結合の Seq 展開になる。最後に二つの `lower_yumark_builder_lambda` と二つの App が W を作る。各 recursive call は child、各 loop は有限列である。□

この定理の結論は生成 Expr の一致である。CST の全入力が成功すること、標準名の解決、生成された制約の健全性、normalizer が意図する空行意味論を保つことは結論に含めない。特に parser が生成した全 blank node を必ず normalizer が発見する、という別命題を `unreachable!` の綴りから推論しない。

## 5. 評価位置と効果を保持する接続

**補題 Y5（生成時の非実行）。** `W(d)` の値構築は、algebra field の body を実行しない。W の二引数を実際に受領した後に限り、E(d) とその document application に制御が進む。

**証明。** W の最外形は Lambda である。値構築規則には body の evaluation premise がない。第一 App はその body の第二 Lambda を返す。第二 App の Value entry が algebra を受領して body に入るとき、初めて E(d) が active child になる。これは完全 Call の順序から従い、algebra の pure 性を必要としない。□

**補題 Y6（生成 code に関する有限 effect 義務）。** 各 algebra field の whole contract と各実際の選択証拠を固定すると、W(d) の immediate/latent/reentry の義務 graph は、既存の有限 source 規則を適用して構成できる。任意の effect を空と仮定する生成規則は不要である。

**証明。** Y2 の導出構成を、各 node の whole packet を保持して反復する。TEXT/FENCE は field の complete Call を置く。単一 child の container は child builder の二段 App、その結果を field へ渡す App を置く。CONS は `a.cons` の取得、`h f a` を引数とする第一 App、その結果の callable に `t f a` を渡す第二 App を置く。この間、第一 App 自体の効果は後半より前に生じうるため、`h,t` を先に eager 評価する三項式へ置換しない。field body の効果はこの App の ordinary port に残る。

W の外側は Lambda 導入なので immediate event seed を持たず、body の全 graph は call/latent port に保持される。field の returned value が callable であれば、その全 latent/reentry graph も source App 規則が繋ぐ。W の二つの GeneratedNeutral binder はユーザー omission 由来の seed を加えないが、既存 metadata の transport を消さない。標準 builder 自身の source formal には元の annotation/provenance に従う receipt 規則を適用する。有限の構文 node に規則を適用するだけなので、有限 graph を構成する。□

Y6 は graph の全 inclusion が与えられた上限を満たすという命題ではない。任意の algebra を pure として受理する結論もない。実際の有限証明書がその graph を閉じる場合に限り、修正機械の効果安全性定理を適用できる。ここで型付けの検査義務と、その検査を常に通過するという完全性命題を分ける。

## 6. 親定理への適用

ソース稿 §14 の Yumark 外殻の前提にある未構成の document builder `D` を、静的木については `E(N(cst))` に置換できる。Y1–Y4 が実行型導出と凍結 Expr 出力の対応を、Y5 が遅延位置を、Y6 が有限 effect 義務の構成を与える。したがってこの静的部分に「内部 builder を外から与える」という残項は不要となる。

残る箇所は commands / inline expressions / interpolation の展開、normalizer の全 parser 出力に対する意味保存、module/import による標準 identity の構成、生成 error/act-copy/derive、修正機械自体の全 simulation、既存候補政策の採用である。これらは本稿の仮定へ隠して全言語が完了したとは記録しない。Simple-sub の元の A/B、主型性・停止性・推論の自然さの義務も変更しない。

検証方法は紙上導出と固定ソースの読み取りであり、コンパイラー、テスト、実行結果は使用していない。独立査読の結果は sprint outcome に記録する。
