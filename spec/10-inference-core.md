# 章10 型推論の核

状態: **構成案・形式化対象を明記**（2026-11-04）。この章は現行の章2〜7を計算体系へ移すための仕様である。新しい注釈構文を追加せず、旧実装の挙動を言語仕様に昇格させない。Lean の対応物は [`../lean/`](../lean/) に置く。

## 10.1 権威と対象

今回の構成では、次の順で根拠を扱う。

1. `yulang3` の確定済みの利用者向け仕様。特に[型](04-types.md)、[effect](05-effects.md)、[表示](07-display.md)、[罠台帳](traps.md)。
2. 2026-11-04 の依頼: `yulang2-oracle` の衛生性を尊重しつつ、破綻した実装をそのまま採用せず、`'e?` と `[io, 'e]` 等は `yulang3` に合わせて再構成する。
3. `yulang2-oracle` の設計意図。参照する commit は `a58eefc31e22141574b6f20c6a5748151c6d79f1`。

旧版の主な参照箇所は `web/docs/ja/reference/type-theory.md`、`spec/2026-05-31-effect-variable-subtractable.md`、`docs/effect-inference-brief.md`、`notes/design/handler-row-subtraction.md`。これらは相互に改訂時期が異なる。古い shift/peel 案、後の directed stack weight、旧 hover 表示を一つの証明済み体系として混ぜない。

核の入力は、名前を解決し、糖衣を除いた式と、その時点で可視な宣言・型注釈である。出力は**値の型、effect 行、残余制約**である。残余制約を黙って捨てて公開型を作ってはならない。

出典: `AGENTS.md`、章4.7–4.8、章5.4–5.5、章7.1–7.4。

## 10.2 型の関係と関数の引数

型の制約は原則として `A ≤ B` であり、すべてを等式単一化に置き換えない。`never ≤ A`、record の幅部分型付け、分岐の union が必要になる。関数の入力は反変、出力は共変で扱う。nominal な型の同一性を構造的な record の同一性と混ぜない。

関数の入力にも computation の行がある。内部記法を

```text
Comp(A, ρ)
Fun(Comp(A, ρin), Comp(B, ρout))
```

と書く。これは利用者向け構文ではない。`'a [flip, 'e] -> ['e] list 'a` の入力側の行を表すために必要になる。

`catch action` に渡される `action` は、callee の handler が処理できる computation である。引数を必ず先に実行し尽くす通常の CBV application だけでは、章5.2 の `all_paths` を表せない。核では computation を引数として渡す規則を明示し、source から suspension/force 等へ移す際は別途その接続を証明する。

分岐は両腕の型を union として保持し、その場で cast を挿入しない。期待型が到来する境界で初めて cast の義務を生成する。`if c: 1 else: "text"` を `int = str` の失敗にしてはならない。

出典: 章3.3、章4.1・4.3・4.8、章5.2、章6.5。

## 10.3 衛生的な effect 行

### 10.3.1 family と出現を分ける

effect の出現は、**family とその型引数を含む key**、およびどの呼出境界から保護されているかを持つ。表示上の family 名だけを比較して capture を決めない。内部の境界識別子は公開型の一部ではない。

同じ `io` に対して、局所で明示された出現と、callback 由来の保護された出現は同時に存在できる。行を family 名の集合に潰してから handler で減算すると、後者を誤って消してしまう。

`ref_update int` と `ref_update str` も別の key である。未解決の型引数を照合するときは、その不変性に対応する型制約を残す。型引数を捨てて同じ family として処理しない。

ここで key に含める型引数は **act/family 自身の引数**である。operation-local な多相変数まで dispatch identity に混ぜない。後者は、呼出側の具体化と handler 側の抽象型を対応させる署名の検査に属する。

実行時の dispatch には operation 自体の識別子も必要である。`OperationKey` は family・operation・型引数を保持する。同じ family に二つの operation があって、一方だけを処理しても、もう一方は残る。family 行の entry を丸ごと消すには、operation の被覆が十分であることを示すか、未処理の operation に対応する family を残す。source の不完全な handler をどう診断するかは、この内部表現だけでは決めない。

### 10.3.2 保護・許可・解除

境界 `b` と、そこで引いてよい key の集合 `P` に対して、`protect(b, P, ρ)` は `P` にない出現へ保護を付ける。許可は effect の存在を要求しない。

解除は対応する境界の保護を一回分だけ相殺し、別の境界の保護は残す。再帰等で同じ静的境界を反復しても、重なった保護を Boolean 一個へ潰してはならない。非負の保護listだけを扱う参照核 `Effects` では `release(b, ρ)` が一個の層を消す。この参照核を高階へそのまま拡張すると往復が壊れるため、10.3.4では符号付き差分に精密化する。

handler が引いてよいのは、対象 key が一致し、かつ現在の保護がない出現だけである。外側の保護は、内側で `[_]` と書いたからといって消えない。

| 表記 | 核で保つ区別 |
| --- | --- |
| `[io, 'e]` | 明示的な `io` と、保護された tail の出現 `'e` の和。tail 自身に同じ `io` が含まれてもよい |
| `'e[io]` | tail のこの出現で `io` だけを引いてよい。明示的な `io` の発生を要求しない |
| `'e` | 保護された行の出現 |
| `'e?` | 対応する位置で保護を解除した出現。別の位置の `'e` は変更しない |
| `[_]` | その入力境界で全 family を許可する注釈。外側の保護の一括解除ではない |

`'e?` と variant の残余行変数は推論結果にだけ現れる。注釈として新設しない。`'e?` と `[_]` を同じフラグへ置き換えない。

この表は章5.4–5.5と章7.3を同時に満たす内部表現としての再構成である。章7.3の最終的な表示形式、複数の解除をどう印字するかまで確定するものではない。

Lean の裸の `.var e` は環境の行を参照するだけである。保護された出現 `'e` の内部形には境界と許可maskを明示し、その対応位置での解除にも同じ境界を使う。非負参照核の例は `.protect b allowNone (.var e)` と `.release b (.protect b allowNone (.var e))` である。符号付き核では解除にも対応するmaskを保存する。前処理で保護のwrapperを落とすと、衛生性の定理は適用できない。

再帰が一周するごとに同じ境界の保護が積み増される型は、**拒否も上限もせず、そのまま許す**（確定, 2026-11-05）。行の解は、有限個の制約の**最小解**として意味を持ち、その解に含まれる出現（key と境界ごとの重み）は有限個とは限らない。例えば `{ raw k } ≤ r` と `protect(b, ∅, r) ≤ r` は、重み `0, 1, 2, …` のすべてを `r` に強制する。保護と解除が釣り合うサイクルは有限になるが、そうでないサイクルも型として正しい。したがって、有限の記号で書けることは、型の意味の前提にしない。
この判断で、次を示す義務が生じる。(1) 最小解への所属が、有限の制約について決定できること。(2) 最小解を有限の記号で表せること（重みが等差的に増える集合を含む）。(3) 非 capture と相殺の定理が、無限の解でも成り立つこと。型の表示（無限の重みをどう見せるか）は、章7で後から決める。

### 10.3.3 置換と shallow handler

行変数は任意の実際の行へ置換できる。保護・解除・handler の作用は、その**出現位置**で、置換後の行へ作用する。未知の tail は処理対象 family を含まない、と仮定してはならない。

shallow handler の継続は同じ handler に自動で包み直さない。再開した継続には元の computation の effect があり得る。operation arm 自身が起こす effect も、handled computation から引いたという理由では消せない。handler の結果行は、残余と arm 側の effect を含む。

出典: 章5.1–5.5、章7.3、旧版 `spec/2026-05-31-effect-variable-subtractable.md`、`docs/effect-inference-brief.md`。

### 10.3.4 値の中のcallbackと高階の向き

computation の request を写すだけでは、`pure callback` の値の内部には届かない。有限の型shapeに沿ってproduct・sum・list・arrowの中をたどる必要がある。arrowの入力では向きが反転し、戻り値と戻りcomputationでは元の向きになる。

保護をlistから一個消すだけの解除では、高階の往復を一般には復元できない。可視なrequestを先に解除しても変化せず、後の保護だけが残る。`HigherOrder.Examples.fresh_roundtrip_is_not_symmetric` がこの反例である。この単純なwrapperを任意の高階引数に対する意味保存の翻訳とは扱わない。

この欠落を埋める精密化が `Directed` と `DirectedHigherOrder` である。出現はkeyのほかに境界ごとの整数weightを持つ。許可mask `P` がそのkeyを許可していなければ、`protect(b, P)` は `b` のweightを `+1`、対応する `release(b, P)` は `−1` だけ変更する。許可されていれば両方とも恒等である。handlerがcaptureできるのは、keyが一致し、**すべての境界のweightが0**のときだけである。負のweightもcaptureを阻止する。

同じmaskを使う一対について、任意の出現・行・有限shapeの値で、次の両方を証明する。

```text
release(b, P, protect(b, P, v)) = v
protect(b, P, release(b, P, v)) = v
```

`DirectedHigherOrder.transport_opposite` は関数を含む任意の値を量化し、新鮮性、weightの上限、fuelを仮定しない。境界名の集合は任意の有限 `Fin n`、各weightは上限のない整数である。非負の保護listは各境界の出現回数へ写せる。`legacy_capture_agrees` はその埋込みでcaptureが一致することを示し、保護層が存在する場合には一個のerase解除とも一致する。層がない場合の解除では負の差分が残り、ここが単純なlistモデルとの違いになる。

相殺の定理と非captureの定理の前提は異なる。符号付き入力のweightがもともと `−1` なら `+1` で可視になるため、任意の行に対する無条件の非captureは成立しない。`default_zero_boundary_noncapture` と高階の `guard_arrow_noncapture` は、変換対象のrequestがその境界でweight 0から来たという `ZeroAt` を明示する。高階の定理では、反変方向に引数を変換した後の `function(releaseValue(argument))` にこの前提を課す。

`contravariant_debt_preserves_local_callback` は由来の混在する具体例である。callbackを受け取る関数の内部に同じkeyを捕まえて `99` を返すhandlerを置くと、無変換ではcallbackが奪われる。高階の保護では、引数側の `−1` がこのcaptureを阻止し、戻り側の `+1` が相殺することで、元の呼出側のhandlerがpayload `7` を受け取る。外側でも永久に隠すだけの例ではない。

これは旧実装のdirected stack全体の正しさを主張するものではない。今回の核では有限の解決済みshapeを扱い、atomとoperation payloadの内部は不透明のままである。sourceからshapeを作り、変換を挿入し、`ZeroAt` に相当する由来の条件を保存するelaborationは別の証明義務とする。

新しい境界を明示的に割り当てる場合には、その原点条件を構成できる。`FreshBoundaries` は、既存の座標を単射で大きいinterfaceへ写し、追加した座標だけを0にする。既存の正負すべての重みを保持し、capture、残余、既存境界での保護・解除、shallow handlerの実行と可換である。`liftTree_zeroAt` は任意の元のrequest treeについて新しい座標の `ZeroAt` を導き、`fresh_noncapture` はその座標で既定の保護を付けた計算が内側のhandlerに捕まらないことを証明する。元のtreeの既存座標には負の重みがあってもよい。これは原点条件を仮定から構成へ進める定理であり、sourceの全呼出しへの割当ての挿入や、値の内部のcallbackの変換までを証明したものではない。

`FreshRowInference.eval_mapScopes` は既存の `RowExpr` の全構文について、この座標写像と行評価の可換性を証明する。未知のtailに入る行は任意の符号付き行でよい。`fresh_eval_zero` は新座標の原点条件を推論行の評価から導く。注釈のsnapshotと保存履歴の検査も単射による境界名の変更で不変であり、`emit_reindex` は推論formulaに付けるgateまで保存する。過去の拒否はfresh化で修復されず、後の行変数の具体化では履歴を再検査しない。

## 10.4 variant の残り

章4.5の決定（2026-11-05）に従い、variant の行は tag ごとに一つの alternative を持ち、同一 tag の payload は union に合流する。`:id int` と `:id str` の合流は `:id (int | str)` である。処理する tag の集合 `H` と、tag が一意な有限行 `R` に対して、残余は

```text
residual(H, R) = { (tag, payload) ∈ R | tag ∉ H }
```

である。tag の腕は合流済み payload 全体を受け取り、その tag の entry 全体を除く。payload の一部を処理して残りを同じ tag の残余に残すことはしない。値の alternative には effect の stack weight を付けない。

[`Yulang/Variants.lean`](../lean/Yulang/Variants.lean) の既存定理は、tag の重複を許す有限 support について、正確な分割、処理済み tag の不在、残余の最小性・最大性、除去の冪等性・交換、payload 置換との両立を述べる。これらの定義と定理は維持する。

[`Yulang/VariantsMerged.lean`](../lean/Yulang/VariantsMerged.lean) の `Variants.Merged.Row` は tag の列が `Nodup` であることを保持する。`normalize merge` は重複を許す行からこの表現へ移す。`merge` は payload の二項演算として明示的に渡し、同一 tag の payload を入力順の右結合でまとめる。該当 payload が `[a, b, c]` なら `mergeAll` は `some (merge a (merge b c))`、一つならその payload、存在しなければ `none` を返す。空の場合のために特別な payload や merge の単位元は要求しない。tag の列順は最後の出現順の逆順である。

ここで証明する主張は次のとおりである。以下の定理名は `Yulang.Variants.Merged` 内にある。

- `normalize_unique` は合流後の tag の一意性を、`tags_normalize` は元の行との tag の一致を述べる。`lookup_normalize` は lookup と上の `mergeAll` の一致を述べ、`mergeAll_eq_none_iff` は `none` と元の行に tag がないことを同値にする。
- `normalize_residual` は `normalize merge (residual H R) = residual H (normalize merge R)` を行の等式として証明する。除去と合流の前後で tag の列順も一致する。
- `selected_normalize` は処理対象 tag の選択結果が合流済み payload 全体であることを述べる。`mem_residual_normalize_iff` は残余の `(tag, payload)` が「tag が未処理、かつ `mergeAll` がその payload」と同値であることを述べる。`handled_no_residual_payload` は、処理済み tag がどの payload を伴っても残余に現れないことを述べる。
- `residual_empty_iff` は、tag が一意な有限行について「残余が空」と「存在する全 tag が処理対象」の同値を述べる。`case_exact_tags_empty` は腕の tag が入力の tag とちょうど一致すれば残余が空であることを述べる。`case_omitted_tag` と合流後への特殊化 `case_omitted_normalize` は、存在する tag を一つでも落とせば残余が非空となり、その tag と payload 全体を含むことを述べる。
- `normalize_map` は、payload 置換 `f` が `f (merge a b) = merge' (f a) (f b)` を満たすとき、置換と合流が交換することを述べる。`residual_map` は合流済み行での置換と残余の交換を述べ、こちらには merge 準同型の仮定は不要である。

これらの合流・残余の定理に、merge の結合則・交換則・冪等則は必要ない。入力の並べ替えや重複挿入で payload が等しくなることまでは主張しない。`variant_union_upper_bound` は既存の `StructuralBase.Subtype` の variant 共変規則と union 規則だけから `variant l a ∪ variant l b ≤ variant l (a ∪ b)` を導く。逆向きの包含や、構造部分型モデル全体の正規化を示すものではない。

`Examples.id_merge` と `id_handled_entirely` は、`[("id", int), ("id", str)]` が一つの `id (int ∪ str)` へ合流し、`id` の処理で残余が空になることを確認する。`str_leaves_num` は任意の payload `s, n` について、`[("str", s), ("num", n)]` から `str` を除けば `[("num", n)]` が残ることを示す。

したがって、この有限行の核では「残余が空」と「全 tag の被覆」は同じ条件である。入力型が腕に書いた tag だけで閉じていれば `_` は不要という章3b.4の条件に対応する。payload 内部の source pattern 網羅性は章4.5の決定により対象外であり、guard 付きの腕は章3b.4に従って被覆に数えない。定理は解決済み tag の処理集合を受け取り、source からその集合を作る検査器は証明していない。payload の部分型 solver、再帰的な open row の solver、case の入力型を閉じる制約生成も、この形式化からは出ない。

出典: 章4.5（確定, 2026-11-05）、章3b.4、`traps.md` T-variant。

## 10.5 一般化・解決・表示の境界

### 10.5.1 実行可能な制約生成

`Yulang.Inference.generate` は、型の包含・行の包含・連言・選言・freshなcomputation slotの存在量化からなる有限の式を構文再帰で作る。各slotは値の型と行の組であり、新しいslotを `none`、既存のslotを `some x` で表すので、名前の衝突は起きない。結果のslotを開けたschemeを返す入口が `principal` である。

`generate_models_iff_typing` と `principal_exact` は、独立に定義した宣言的判断と解集合が一致することを証明する。

```text
principal(Γ, e) の解 (A, ε)  ↔  Γ ⊢ e : A ! ε
```

これは任意の型・行モデルと、それに対応する入力環境についての主張である。生成器はsolverを呼ばず、solverの健全性や成功を前提にしない。`principal_most_general` は、どの健全な候補schemeの解も、この生成schemeの解に含まれると述べる。解いた後の単一の型表示が最も一般的だ、という定理ではない。

非再帰letの一般化経路では、右辺が構文的な値であり、純粋に型付けできることを要求する。その右辺のschemeを保存し、参照ごとに内部の存在slotを独立に具体化する。外の環境のslotはそのまま残す。

単相経路はすべての右辺に使える。一つの右辺型を選び、その純粋な値を本体で共有し、右辺の実行行と本体の行を合流する。構文的な値には「純粋な一般化経路、または単相経路」の選言を生成し、値でない式には単相経路だけを生成する。どちらの経路でも、右辺が未使用だからといってその型付けを省略しない。

この区別はcomputation引数で必要になる。変数 `action` が `int ! [io]` を表す場合、変数という構文だけを見て空行で一般化しようとすると、その `let` 自体を誤って拒否してしまう。`Polymorphism` はこの変数を束縛してunitを返す式が `unit ! [io]` を持ち、空行では任意の結果型について型付けできないことを、生成制約まで証明する。effect付きの変数を純粋な多相値へ変えてしまう修正ではない。

対象は、名前解決後の変数・基本literal・lambda・computation application・非再帰let・分岐・pair/projection・record/field・variant注入である。`Structural` の具体的モデルで、unionを必要とする分岐、二種類の型で使う多相identity、record幅部分型からのprojectionを生成制約まで検証する。

内部の判断を `Γ ⊢ e : A ! ρ` と書く。各行の結果には、必要に応じて値の型と行それぞれの包含制約を加える。以下の表はsource構文の追加ではなく、`Typing` と `generate` の共通の契約である。

| 核の式 | 前提と生成する関係 |
| --- | --- |
| 変数 | 環境のschemeをfreshな内部slotで具体化する。捕捉した外側のslotは共有する。未束縛なら偽の制約になる |
| literal | 対応する基本型と空行を結果の上界へ包含させる |
| lambda | 引数にfreshな `A ! ρa` を置いて本体を `B ! ρb` と型付けする。関数値は `(A ! ρa → B ! ρb) ! ∅` |
| application | 関数を `(A ! ρa → B ! ρb) ! ρf`、引数を `A ! ρa` と型付けする。結果は `B ! (ρf ∪ ρb)` |
| 分岐 | 条件を `bool ! ρg`、両腕を `A ! ρa` と `B ! ρb` にする。結果は `(A ∪ B) ! (ρg ∪ ρa ∪ ρb)` |
| pair | 両成分の値型をpairにし、実行行を合流する。projectionはpair型との包含制約を通じて該当成分を取り出す |
| record | field値とrestを型付けし、restに `restType ≤ emptyRecord` を要求する。結果には元のrest型を保持し、両方の実行行を合流する |
| field | receiverを対象fieldを持つ単一fieldのrecord型へ包含させ、その値型を返す。余分なfieldは幅部分型で許す |
| variant注入 | payloadの値型を指定tagで包み、payloadの実行行を保つ |

recordのfield照合は同じlabelの最初の出現を採用する。後に現れた同名fieldへ都合よく読み替える幅規則にはしない。具体的な部分型モデルは有限recordのspineについてこの条件を実装するが、unionを含むすべてのrecord型の正規化や完全なMLsub solverを定義したものではない。

### 10.5.2 operationとshallow handlerの制約

`RowInference` は前節の生成器を実際に呼び、解決済みのoperation呼出し・境界変換・shallow handlerについて、独立な型判断と制約生成の双方向の一致を証明する。行の空・和・明示的head・保護・解除・残余・包含を `RowAlgebra` で与えることで、同じ生成器と定理を非負の保護listと符号付き行の両方に使う。`EffectInference` は非負参照核の規則と署名・arm環境の定義を保持する。以下の式は最小限の結果上界を示しており、核の部分型規則でさらに上界へ広げられる。

operationの署名を `k : P → Q`、宣言された追加行を `δ`、payloadの推論結果を `P ! ρp` とすると、結果は

```text
Q ! (ρp ∪ {k} ∪ δ)
```

となる。追加行があってもoperation自身のeffectを消さない。`k` はfamily・operation・family型引数を含む解決済みkeyである。単相署名を保ったまま、有限個のoperation-local型変数を持つ `PolySignature α n` も扱う。署名の入出力ではambient slot `α` と局所型変数 `Fin n` を区別する。呼出側の `polyRequestConstraints` は局所型の割当てを存在量化し、`poly_request_constraints_exact` は「ある割当てで独立なrequest規則が成立する」との同値を証明する。この存在量化は、呼ぶ側が任意の型を選べるという章5.1の規則を表す。呼出しごとに量化し、別の呼出しと局所型を共有しない。

actionの型を `A ! ρ` とするhandlerでは、value armに純粋な `A` を渡す。operation armには純粋なpayload `P` と、純粋な関数値としての継続

```text
Q ! ∅ → A ! ρ
```

を渡す。継続の出力行は元の `ρ` であり、`residual({k}, ρ)` ではない。value armとoperation armがそれぞれ `B ! ρr`、`C ! ρo` ならhandlerの結果は

```text
(B ∪ C) ! (residual({k}, ρ) ∪ ρr ∪ ρo)
```

である。`ρo` の中に同じoperationが現れても再び差し引かない。別operationの残存、handler armの再送出、元の行を持つ継続が個別の定理になっている。

operation-local型変数を持つhandlerでは、その型をrigidに扱う。`poly_handler_constraints_exact` が対応する独立な `PolyHandlerTyping` の量化順序は

```text
∃ input returned, actionとvalue armの型付け ∧
  ∀ ι : Fin n → m.Ty, ∃ operated,
    operation armの型付け ∧ 結果の型と行への包含
```

である。actionとvalue armの型・行は局所型を選ぶ前に固定する。operation armは、すべての局所型割当てで同じ式を型付けできなければならず、一つの具体型に単一化して検査を済ませることはできない。局所型の値を同じ型を受け取る継続へ渡す使い方は許す。

handlerの結果 `out : CompTerm α` と外側のscheme環境 `SchemeEnv α` は局所slotを含まない。`EffectInference.local_result_no_escape` はどの局所割当てでも結果の型・行が元の `out` の評価と一致することを、`local_outer_environment` はどの局所割当てでも同じ外側binding環境を表すことを証明する。したがって局所変数のescapeは核の規則の構造で排除され、存在型へ包んで外へ出す規則はない（章5.1、確定2026-11-05）。source上でescapeを検出しエラーを報告するelaboratorまで証明したものではない。局所slotの行成分は空行であり、局所行変数は導入しない。atomのkeyと追加effectは局所割当てによらず固定する。atomのpayload内部に現れる局所変数はこの形式化の対象外である。局所変数のrole制約は、10.8の `RoleEvidence` 層で同じ署名へ接続する。

`SignedStructural.generated_poly_request_at_any_type` は任意の構造型での呼出しを受理し、`generated_poly_requests_independent` は同じ署名・同じ外側の割当てでintとstrへの二回の独立した具体化を受理する。`generated_poly_handler_resumes_payload` は任意の局所型で `k payload` を受理する。一方 `generated_poly_handler_payload_escape_rejected` はpayloadを固定のint結果へ直接返す腕を拒否する。負例は局所型をstrとしたときの `str ≰ int` によるもので、任意のモデルや任意の固定結果上界について拒否を示した定理ではない。

`SignedStructural` は共通の構造部分型を実際の `Directed.Row` へ具体化し、`RowView` を恒等写像で実装する。このモデルでは、operationの生成制約が自身の行を含む結果を受理し、空行を拒否する。また、保護前の解除が作る負の差分を持つ行は受理され、その差分を空行へ消すことは拒否される。これらは任意のscope数と解決済みkeyについての定理である。

`DirectedBounds` 内の `Directed.Computation.shallowHandle_bounded` は、符号付きcomputationのactionと両armに実行時の上界があることを前提として、上の残余と和がhandler全体の上界になると証明する。継続の前提にも元の行を使う。境界での保護・解除によるcomputationと行のtransportは双方向に上界を保ち、この主張自体には `ZeroAt` を必要としない。上界のtransportと非captureを混同しない。

`RowInference.generated_signed_handler_composes_effect_bounds` は、成立したhandler生成制約を独立の型判断へ戻し、action・armの明示された実行時上界と組み合わせて、実際の符号付きshallow handlerの出力上界を導く。この合成定理は `DirectedHandlerInference` に置く。型付けからaction・armの上界を導くpreservationを、前提の中へ隠して証明済みと数えない。

この層では、payload・action・armを前節のcore `Expr` で表し、一つの解決済み規則ごとに生成する。effect構文を再帰的に含む一つのsource ASTからの翻訳まで証明したものではない。また、境界規則がここで変換するのはその場のcomputation行である。値の中にある関数の潜在行と10.3.4の高階transportを結び付けるには、型に沿ったelaborationの証明が別に必要になる。

### 10.5.3 sourceへ接続するときの義務

- **一般化**: 構文的な値だけを一般化する。環境由来の未確定変数を量化してはならない。計算された binding は単相で共有する。再帰 SCC は同時に扱い、computed-value cycle を通さない。
- **operation の多相性**: 呼出側は operation-local 型変数を具体化する。handler 側は抽象型として受け取り、任意の具体型へ単一化しない。role 制約があれば、その証拠だけを利用できる。
- **method / role**: receiver の下界が定まるまで解決を保留する。同じSCC内で型が分かれば既知型の優先順位を使い、SCC確定時にも未知なら可視roleの同名methodを0/1/複数で分ける。解決済みSCCの解釈は後の具体化で選び直さない。field/with、role、effect 行の優先順位を守り、同じ階層の複数候補は曖昧とする。
- **cast**: 期待型境界で挿入する。直接の重複規則と、複数の間接経路を区別する。後者は選択が仕様上自由なので、型の主性と elaboration の一意性を同じ定理にしない。
- **公開表示**: 残余の行変数や実際の制約を消さない。内部の識別子を隠す処理には、型の意味を保つことの根拠が必要になる。

出典: 章2.1、章4.7、章5.1、章6.2・6.4–6.5、章7。

## 10.6 証明の区別

次の主張は別々に検証する。

1. **生成の停止**: 任意の有限な核の式に対して、制約生成が停止する。
2. **生成の健全性・完全性**: 独立に定義した宣言的型判断と、生成制約の解が両方向に対応する。
3. **制約 scheme の主性**: 一つの生成結果が、その式の許される型付けをすべて、かつ余分なく表す。
4. **solver の正しさ**: 実際に解を求め、失敗が解の不在を意味し、成功結果が明示した主性・最小性を満たし、停止する。全解を表す制約 scheme と、すべての解以下にある最小モデルは別の主張である。禁止制約を持つ Horn 問題では、最小モデル以上の valuation がすべて解とは限らない。
5. **実行時型安全性・衛生性**: elaboration と評価の対応、preservation/progress、呼出元の effect を内側の handler が奪わないこと。

2・3だけから4・5を主張しない。有限の包含制約の solver を証明しても、再帰的な型・保護の stack・role 解決を含む全言語 solver の証明に置き換えない。証明対象、量化子、依存公理は [`lean/README.md`](../lean/README.md) に記す。

## 10.7 確定した規則と残る接続

2026-11-05の決定により、次の二点は言語仕様として確定している。意味論の未決定と、sourceへの接続やsolverの未証明を区別する。

- associated typeは普通のfreshな型変数と等式制約で表す。impl選択で等式を追加し、先に積まれた制約を上書きしない（章6.3）。
- variantはtagごとにpayloadをunionへ合流し、tag全体を処理する。網羅性は閉じたtag集合で決まり、guard付きarmは被覆に数えない（章4.5、章3b.4）。source patternからこの核へ翻訳する証明は別に必要である。

章6.3の Paterson 型条件の下で、第一階の impl 集合に対する role 解決の停止は [`Yulang/Roles.lean`](../lean/Yulang/Roles.lean) で証明した。型構築子と型変数を各1と数え、head と各条件の型引数のサイズを合計する。各条件の合計が head より真に小さく、各変数の出現回数が head 以下なら、任意の impl 変数の置換後も条件は head より真に小さい。全 impl がこの条件を満たすことを入力に要求する `resolve` は、そのサイズを測度として深さ制限なしに停止する。候補は goal の変数を rigid に保った一方向の head 照合で決め、二つ以上なら `where` を調べる前に曖昧とする。一意な候補の子で曖昧さが見つかった場合も、別の子の候補不在より曖昧さを優先する。健全性、到達する head に重なりがない場合の完全性、到達可能な head の重なりと曖昧さの同値もこの核の範囲で証明した。

章6.3の決定（確定, 2026-11-05）により、impl の associated type の右辺は具体的な型・型構築子・head に現れる型変数だけからなり、他 role の associated type を参照できない。この第一階の関連型には追加のサイズ規則は不要である。[`Yulang/RolesAssoc.lean`](../lean/Yulang/RolesAssoc.lean) の `assocOf` は、既存の `resolve` の成功後に、選ばれた impl の右辺へ照合置換を一度適用する。省略された定義には、role の引数位置を goal の型引数で置換した default を使う。別の関連型を展開する再帰はない。表現上は、関連型名の辞書の無重複性、同じ元の impl への辞書の一貫性、default の変数範囲を要求する。`AssocWellFormed` は、明示定義の変数が head に現れること、署名との引数数の一致と必須定義の充足、role にない名前を提供しないことを要求する。

`assoc_total_closed` は、全 impl が Paterson 適格性と関連型適格性を満たすとき、解決済み goal の宣言済みの各関連型名について値が存在し、結果の変数がすべて goal に現れることを証明する。`assoc_unique` は値の一意性を、`assoc_independent_of_constraints`・`assoc_explicit_eq`・`assoc_derivations_unique` は where の解決導出や head の照合置換の選び方によらないことを示す。`assoc_explicit_size` は明示定義の具体化について、既存の `Term.subst_size` の正確なサイズ公式を再利用する。関連型の等式追加は10.8の `RoleConstraints` で接続するが、構造部分型と合わせた単一化のsolverは未証明である。generic role の method dispatch、章6.4の receiver 下界による保留、operation-local role 制約、effect との相互作用、推論の制約言語との統合、source 宣言時の検査は `RolesAssoc` 単体の定理の対象外であり、以下の各層で扱う範囲を分ける。出典: 章6.1–6.3（確定, 2026-11-04・2026-11-05）、`Yulang.Roles.size_decreases`・`resolve_sound`・`resolve_complete`・`resolve_ambiguous_iff` および上記の関連型の定理。

上の判断に依存しない核の定理は先に閉じる。未解決制約を受理済みプログラムと同一視しない。

`Annotations.no_substitution_invariant_extensional_check` は、さらに次の三つを同時に満たす単純なcheckerが存在しないことを証明する: 未知の行を常に受理すること、許可外の具体headを拒否すること、任意の行置換に対して受理が不変であること。未知行をその具体headで置換すれば矛盾する。したがってT3の注釈検査は、**注釈を検査した時点で見えている具体 effect** だけを対象にする（確定, 2026-11-05）。共変の注釈は行変数を束縛せず、検査するだけで、反変の許可と同じ変数に集まって干渉することはない。その時点で見えていない行変数が後で具体化されるのは、一般化された型の具体化（代入）であって、注釈の再検査ではない。注釈の時点で既に分かっていて、保護されず可視な許可外のeffect（例えば `[io]` の注釈に対して引数の型が `undet` を出すと分かっている場合）は、その時点でエラーになる。局所snapshotの検査はこの方針に対応し、実装・証明した。

## 10.8 確定事項を接続した拡張核

この節は、章2・4・5・6と2026-11-05の決定を形式化する層の対応を記す。新しい言語仕様を追加する節ではない。詳細な量化子と対象外の範囲は [`lean/README.md`](../lean/README.md) を参照する。

### 10.8.1 qualifiedな推論と公開境界

`QualifiedInference` はrole要求を有限の制約として生成する。resolved methodの要求を生成した時点で具体的なimplを探す必要はない。`principal_exact` は、指定されたrole証拠の解釈の下で、生成制約の解と独立な型判断を双方向に対応させる。

`QualifiedGeneralization` では、環境slot `α` と一般化する有限slot `Fin n` を分ける。raw role制約のうちlocal slotを含むものはschemeへ、環境slotだけのものは残留制約へ移す。この分配はすべての割当てについて制約を保ち、混合した制約の環境slotも共有する。右辺は抽象辞書を仮定して全local割当てで検査し、schemeの利用時に具体化と証拠を要求する。通常のletは値型と行を含む `Comp` slotを一般化する。

`ModuleRoles` のEOF検査には、推論が求めた部分割当てと、公開型および残留制約を含むinterfaceを渡す。公開に関わる未確定ambient slotは拒否し、残留role制約は実際のresolverで検査する。受理した公開schemeの意味は、その後の無関係なslotの補完に依存しない。この定理は部分割当てを探索するsolverやmodule全体の制約収集passを含まない。

`RoleConstraints` は関連型選択の結果を普通の等式として蓄積する。すべての置換に対して、追加の順序・重複は解集合を変えない。与えられた置換での検査と、解となる置換の存在を決めるsolverは区別する。`CheckedRoles` は有限回の出現回数・サイズ検査からPaterson適格性を構成し、不適格な宣言をresolverの呼出し前に拒否する。

### 10.8.2 再帰と評価依存

`RecursiveInference` は有限のresolved blockについて、全本体を同じ再帰仮定環境で検査する。単相memberのslotはブロック全体の外で一度だけ選ぶ。全注釈memberの呼出しは値型変数だけを存在的に具体化し、定義の検査はそれらすべての具体化について行う。明示的なeffect行slotは共有する。通常のletの行の一般化と、この注釈による多相再帰の量化を混同しない。

SCC後の一般化はブロック全体の検査を含み、量化するslotに属するunannotated memberには構文上の値かつpureであることを要求する。computed memberのslotは共有環境へ残る。local/captured slotの分類はこの核への明示的な入力であり、未解決の部分型グラフから分類を発見する算法は別である。

`RecursiveExamples` は、再帰時に引数をpairへ包むdepth型の本体について、全注釈による受理と、有限の構造型すべてについての単相拒否を示す。後者はunion・intersection・bottomを含む同じ構造部分型モデルでの結果であり、再帰型を導入したモデルへは外挿しない。

`EvaluationOrder` は有限グラフの到達可能性を使って保守的な評価依存を判定する。computedな参照先には評価位置の真の先行を要求するため、自己依存と未来への依存は拒否される。`Initialization` は同じresolvedな本体をSCCの式へ翻訳し、値制限の一致を証明してから両判定を接続する。型の解の有無だけではcomputed cycleを通さない。依存判断と任意のsourceの高階closureフローとの対応、実行時のpreservation/progressは別の義務である。

### 10.8.3 roleを持つoperationと観測履歴

`RoleEvidence` は既存の `PolySignature` にrole制約を追加する。呼出側では局所型の存在具体化と証拠の充足を要求する。handler側では、action・value arm・外側の結果を固定した後に、署名の辞書を加えてすべての局所型でoperation armを検査する。継続の行は元のinput rowを保ち、armが新しく起こすeffectを残余操作で消さない。

`AnnotationSnapshots` は注釈時点の符号付きの具体行を保存する。後のscheme具体化はその履歴を変更しない。許容された履歴は後の行変数へ上界や等式を追加せず、失敗した履歴は後の置換で修復されない。観測前には、その時点で既知の置換を適用しておく必要があり、その知識を求めるsolverの正しさはこの定理の前提となる接続義務である。

### 10.8.4 castと構築位置

`Casts` の境界変換は普通の適合性と別の判断である。普通に適合すれば変換せず、不一致なら関数の入力を反変、出力とデータの中身を共変に調べる。固定されたnominal引数の変換には、外側の型全体の明示規則が必要になる。普通の部分型判定はこの層への独立した入力であり、この追加変換の決定可能性だけから部分型全体の決定可能性は導かない。

`CastGraph` は有限のground登録集合について、直接規則の重複と複数の間接経路を区別する。`Methods.checkCall_exact` は相異なるmethod所有型がちょうど一つであることと、全receiver memberからその型への境界変換を要求し、memberの順列で結果は変わらない。

`LiteralCasts` はlist literalの元の構築位置と要素型を保留する。期待要素型が決まれば各構築位置で境界を検査し、EOFまで期待型がなければ元の要素型のunionを記録して変換を挿入しない。構築済みのnominalなlistの要素を変換する規則とは別である。cast本体の実行・effectと弱い型変数の解探索は、この計画の正確性の対象外となる。

## 10.9 追加確定事項の形式化

2026-11-05の追補（章2.1、5.5b、6.2、6.4–6.5）により、前節で分離していた義務のうち次を接続する。source全体の翻訳や全体solverの完了とは区別する。

### 10.9.1 一般化直前の観測

`AnnotationFinalization` は一つのbinding/SCCの有限Horn制約を全部集め、実際の最小解を求めてから符号付き行を観測する。`known_iff_forced` は、成功した最小解の真のfactが、全モデルで強制されるfactと一致することを示す。制約のmembershipが同じなら解は同じで、制約の生成順序・重複・memberの収集順序に受理は依存しない。memberを並べ替えても名前解決済みのfact/row識別子は保つ。

同じSCCの別memberから伝わるeffectも検査し、後のscheme具体化は保存した観測を再検査しない。入れ子のbindingは自身の単位を確定するAPIで扱う。有限fact interfaceを構造推論から漏れなく生成することと、source traversalが各APIを呼ぶ時点の正しさはelaborationの義務として残る。

### 10.9.2 純粋なcastの実行

`PureCasts` は、実際の符号付きcomputationで表したcast本体と、その推論行による上界を受け取る。宣言の検査は行全体が空であることを要求する。可視なheadだけを消して純粋と判定することはなく、保護された要求・負の差分も拒否する。

チェック済みの基本castから、合成・積・和・関数wrapperのplanを作る。`Plan.run_eq_pure` はplan全体の純粋性を導き、`insert_requestTree` は境界挿入前後で返り値を除いた要求木が等しいことを示す。関数の入力は反変に変換し、出力は共変に変換する。`wrapper_requestTree` が比較する元の関数の呼出しは、変換後の引数に対する呼出しであり、変換前後の入力値に対する実行が等しいとは主張しない。任意の宣言済みの潜在行の上界は保たれる。

本体のoperationalな行上界をsource型付けから導くことと、`Casts.Boundary`から実行planを合成することは別に必要である。

### 10.9.3 多相castの有限探索

`ParametricCastRules` は第一階の型について、targetサイズの非増大と全変数の出現回数の非増大を有限に検査する。その条件から、任意の置換後にもtargetサイズがsource以下になることを導く。固定ground宣言がサイズを増やす場合には、宣言のtargetサイズも全体の上界へ含める。

到達先の構築子は、出発型と有限個の宣言targetに現れるものに限られる。`ParametricCastUniverse` はその有限alphabetとサイズ上界からground型を列挙し、任意の明示cast経路の到達先が列挙に含まれることを証明する。`ParametricCasts` はこの集合からグラフを構成して探索する。成功は適格な宣言・groundなsource・経路の存在と同値であり、検査済みの領域での失敗は経路の不在と同値である。等サイズの循環を禁止せず、任意の深さ打切りも用いない。

これは明示規則のendpoint連鎖の決定可能性である。直接規則の重複・重なり診断、source型の正規化、構造的な持ち上げを混ぜた全体のelaboration/solverは別の責務となる。列挙型の参照実装であり、性能上の主張ではない。

`box 'a → 'a` の具体化に合わせ、ground境界もnominal/baseなsourceから任意のtargetへの外側全体のcastを許す。pair・関数・unionを返すunboxの例を検証した。sourceがunionの場合は全memberの境界を要求し、union全体だけの規則でこの要求を迂回しない。

### 10.9.4 nominal構築位置の保留

`NominalConstructions` はlist・struct・enumの各構築位置を有限の不変パラメータslotへ対応させる。期待型が決まったslotでは、対応する元の値すべてに境界変換を要求する。EOFで未解決のslotには、そのslotに属する元の型だけのunionを記録し、変換を挿入しない。構築子・enum tag・元の位置を保持し、構築済みの値の内部へcastを通さない。

一つのslotのlist構築への特殊化は、失敗も含め既存の `LiteralCasts.finish` と厳密に一致する。出現しない未解決パラメータの空union記述は、既定型や公開可能性を決めるものではない。sourceからの全出現位置の収集と弱い変数の解探索は前段に残る。

### 10.9.5 実際の読み取りと初期化順序

`EvaluationSafety` は名前で決まらない呼出しについて、moduleの宣言・文に含まれるすべてのlambda本体の参照を候補にする。`EvaluationReads` はclosureと捕捉環境、pair/projection、分岐、storeを持つ独立なCBV意味論を定義する。読み取りprefixは、値のないstoreから読もうとする場合や、その後に発散する場合も表す。

`reads_needed` は、closureがmodule内のlambdaから作られたという由来条件の下で、実際の読み取りを静的な依存集合が覆うことを証明する。由来条件は実行で保たれ、初期化済みであることや読み取りの安全性を仮定しない。checkerの受理からcomputedな読み取り先の真の先行性を導き、先行する初期化結果を記録したprefix storeでは、その値が存在することを導く。初期化の実行結果を記録すると、このprefix不変条件が次の位置へ進む。`EvaluatedPrefix` は空storeからのcomputed宣言の実際の初期化履歴を表し、closureの由来と先行値の存在をその履歴から導く。位置を進めるときは、その位置の宣言が一意であることを要求する。

`Initialization.generate` はこの検査をSCC型推論と同じ本体へ課す。`generated_prefix_initializer_read_initialized` は、生成制約の解と実際の既評価prefixから、次の初期化の読み取り先に値が存在することを導く。現在の式の終了や読み取り先の利用可能性を前提としない。依存計算は実際の読みの保守的な上界であり、実行時に必ず読まれる集合との同値ではない。外部closure・可変store・source翻訳・全言語のprogressは対象外である。

### 10.9.6 匿名変数とrefの照合

`ImplHeads` はimpl headの各 `_` に別の変数を割り当て、名前付き変数の共有と衝突しないことを、任意の有限headについて証明する。whereの名前から匿名変数を参照できないことも示す。下ろしたheadは既存の第一階matcherへ渡す。

refには委譲規則を加えず、nominal application全体を同じmatcherで調べる。異なる外側の構築子のheadは一致せず、`ref _ int` の特化は任意のeffect引数を受理する。methodの検索段階・可視性・sourceのkind検査までこの照合補題で証明したものではない。

## 10.10 再帰する行制約の最小解

`RecursiveRows` は既存の `RowExpr` を、符号付き出現の集合としても解釈する。出現のkey、境界ごとの整数重み、保護・解除・残余の規則は変えず、行のsupportが有限であるという制限だけを外す。`finite_eval` と `finite_models_exact` は有限listによる既存の解釈とmembershipが一致することを証明する。

対象は有限個の正の下界規則 `E ≤ slot` であり、`E` には行変数、空行、具体head、和、保護、解除、handlerの残余を使える。自己参照と相互再帰を許す。`Derives` はこの規則から有限の導出で得られる出現を表し、`least_principal` は各slotの導出可能な出現全体が実際に全規則を満たし、他のすべての集合解に含まれることを証明する。`derives_iff_forced` により、導出可能であることは全解で強制されることと同値である。規則の順序と重複はこの解を変えない。

固定した集合への上界 `E ≤ U` も加えられる。そのとき解が存在することと、構成した最小解が全上界を満たすことは同値になる（`upper_constraints_exact`）。`U` は未知の行の割当てに依存しない。任意の二つの未知行式の包含や、型と行を合わせた全体solverについての定理ではない。

有限制約だからといって、解に含まれる出現まで有限とは限らない。例えば同じ境界 `b`、許可なしの保護について、二つの制約

```text
{ raw k } ≤ r
protect(b, ∅, r) ≤ r
```

は重み `0, 1, 2, …` のすべてを `r` に強制する。`Examples.every_weight_derived` と `growing_has_no_finite_model` は任意の有限list解の不在を証明する一方、`growing_has_least_model` は集合解が存在することを示す。保護と解除が対応して相殺するcycleには有限解があり、`balanced_has_finite_model` が同じ核でその例を確認する。cycle自体を一律に拒否する規則は加えない。

この結果は、有限Hornへの翻訳に有限性の根拠が必要なことを明示する。任意の残余付き相互再帰問題のmembership判定と解の有限記号表現、sourceからの制約抽出は別の義務であり、この二規則から特定のsourceプログラムの拒否を結論しない。2026-11-05の10.3.2の決定により、この無限解自体は許容する。有限表現と決定手続きについて閉じた範囲は10.13で区別する。

## 10.11 入れ子のeffect式の制約生成

`RecursiveEffects` は10.5.1の全core構文にrequest・boundary・shallow handlerを加え、すべての部分式を同じ再帰ASTで表す。operationのpayload、lambdaの本体、handlerのactionと両armにも、さらにhandlerやoperationを含められる。10.5.2の一段ごとの生成規則をこの有限ASTへ接続したもので、新しいsurface構文やhandler規則は加えない。

`generate_models_iff_typing` は任意の式、空・和・行包含を整合させる `RowView` を備えた型・行モデル、対応するscheme環境と署名環境について、生成制約の解と独立な型判断を双方向に対応させる。`principal_exact` はすべての許される結果の型・行を表し、`principal_most_general` は健全な候補schemeの解がこの生成schemeの解に含まれることを述べる。生成は式の構造に沿って停止し、solverの成功やruntime上界を前提にしない。解を見つける全体solverの主性・停止性とは別の定理である。

computation引数、値制限付きの多相let、computed letの共有、関数の入力行と出力行の区別は維持する。handlerの継続は元のaction行を保ち、armのeffectは残余を取った後に加える。境界規則は即時のcomputation行に作用し、値内部の潜在callbackを自動で変換する規則にはしない。

この統合層のoperation署名は、外側の型slotを参照できる単相署名である。fresh slotを増やすときは署名中の外側slotもrenameし、利用ごとに勝手に一般化しない。10.5.2のoperation-local多相と10.8のrole証拠は別層に残り、任意の入れ子ASTとの統合は未証明である。再帰SCC、source elaboration、型付けからの実行時安全性も、この生成器の定理だけでは従わない。

`RecursiveEffects.Conservativity.generate_preserved` は、既存の `Inference.Expr` の全constructorについて、生成formulaが旧生成結果の埋込みと等しいことを証明する。fresh slotの配置、値制限letの両分岐、principal schemeの結果binderを含めて保存する。`generated_core_exact` と `principal_core_exact` は既存の `Inference.Typing` そのものとの一致も導く。

operationのkeyは10.5.2と同じく、family・operation・family型引数を区別する解決済み識別子を想定する。genericな `Key` にfamily名だけを渡してoperationの区別を潰してよい、という意味ではない。`RecursiveEffectExamples` は入れ子handler、effectを含む多相lambda、未使用のcomputation引数とcomputed letを検査する。armの再送出、保護、負の解除差分を空行へ消せないことは、任意の結果型とslot割当てについて示す。

## 10.12 型付けから実際のeffect上界へ

### 10.12.1 形状解決済みのchecker

`OperationalTyping` はatom・pair・関数の有限shapeが決まった式を扱う。lambdaの入力型とhandlerの結果型は構文に持ち、残りのcomputation行を実際の `infer` で計算する。関数型の入力は値型と行の両方で反変、出力は共変に検査する。`infer_exact` はこのcheckerと独立な型判断との双方向の一致を証明する。未知のshapeを推論するsolverや、全言語の主型の決定手続きではない。

評価は既存の符号付きrequest treeを使い、関数へ引数をcomputationとして渡す。型の意味は「即時の要求が推論行に収まること」と「返された値が型に適合すること」の連言であり、関数では任意の適合するcomputation引数に対する結果まで要求する。`typing_sound` は部分式の型付けからこの意味を導く。handlerのaction・armの安全性を外から仮定せず、各型付けへの帰納仮定を使う。`closed_inferred_bound` は閉式のchecker受理だけから、実行中のすべての要求と継続分岐の上界を得る。

`OperationalTypingExamples` では未使用引数、明示した許可の下での引数の処理、shallow再開後に外へ残る要求、同じ継続の二回利用、armからの同一key再送出、pair内のcallback、負の差分を検証する。checker結果だけでなく、実際の評価値・request treeと、不適切な空行やraw行では上界にならないことも確認する。

この層のatomは一つの共通carrierで、operationのpayload・responseも同じcarrierを使う。任意のsource署名の安全性、一般再帰、sourceのelaboration、全言語のpreservation/progressは対象に含めない。

### 10.12.2 再帰制約生成器からの直接の接続

`OperationalCorrespondence.erase` は形状解決済みの式からlambda入力注釈・handlerの結果型・明示的なwidenを消し、10.11の再帰ASTへ写す。application・computed let・request・境界・shallow handlerの実行構造は保つ。`erasure_typing_sound` は、消去結果に対する任意の `RecursiveEffects.Typing` から同じ式の実行上界と返り値の意味を導く。型判断には既存の構造型モデルのunion・intersection・関数の分散を使える。値制限付き多相letでは、純粋な右辺が返す一つの実際の値が、各使用箇所の型を満たすことを導く。

`principal_operationally_valid` と `principal_effect_bound` は閉式について、実際の `RecursiveEffects.principal` の解だけから評価木の上界を導く。annotated checkerの受理やaction・armのruntime上界は前提にしない。operationのpayload・responseは共通のatom carrierで、構造型モデルのunitをそのmarkerにする。任意のsource literalをunit型とする仕様変更ではない。

この入口と10.12.1のcheckerは、同じ評価に対する二つの健全な入口である。注釈を消すため受理集合の一致は主張せず、checkerが注釈不一致で拒否する式の消去結果にも解があり得る。未知shapeの推論、異種operation署名、注釈と潜在値の衛生変換を保持したsource elaborationは別途必要となる。

`OperationalCorrespondenceExamples` は実際のrequestと、lambda内部のhandlerが許可したcomputation引数を処理するapplicationの制約解を構成する。requestは任意の結果値型で空行解を持たない。handlerを含むapplicationは空行の解を持ち、同じ評価が値8を返すことと接続する。これは具体的な解と拒否の検証であり、全制約solverを実装したという主張ではない。

### 10.12.3 fresh境界での衛生性

`CheckedHygiene.inferred_fresh_origin` はchecker受理から実行上界を得て、推論行が古い境界からfresh座標へ持ち上げた `RowExpr` の評価であるという静的な前提から、実際の評価木の `ZeroAt` を導く。未知tailに具体的な負の重みが含まれていても、古い座標の重みはそのまま保たれる。行の表現をchecker自身が発見するとは主張しない。

`closed_checked_boundary` は閉式のchecker受理だけを前提に、実際にfresh座標を割り当て、許可なしで保護したrequest treeについて、対応する行上界と任意の内側shallow handlerによる非captureを証明する。runtime上界や原点条件を追加の入力に要求しない。fresh化と保護が作用するのは即時のrequest treeであり、返り値は元の `Value n` のまま保持する。潜在closureに型に沿ったtransportを挿入することと、sourceの各境界がこの割当てを使うことは別の接続義務である。

`principal_fresh_boundary` は同じ行上界と非captureの結論を、10.12.2の実際のprincipal formulaの解から導く。これにより、再帰制約生成器・独立な型判断・実際のrequest treeの上界・fresh境界の非captureが、同じresolved式について接続される。checker受理を重ねて要求しない。

## 10.13 無限の行型と有限な制約表現

この節は10.3.2の2026-11-05の確定事項を形式化する。無限の最小解を拒否せず、探索の深さや重みに上限を課さない。行の意味、制約の有限表示、解の所属を判定する算法を区別する。

### 10.13.1 無限行の衛生性

`InfiniteRowHygiene` は既存の `RecursiveRows.SetRow` と同じ集合行を使う。`release_protect` と `protect_release` は任意の無限行に対する両方向の相殺を示し、`protect_included_iff` は包含を保存・反映する。`residual_greatest` は残余が捕捉不能な最大部分集合であることを示す。古い座標の重みには負の値も許す。

`eval_mapScopes` は未知tailに無限行を代入した全 `RowExpr` で、境界の単射による変更と評価が可換であることを証明する。`least_reindex` は残余を含む再帰問題全体について、新しい境界で求めた最小解が、元の最小解全体の像に等しいことを示す。fresh座標の原点条件はこの等式から構成できる。

`explicit_head_protected_tail` は `[key,'e]` の明示的なheadを処理した後も保護されたtail全体が残ることを示す。tailは同じkeyを含んでよく、無限でもよい。実行上界は既存の `Computation.AllRequests` に集合行を渡して定義する。`shallowHandle_bounded` は元のinput行を継続に保持して、armのeffectを残余の外へ加える。`fresh_boundary` は無限行上界の保存と非captureを同時に導く。これらの合成定理で受け取るruntime上界を、任意のsource型付けから導いたとは主張しない。

深さ2でもresponseごとに任意に大きな重みを要求するtreeを構成し、`infinite_tree_bound` で実際の `growing` の最小解による上界を、`infinite_tree_has_no_finite_bound` で任意の有限list上界の不在を証明する。この例をsourceから生成できるという主張ではない。

### 10.13.2 有限graphへの正確な変換

`RecursiveRowGraph.compile` は、既存の有限問題をheadまたはslotからtarget slotへ進む有限edge列に変換する。edgeには保護・解除・残余を内側から外側へ並べたprogramが付く。`compile_models_exact` は任意の集合行割当てで全モデルを保存し、`reachable_iff_derives` は独立な有限path到達可能性と既存の最小解への所属を同値にする。

`RowTransportNormalForm.normalize` は固定keyについて各edgeを、一つの整数平行移動と有限個の禁止入力点へ正規化する。途中の残余は、その位置の零ベクトルを入力側へ逆平行移動した禁止点として残す。`execution_normal_form` は元のprogramの成功・失敗との一致を示す。総変位が零でも `protect; residual; release` は恒等とは限らず、重み−1の要求を途中で拒否する具体例を検証する。

このgraphは制約の有限表示であって、解集合の半線形な表示や所属判定器ではない。control graphが有限でも整数重みのconfiguration空間は無限であり、各edgeの禁止点をpath全体から消すことはできない。

逆方向の `FinitePointGuards.encode_run` は、任意の整数平行移動と有限個の禁止入力点を既存の保護・解除・残余で表現する。禁止点 `p` は重みを `-p.weights` だけ動かし、`residual [p.key]` を掛け、重みを戻すことで表す。同じ重みでも異なるkeyは残る。`guarded_graph_exact` はこの表現を有限graph全体へ拡張し、その独立な到達可能性を既存の `RecursiveRows.Derives` と同値にする。禁止点を持つ一般graphを解く義務は、単に過大な中間表現を選んだ結果ではない。

### 10.13.3 affineな無限行の判定

`AffineRows.Ray` はkey、基点の重み `a`、整数周期ベクトル `d` から、`a + k d`（`k : Nat`）の全出現を表す。境界数は任意に有限で、周期の各成分は負・零でもよい。`check_exact` は所属判定の正確性を両方向に証明する。各座標の整数割算から候補を一つずつ取り、零回の候補と合わせて実際の出現の等式を検査するため、探索回数は重みの大きさによる打切りではない。

`checkSubset_exact` と `checkEqual_exact` は二つのrayの包含と等価性を判定する。包含では基点と一回進んだ点の対応に加え、相手の反復indexが非減少であることを検査する。相手の周期が非零ならindexは一意で、負の傾きは十分先の点に負のindexを要求して矛盾する。周期零のsingletonも同じ入口で扱う。有限個のrayのunionに対し、各rayが一つの相手rayに含まれるかだけで全体の包含を決めるとは主張しない。

`SymbolicRows.Segment` はこのrayに任意の有限な上端を付けるか、上端なしのまま保持する。`Segment.check_exact` はどちらも有限候補で正確に判定する。上端は表す集合自体の一部であり、未知の再帰解へ勝手に加える上限ではない。この層の定理だけでは、すべての再帰制約をrayまたはsegmentへ解けるとは結論しない。

`SymbolicRows.Expr` はsegment・union・差集合からなる有限式である。`Expr.check_exact` はその所属判定を、`compile_exact` と `check_compiled_exact` はこの式で表現済みの環境に対する全 `RowExpr` の評価保存と所属判定を示す。保護・解除はkeyごとに基点を移し、周期と上端を保つ。shiftには両方向の逆写像があるため差集合も保たれる。残余は扱うkeyのraw点だけを有限集合として除く。再帰式の未知環境を求める算法ではない。

`SegmentDecisions.checkSubset_exact` は二つのsegmentの包含を判定する。sourceの上端が有限ならそこまでの全点を検査する。両者とも上端がなければrayの包含を使い、sourceだけ上端がない場合は周期が全座標で零かつ基点がtargetに入ることを検査する。非零周期なら無限個の異なる点を生むため有限targetには収まらない。`checkEqual_set_exact` は両方向の包含と集合行自体の等号の同値を示す。有限sourceの処理量は実際の上端に依存する。

### 10.13.4 生成制約から無限行による実行上界へ

`InfiniteOperationalCorrespondence` は10.12の `OperationalCorrespondence.erase` と `principal`、`OperationalTyping.Expr` と `eval` をそのまま共有し、構造型の行だけを `RecursiveRows.SetRow` で解釈する。`erasure_typing_sound` は全resolved式の型判断から、全requestの行上界と返却値の構造型解釈を導く。union・intersection・arrow、computed let・値制限付き多相let、request・境界・shallow handlerを含む。handlerのaction・return節・operation節のruntime上界は前提として渡さず、型付けの帰納法で導く。

`principal_operationally_valid` と `principal_effect_bound` は、既存のprincipal formulaの集合行モデルでの解から、同じ閉式の評価木についてこの結論を導く。`principal_fresh_boundary` は同じ解・同じ評価木から、fresh座標へのliftとdefault protect後の行上界、および任意の内側shallow handlerによる非captureへ接続する。有限行checkerの受理を仮定しない。

これは与えられた制約解の健全性であり、任意の無限行制約を解くsolverではない。resolved shapesと同じAtom carrierによるunit署名という10.12の制限は残る。source elaboration、異種payload署名、runtimeの再帰構文、返却closure内部のscope変更と型に沿ったwrapper挿入は別の接続義務である。

### 10.13.5 一つのguard付き再帰cycleの最小解と判定

`CyclicRows.SeededCycle` は一つのkey・初期program・反復programを持つ。その `problem` は既存の構文だけで表した二つの下限制約からなる。

```text
wrap(initial, head key) ≤ r
wrap(body, r) ≤ r
```

初期programが失敗すれば最小解は空になる。成功した初期点を `a`、bodyの正規形の変位を `d`、有限禁止入力点の集合を `F` とする。到達可能なのは、すべての `j < k` について `a + j d ∉ F` を満たす `a + k d` である。`firstHit` は各禁止点の有限なindex候補から最小の一致を計算する。一致がなければ全ray、一致する最初のindexが `h` なら `0 ≤ k ≤ h` のsegmentを返す。点 `h` 自体には到達済みであり、そこからの次のbody実行が失敗するため、上端は含める。

`Cycle.firstHit_exact` と `no_hit_exact` はこの停止点の意味を、`SeededCycle.solve_exact` と `solution_least` は求めた有限表示が元の二規則の最小集合解そのものであることを証明する。`check_exact` と `check_rejects` は所属の成功・失敗を実際の `Derives` と同値にする。任意の符号付き初期点も `Cycle.asSeeded` で有限の初期programに変換でき、`Cycle.check_derives` と `solution_least` が接続を示す。境界数は任意に有限で、周期の符号・零座標・零周期を制限しない。

`CyclicRowDecisions.checkSubset_exact` と `checkEqual_set_exact` は二つのこの問題を解いてから比較し、元の問題の最小解同士の包含・等号と一致する。初期programが失敗する空解も扱う。これは表示済みsegmentだけの比較から、既存の再帰制約の解同士の比較までを閉じる定理である。

例では、無制限に増加・減少する重み、正味変位が正でも途中のresidualで止まるcycle、上端の包含、零周期、初期点からのbody失敗、初期program自体の失敗、別境界に非零重みがあるため捕捉されない場合、異なる二つのcycleが同じ有限最小解を持つ場合を検証する。これらの算法は無限解を拒否せず、深さ・重みの人工的な上限を設けない。

### 10.13.6 一般の相互再帰に残る証明義務

有限禁止点を残す任意の分岐と複数cycleが相互作用する問題については、最小解の所属決定、有限な半線形表示の構成、その表示間の包含・等価性の決定は未証明である。禁止点のない一般graphの有限半線形表示は10.13.8で、禁止点の無害性を指定座標の不変条件から検査できる範囲は10.13.9で構成する。10.13.5の一つの反復programへの制限を、言語の制限やそれ以外の問題の拒否規則にはしない。10.3.2で確定した無限最小解の許容は、すべての問題についてそのまま保つ。

禁止点を除いた整数vector addition systemの到達集合には、有効なPresburger表示がある（[Haase–Halfon, 2014, Corollary 10](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/HH-rp14.pdf)）。その結果から、禁止点を保持する本問題の結論をそのまま導くことはできない。`guarded_graph_exact` により、必要なのは有限禁止点付き整数平行移動graphについての対応する到達定理である。ここでは一般の決定不能性も主張しない。推論された無限行の再帰表示には7.3bで確定した `as` を使う。複数の相互再帰変数の具体的な表記は引き続き未決である。

### 10.13.7 推論表示の `as` と最小解

7.3bと2026-11-05の確定事項28に従い、`RecursiveRowDisplay.AsRow` は単一の行変数を束縛する有限の `RowExpr` 本体を持つ。その意味は既存の `RecursiveRows.Derives` による最小解である。`unfold_set` は展開・折り畳みで集合行が変わらないことを、`least` は任意の前固定点に含まれることを証明する。自己参照だけでseedのない本体は空の最小解となり、任意の固定点を勝手に選ばない。

`AsRow.ofProblem` はslotが一つの任意の有限問題について、すべての下限を有限unionにまとめる。`ofProblem_exact` と `ofProblem_least` は、得られたbinderが元の問題の最小解を正確に表すことを示す。元の問題は分岐や複数cycleを含んでよい。ただしこの有限な再帰表示を構成することから、所属・包含の決定手続きは導かない。

`Display.render` は既に確定した一つの境界を意味情報として持ち、`[k, 'e] as 'e`、`[k, 'e?] as 'e`、`[io, 'e[io]] as 'e` の形を出力する。default tailは保護、`?` は解除、maskに含まれるkeyはその境界で移動しない。数値重みを表示に持ち出さない。`Display.check_exact`・`checkSubset_exact`・`checkEqual_exact` は、この一stepのcycleの表示payloadについて、既存のcycle solverと展開後の意味の所属・包含・等価性が一致することを示す。

名前の変更は意味を変えない。この層は推論結果の表示payloadを扱い、型注釈の構文を追加しない。文字列のparse/roundtrip、複数の境界をまたぐ一般本体の整形、相互再帰する複数変数の表記は対象外である。

### 10.13.8 禁止点のない一般graphの半線形表示

`SemilinearWeights` は任意の `Fin n → Int` 上の線形集合を、基点と有限個の周期が生成する非負整数和で表す。半線形集合はその有限unionである。`Linear.sum_exact`・`sum_exact` は和を、`Linear.star_exact`・`star_exact` は任意の有限回の反復を、有限の同じ表現へ変換する。線形集合 `a + Span(P)` のstarは `{0} ∪ (a + Span(a :: P))` となる。基点を一度も使わず周期だけを使う点は加えない。

`Regex.compile_exact` は、union・連接・starを持つ有限な重み付き正規表現から半線形表示への変換が、独立な集合意味論と一致することを示す。整数の負成分・零成分や次元を制限しない。重みの和が可換であることを使うが、元のgraphの合法なpath自体を自由に並べ替えてよいという主張ではない。

`WeightedPaths` は任意の有限なunguarded graphからstate eliminationで正規表現を構成する。処理済みvertexを経由する合成に対する閉性を各段階で保存し、最後は全有限pathについての完全性を帰納法で導く。`solve_exact` は、実行可能な変換が返す半線形集合への所属と、独立な `Path` 判断を同値にする。vertex一覧の網羅性を入力に要求するだけで、pathの長さ・整数重み・cycleの数に上限を置かない。

この結果は禁止点のないgraphの有限表示であり、有限禁止点付きgraphへの外挿や、半線形集合の一般の所属・包含・等価性の決定手続きは含まない。表示の大きさや変換速度についても主張しない。

`SemilinearRows` はこれを既存の行制約へ接続する。固定keyについて全compiled programを正規化する。matching headは専用のseed vertexからtarget slotへ進むedgeに、slot間の依存は通常のedgeに変換する。seed vertexへ入るedgeはないため、複数のheadの重みを足し合わせて架空の到達点を作らない。`path_derives_exact` と `presentation_exact` は、全normalized exclusionが空の場合、計算した半線形表示と元の `RecursiveRows.Derives` が正確に同じ最小集合解を表すことを示す。

`summarize` はこのguard条件を自分で有限に検査する。slot一覧がslot型全体を覆うという前提の下で、`summarize_exact` は返された表示の正確性を導く。残るguardがあればこの入口では未対応として返し、言語の拒否規則にはしない。全slotを網羅する有限一覧と任意の境界数を扱い、各座標の符号・大きさやpath長を制限しない。`SemilinearRowExamples.whole_quadrant_in_presentation` は、2slotの相互再帰と別のself loopが混ざる実際の問題で、すべての `p, q : Nat` に対する `(p, -q)` の所属を示す。途中のresidualが負の入力点を除外する場合に、そのguardを消去しないことも検証する。

さらに `WeightedPaths.solveFinite` はgraphのedge targetを自分で列挙する。pathの帰納で必要な中間vertexはこの集合に含まれるので、`solveFinite_exact` にはvertex型全体の有限性や外部の列挙を要求しない。`SemilinearRows.summarizeFinite_exact` は同じ入口を元の行制約まで接続する。slot識別子を `Nat` のような無限型で表す場合も、問題自体の有限性と実際のguard検査だけで有限半線形表示の正確性が成立する。

### 10.13.9 不変な座標で禁止点を避ける再帰問題

`GuardedAffineRows` は、固定key、指定座標 `j : Fin n`、各slotのpotential `h : Slot → Int` をcertificateとして受け取る。slot間のedge `u → v` の変位を `d` とすると、有限checkerは `h(u) + d(j) = h(v)` を検査する。さらにそのedgeの全禁止入力点が、別keyを持つか、座標 `j` の値が `h(u)` と異なることを検査する。head edgeはraw出現に対して実際のguardを実行し、失敗したseedは加えず、成功したseedがtargetのpotentialを満たすことを検査する。

`path_state` は全中間vertexで重みの指定座標がそのslotのpotentialに等しいことと、元のguardを通った導出の両方を保持する。最後の総変位だけからguardを消すのではない。検査が通れば、任意の分岐・複数cycleの経路をunguardedな重み付きgraphへ移しても到達集合が変わらず、`checkedSummary_derives` が実際に返した半線形表示と既存のrow構文へ埋めた問題の最小解の同値を示す。

`CertifiedRowSummaries` は任意の元の `RecursiveRows.Problem` を直接受け取る。既存のcompile結果の各programを固定keyで正規化し、`normalized_reachable_exact` と `normalized_derives_exact` がそのguard付きgraphと元の導出を双方向に結ぶ。各stepでkeyの保存を復元してから正規化の実行等式を使うため、異なるkeyのheadを混ぜない。`checkedSummary_derives` は実際のchecker成功だけから、返された半線形表示の意味が元の `problem` の `Derives` と全整数重みについて一致することを示す。別途encodeして作った問題だけを結論にするものではなく、全slotの列挙も外部のguard安全性の仮定も要求しない。

具体例では、一座標を1に保ち、他の座標を正負のcycleで任意の整数へ動かす。両cycleは非空の禁止点を持つが、禁止点の第一座標は0なので到達しない。同じpotentialで実際のseedを除外するguardはcheckerが未対応として返す。直接のrow ASTで `protect`・`release`・`residual` を組み合わせ、slot識別子を `Nat` とする例も接続する。

この層は指定したcoordinate/potentialを検査する一つのcertificate familyであり、その発見・探索や一般のguard問題を解く算法ではない。検査失敗はこの入口が表示を返せないことだけを意味し、言語プログラムや無限解の拒否にはしない。半線形表示を構成することと、一般の所属・包含・等価性を判定することも区別する。

## 10.14 SCCで固定するmethodと呼出し側の可視impl

この節は2026-11-05の確定事項29–32と章6.2–6.4を接続する。入力に残るsourceの名前解決・制約収集と、ここで実装・証明した選択および検査を区別する。

### 10.14.1 SCC確定時の選択と後続代入

`MethodResolution` はSCC最終時点のreceiver知識を受け取る。未知なら、可視roleからmethod名を持つ相異なるroleを数え、0個ならfield制約、1個ならそのrole method、複数なら曖昧とする。同じroleの重複は候補数を増やさず、順序も結果を変えない。既知の構造receiverでは既存の `StructuralBase.Ty.lookup` でfieldの有無を計算し、存在するfieldを優先する。fieldがない場合のnominal/inherent/effect/unionのlookup結果は入力であり、この層が全lookupを実装したとは主張しない。

`FrozenMethods` は選択済み参照を既存の `.field` または `.app (.method declaration) receiver` へ変換する。`generateDot_exact` と `principalDot_exact` は、選択とfield/methodの契約を直接述べる独立な型判断との双方向一致を証明する。`FrozenDot.principal_substitution_exact` は、captured slotとresult slotを含む任意の後続代入でも同じ選択と宣言の要求が残ることを示す。具体化時のreceiver型でlookupを再実行しない。

`FrozenMethodExamples.fixed_selection_changes_acceptance` は、未知receiverで選んだ `Size` が後の `box` の `size` fieldで置換されないことを、実際のprincipalの拒否として示す。同じSCC内でreceiverが既知ならfieldを選び、同じ最終型のprincipalがimplなしで成立する。保存したqualified schemeは正確に `Size box` を要求し、定義自体は抽象辞書の下で検査できる。例の `box` は構造型carrierであり、nominal型のelaborationを代替しない。最終snapshotの算出、role scopeとmethod宣言tableの整合性検査は上流の義務となる。

### 10.14.2 呼出し側の可視性と実際の辞書木

`RoleVisibility.resolved_mono` は可視impl集合の増加に対し、成功が成功または曖昧にしか変わらないことを、`ambiguous_mono` は曖昧さが保存されることを示す。`resolve_congr` はmembershipが同じなら順序・重複によらず結果が同じことを示す。全体のcoherence条件やorphan ruleを追加しない。別fileの同じheadは各々の呼出し側で解決でき、両方が見える呼出しだけで曖昧になり得る。

`RoleDictionaries.buildResolved` は既存のresolverの成功から、実際に選んだimplとすべてのwhere子を持つ辞書木を計算する。再帰は同じPatersonのサイズ減少で停止し、全nodeで同じrootの可視集合を使う。`elaborate_success_iff` は成功と辞書木の存在を同値にし、`elaborate_all_visible` は木全体の宣言が呼出し側から見えることを示す。`elaborate_mono` は可視集合が増えてなお成功する場合、rootだけでなく全子の宣言選択が同じになることを証明する。

`useEvidence` は既に渡された辞書を先に使い、存在しない場合にだけ受取側でresolverを呼ぶ。`useEvidence_exact` は既存の `WithEvidence` と成功条件が一致することを、`useEvidence_preserves` は渡された辞書の木が受取側の別impl・impl不在・曖昧さで選び直されないことを示す。辞書payloadは宣言identityと子辞書であり、source method bodyの実行や重複given binderのsource選択規則は対象外である。

### 10.14.3 EOFのfile可視性

`ModuleVisibility.FileScope.select` は、宣言が自fileまたは読み込んだfileの所属であることと、通常のaccess検査を通ることを要求する。その結果だけを実際の `finishModule` とresolverへ渡す。`finish_exact` は既存の公開型閉性・全pending roleの充足・scheme構成と接続し、`finish_congr` と `finish_append_hidden` は同じ可視集合ならEOF結果が変わらず、非可視宣言の追加も影響しないことを示す。全where子も同じfile可視集合を使う。

sourceのimport構文・access規則の解析は入力に残る。別のsource implは別の `Roles.Impl.key`、同じ宣言の重複importは同じidentityとして供給する必要がある。この層だけでは未定型を推論せず、与えられた部分割当てを検査する既存入口へ可視性を接続する。

`ModuleDictionaries` は同じfile selectorを実際の辞書elaboratorへ渡す。`elaborateAt_all_origins` は返った木の全nodeについて、自fileまたはloaded fileのaccess可能な宣言に由来することを示す。`elaborateAt_congr` は非可視宣言・順序・重複に対する木全体の不変性を保つ。`crossing_file_preserves_dictionary` は、そのfileで構成した辞書を、任意の別fileのcatalogの下でも同じ木として使うことを示す。受取側のcatalogが元のimplを含むという前提は要求しない。

### 10.14.4 可視ground headからEOFの弱型を推論する範囲

`EOFRoleInference` は、残る弱型slotを `Fin k` で表し、全slotを直接引数に持つpending predicate `Role ?a₀ … ?aₖ₋₁` をanchorとする。そのroleについて見えるimpl headがgroundなら、型タプルの候補を宣言headそのものから列挙できる。他roleのheadとnested whereには多相性を許す。rowは既に解かれたものを入力とし、型の損失のない第一階表現 `TypeCodec` と、残る通常制約の実行可能な検査を明示的に受け取る。

候補ごとに既知の型との一致、通常制約、すべてのpending roleを検査する。`completion_is_candidate` は、固定rowとこれらの検査を満たす任意の意味的代入が必ず列挙に入ることを証明する。有限候補集合の完全性を外部仮定にはしない。`infer_unique_exact`・`infer_missing_exact`・`infer_ambiguous_exact` は、それぞれ任意の代入全体での一意completion・completion不在・異なるcompletionの存在と対応する。

`finalize` は一意に残ったタプルからactual assignmentを構成し、実際の `finishModule` が返したclosed interfaceと一緒に返す。`finalize_exact` は一意completionとの同値を、`finalize_preserves_known` と `finalized_scheme_exact` は既知型と保存schemeの意味を保つことを示す。`checkedFinalize` はground headとanchorの存在を自分で有限に検査するため、成功の健全性にはこれらの外部仮定を要求しない。`finishFile_congr` は可視集合が同じなら推論したassignmentとclosed interface全体が不変であることを示す。

実例は、未定型をintへ決めてexportする場合、二つの弱型を同時にint/strへ決める場合、候補型が二つある場合、同じ型に異なるimplが重複する場合、同じ宣言を重複importする場合、既知型・通常制約を保持する場合、fileのimport可視性が変わる場合を区別する。一意の型と一意のimplは混同しない。

ground head条件または全slotを覆うanchor条件が満たされなければ、`outsideFragment` で返す。解決済みrow、codec、通常制約checkは型付き入力として受け取り、それらの有無をこのBool検査で判定するわけではない。一般の `impl Default (box 'a)` から `box ?a` という形を決め、残る弱型を最小型solverへ渡す処理を、ground型が一意でないという理由で拒否しない。anchor roleの選択と一般制約からの抽出、anchorが覆わないslot、未定row、一般通常制約solver、一般型モデルのcodecは別の接続義務である。`noCompletion` はすべての検査を通るcompletionがないという内部結果で、具体型に対するimpl重複も含む。章6.3のimpl不在と曖昧さのdiagnosticsを細分する処理は、この入口ではまだ接続していない。
