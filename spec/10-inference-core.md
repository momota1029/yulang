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

これは旧実装のdirected stack全体の正しさを主張するものではない。今回の核では有限の解決済みshapeを扱い、atomとoperation payloadの内部は不透明のままである。sourceからshapeを作り、変換を挿入し、`ZeroAt` に相当する由来の条件を保存するelaborationは別の証明義務とする。10.17では、既存の実行モデルのcomputation引数と返却closureに対するwrapperを構成し、その型との対応を接続する。

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

`RecursiveExamples` は、再帰時に引数をpairへ包むdepth型の本体について、全注釈による受理と、`any -> int` による単相での受理を示す。決定36以前のtopを持たない有限型モデルでは単相拒否を証明していたが、現在はpairの引数を `any` に広げられるため、その拒否命題は成立しない。`unannotated_depth_typable` と生成制約・closed SCCへの接続が、この仕様変更の具体的な証拠である。全注釈による多相再帰の規則自体は維持する。

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

有限禁止点を残す任意の分岐と複数cycleが相互作用する問題については、最小解の所属決定と有限な半線形表示の構成は未証明である。既に有限半線形表示が得られた集合の所属・包含・等価性は10.15で完全に判定する。禁止点のない一般graphの有限半線形表示は10.13.8で、禁止点の無害性を指定座標の不変条件から検査できる範囲は10.13.9で構成する。10.13.5の一つの反復programへの制限を、言語の制限やそれ以外の問題の拒否規則にはしない。10.3.2で確定した無限最小解の許容は、すべての問題についてそのまま保つ。

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

この結果は禁止点のないgraphの有限表示であり、有限禁止点付きgraphへの外挿や、半線形集合の一般の所属・包含・等価性の決定手続きは含まない。表示の大きさや変換速度についても主張しない。得られた任意の半線形表示についての完全な判定は10.15を参照する。

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

この節は2026-11-05の確定事項29–33と章6.2–6.4を接続する。入力に残るsourceの名前解決・制約収集と、ここで実装・証明した選択および検査を区別する。

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

### 10.14.4 EOFで未定型をimplから補完しない

章6.3・2026-11-05の決定33により、EOFまで未定の型変数を、唯一の可視impl headから決めることはしない。通常の推論または注釈で型が決まってから、そのfileの可視implによる一意・曖昧・不在の検査を行う。これは以前の決定32の訂正であり、旧completion実験の成功例を現行言語の受理例とは扱わない。

`EOFNoDefaulting.finish` は既存のinterface supportを先に走査し、未定slotがあればそのslotを返して失敗する。すべて決まっている場合にだけpending roleを具体化し、既存の停止するresolverを呼ぶ。入力の部分割当てを補完する処理はない。`finish_success_iff` と `finishFile_success_iff` は、それぞれ既存の `ModuleRoles.finishModule` とfile可視な `ModuleVisibility.finish` の成功に正確に一致することを証明する。

`undetermined_exists_iff` は、support内に未定slotがあることと未定型エラーを同値にする。`undetermined_catalog_independent` はこのエラーが任意の可視impl集合の間で不変であることを示す。`role_error_sound` は、roleエラーを返す段階ではsupport全体が既知であり、返された具体goalについて実際のresolverが失敗したことを示す。公開値に現れず残留role制約にだけ現れる未定slotも検査から漏らさない。一般化されたslotはambientな未定slotとは区別する。

`accepted_no_unresolved` と `accepted_export_independent` は、成功した公開interfaceの閉性と、入力割当ての任意の全域拡張に対する意味の独立性を保つ。`accepted_with_more_impls` は、可視implを増やしたとき、同じclosed interfaceのまま成功するか、具体goalの曖昧さになることを示す。別の弱型を選び直すことはない。既知型に対するimpl追加で曖昧さが起こり得るという章6.2の規則はそのまま保つ。

旧 `EOFRoleInference` は参考実装として残すが、現在の核をまとめる `Yulang` からはimportしない。独立した実験として公理監査には含める。そのground anchorからのcompletionは現行言語の推論入口へ接続しない。sourceからの残留制約の漏れない収集、ambient/generalizedの分類、通常型推論そのもの、source診断の位置と文言は上流の義務として残る。

## 10.15 整数重みの完全な判定と自動guard検査

### 10.15.1 任意の半線形集合への所属

`SemilinearDecisions.checkSpan` は、任意の整数vectorの有限リストが生成する非負整数和への所属を判定する。係数に上限を置かず、各係数の二進数字を一桁ずつ選ぶ。状態qと次のcarry q′は `q = digit + 2q′` を満たす。`digit`は各周期を0回か1回選んだ和である。入力vectorと周期の絶対値から有限のcarry boxを構成でき、係数のhalvingによって任意の真の組合せからそのbox内の到達経路を構成する。状態空間の有限化は係数や再帰の展開回数の打切りではない。

`checkSpan_exact` は独立な `Span` 判断と、`check_exact` と `check_rejects` は有限unionの `Meaning` と正確に一致する。周期の正負・次元・相殺を制限せず、空周期・零周期・空集合・0次元も含める。`FiniteBooleanReachability.closure_exact` は実際に構成した有限Boolean行列と全有限pathの一致を支える。

### 10.15.2 任意の半線形集合の包含と等価性

`SemilinearDigits` は各座標が−1・0・1の有限alphabetを使い、整数vectorを有限語の値として表す。符号付き絶対値のhalvingにより `value_surjective` を証明する。`SemilinearAutomata` は半線形集合を有限NFAへ変換する。carryの遷移は `2q′ = q + periodDigit − inputDigit` であり、終状態の受理には既存の `checkSpan(periods, −q)` を使う。この検査は入力語より上位に残る任意の係数桁を吸収するため、短い語や末尾の零の個数に依存する欠落がない。

`accepts_exact` はすべての語について、NFAの受理とその語の整数vectorが `Meaning` に属することを同値にする。`FiniteAutomata` の全有限語に対する包含判定を用い、`checkSubset_exact` は全整数vectorを量化する集合包含を、`checkEqual_exact` と `checkEqual_sets` は意味的な等価性を完全に判定する。非包含時には `checkSubset_rejects` が実際の整数vectorの反例の存在を与える。sourceの各線形成分がtargetのどれか一成分に入る、という不完全な置換はしない。自然数全体が偶数と奇数のunionに等しい例も形式化する。

これは停止する参照判定器であり、実用上の小さい計算量を主張しない。有限NFAの比較は冪集合構成を含み、半線形表示自体も大きくなり得る。これらの定理は、禁止点を持つ任意の到達集合が半線形であるという未証明の主張を含まない。

実行時のNFA比較には `FiniteWorklist` を使い、初期状態対から到達する後続だけを列挙する。新しい状態を処理するたびに有限全状態数から容量を減らすが、既出のpending状態では減らさない。pendingが空なら到達集合は閉じており、容量を使い切った場合は相異なる訪問済み状態が全状態を尽くす。この二場合から `reachable_exact` が任意長のpathについて完全性を証明する。NFA対の容量は `2^n * 2^m` から自動計算し、全冪集合の列挙は証明だけに使う。呼出側のfuelや言語の再帰上限ではない。各状態対のBoolean座標も一度だけ実体化し、過去の遷移を座標参照のたびに再計算しない。

`FiniteWorklistExamples` は高速な包含成功を経由せず、NFAの入口を直接実行する。自然数全体と偶数・奇数の和では、5状態と14状態のNFAからなる524,288通りの候補対のうち、到達する5対だけを訪問する。共同被覆の肯定、偶数だけへの包含の否定、同じ無限rayへの包含を実行検証し、全有限語についての論理的保証は別のkernel検証された定理で与える。

### 10.15.3 外部certificateを要求しないguardの検査

`AutomaticRowSummaries` は元の有限 `RecursiveRows.Problem` とkeyを入力とする。head edgeのguardは実際に実行して、失敗したseedを無効にする。slot edgeのguardだけを一旦消したgraphについて、各sourceへの到達集合を半線形表示する。元の各禁止点がそのsourceの到達集合にないことを、10.15.1の完全な所属判定で検査する。空の禁止集合と別keyだけの禁止集合では、この表示の計算を省く。

`GuardedRowErasure.path_state` は各途中状態で元のguardを通過することを保つ。`AutomaticRowSummaries.check_exact` は、checkerの成功と、この十分条件 `Harmless` の一致を示す。`summarize_exact` は返された有限表示が元の `Derives` と全整数重みについて一致することを、`query_exact` と `query_false` は返された所属・非所属の答えの正確性を示す。座標・potential・任意のSlot型全体の有限列挙を入力に要求しない。`certified_is_supported` により既存の座標certificateが通る場合もこの自動入口で扱える。

十分条件が満たされなければ `none` を返す。この値は一般のguard問題がこの入口では未対応であることを表し、プログラムの拒否や非所属を表さない。到達するguardが意味的に冗長な場合もあるため、この条件を半線形表示の存在やguard消去可能性の必要条件とは呼ばない。

直接のrow ASTを使う例は、重み1のseedから2ずつ増える無限行と、入力点0を禁止するcycleを持つ。偶奇によってguardの無害性を判定し、1・3への所属、2・−1への非所属を実際のqueryで検証する。seedが0の例ではguardを消すと余計な到達点が生じるので、未対応として返す。有限graphのstate eliminationでは、同じtargetを一度だけ消去する。重複消去を省いても `solveFinite_exact` の全pathとの同値は変わらない。

### 10.15.4 意味を保つ正規化と高速な成功判定

`SemilinearNormalization` は零vectorと重複する周期を除き、同じ基点・同じ周期集合を持つ成分をまとめる。周期の順番が異なるだけの成分も対象とし、`span_exact` と `normalize_exact` が全整数vectorについて意味を保存する。これは最小の半線形表示を構成する主張ではない。carry boxとNFAを作る前にこの正規化を使い、冗長な構文がそのまま状態数を増やすことを避ける。

空周期は零vectorとの等号だけで判定する。単一周期では非零座標から自然数係数の候補を計算し、すべての座標の一致を確認する。`checkSingleton_exact` により、この場合は巨大な入力座標に比例するcarry boxが不要になる。包含については、各source成分の基点と周期が一つのtarget成分で表せる場合だけ `SemilinearFastInclusion` が先に成功を返す。それで成功しなければ、10.15.2の完全なunion比較を実行する。`checkSubset_preserves_result` は最適化前後のBoolean値そのものの一致を示し、偶数・奇数による共同被覆を高速経路の失敗で拒否しない。

### 10.15.5 元の制約から行全体を比較する

`SemilinearRowAlgebra.Row` は有限のkeyと半線形表示の組のリストである。同じkeyの複数entryは和として解釈し、存在しないkeyは空集合とする。keyの型自体は有限でなくてよい。`checkSubset_sets` と `checkEqual_sets` は全key・全整数重みでの比較を既存の `RecursiveRows.SetRow` の包含・等号へ接続する。

`SolvedRecursiveRows` は元の制約graphに現れるhead keyを列挙し、各keyについて10.15.3の自動summaryを集める。すべての導出がいずれかのheadに始まり、保護・解除・残余はkeyを変えないことから、列挙外のkeyには最小解の出現がない。`summarize_exact` と `summarize_decode` は返された行全体が元の `Derives` と一致することを示す。`querySubset_exact`・`queryEqual_exact` は元の二つの最小解の包含・等号を、`querySubset_rejects` は非包含の実際の出現が存在することを証明する。

この入口も未対応を `none` として保つ。現在の十分条件は全head key・全slot edgeのguardを調べるため、照会先とは別の成分の有害なguardで未対応になることもある。headを持たない再帰cycleは空の最小解となり、head自身で失敗するguardはseedを生まない。重複・順序変更したhead、複数key、存在しないslot、無限の奇数行、失敗するhead guardと未対応のslot guardを元のASTで実行検証する。

比較するのは制約の**最小解**である。下界を持たないslotの最小解が空でも、他のモデルや後のscheme具体化でそのslotが空に固定されるとは限らない。この判定を、開いた行変数のすべての後続具体化における等価性へ読み替えない。出典: 10.3.2・10.10、上記Lean定理。

### 10.15.6 固定上界を持つ元の制約の充足可能性

`RecursiveRowQueries.extend` は、任意の有限個の既存 `RowExpr` をfreshな出力専用slotの下界として追加する。元のruleと照会式は元のslotだけを読み、追加slotから元のruleへ戻る依存を作らない。`models_exact` は拡張前後のモデルの関係を記述し、`extension_least`・`original_exact`・`query_exact` は元の最小解を保存したまま、追加slotが照会式をその最小解で評価した集合と一致することを示す。`query_iff_forced` は、そこで得る出現が元のすべてのモデルで強制されることとも一致する。

`RecursiveRowConstraints.Upper` は左辺に任意の既存row式、右辺に固定した半線形行を持つ。`check` は各左辺を上の追加slotへ写し、そのsummaryを右辺と比較する。返されたBooleanについて `check_exact` は次を証明する。

```text
check(problem, limits) = some answer ならば、
answer = true
  ↔ 元の全下界を満たし、limitsの全上界も満たす行割当てが存在する
```

証明は10.10の `upper_constraints_exact` を使い、最小解での包含と元のモデルの存在を結ぶ。`check_rejects` は `some false` と解の不存在の同値であり、単に一つの候補割当てが失敗したという主張ではない。`none` は拡張問題のguard検査が未対応であることを保ち、不整合とは扱わない。上界が空のリストなら、正の下界制約には常に最小モデルがあるので、guardの到達判定をせず成功する。右辺は固定された集合であり、未知の上界変数との相互求解や、すべての後続具体化で同じ上界を満たすという全称的な保証は含まない。

## 10.16 有限構造部分型の完全な比較

`StructuralCut.Comparison`（namespace `StructuralDecisions`）は既存の `StructuralBase.Subtype` から明示的な推移則を除いた判断である。`Comparison.trans` は任意の中間型を消去し、`comparison_iff_subtype` が元の判断との双方向一致を証明する。union/intersection・pair・variant・recordの幅と同名fieldの先勝ち・関数の入力反変と出力共変をすべて含み、関数の二つの行の向きも保つ。行関係には推移性だけを要求する。

`StructuralDecisions.check` は型の有限構造に従って再帰する実行可能な比較器であり、`check_exact` が正確な行比較を入力として元の部分型判断と一致することを示す。`checkSigned` は行比較を実際の符号付き出現の包含で実装するため、有限符号付き行では外部oracleが残らない。`checkSigned_rejects` の否定結果は、直接の比較規則だけでなく、任意の中間型を通るすべての宣言的導出の不存在を意味する。unionの順序、格子の吸収、隠れたrecord field、負の解除差分、入力行と出力行の分散を回帰例に含める。

`SemilinearRowAlgebra.checkType_exact` は同じ構造比較へ10.15.5の完全な行包含を代入する。したがって、有限ground値型の潜在行が無限集合でも比較できる。重複keyに偶数・奇数を分けた行が自然数全体と等しいこと、その行を持つ関数型の比較、keyや片方の偶奇が欠ける場合の拒否、非空の出力行を消せないことを確認する。この定理の型構文は有限半線形表示を行位置に持ち、その上で既存の構造部分型関係を使う。

集合として同じ行に複数の半線形表示があるため、表示の構文上の等号と意味上の等号は区別する。`SemilinearRowQuotient` は10.15.5の決定可能な集合等号で行を同一視し、その商から既存の `SetRow` への写像を単射にする。商上の等号と包含は実行可能であり、標準形を一意に選ぶoracleは不要である。`StructuralRowResolution.subtype_map_iff` は、構造を変えずに行を写すときの部分型の保存・反映をcut除去から導く。これを用いた `SemilinearRowQuotient.checkType_exact` と `compareCodes_exact` は、元の集合行を持つ `StructuralBase.Subtype` と正確に一致する。内部のraw型でrecordのtailがrecordでない場合の反射律も保持し、追加のwell-formedness前提で比較対象を狭めない。

`SolvedRecursiveTypes` は、各行位置に元の問題のslotを持つ有限型を入力にし、その位置だけを `StructuralRowTraversal.traverseRows` で解く。`resolve_exact` は、返された型の集合解釈が元の各 `Derives` を代入した型と一致することを示す。`querySubtype_exact`・`querySubtype_rejects` は、返された肯定・否定がその元の型同士の部分型関係と正確に一致することを、`queryEquivalent_exact` は相互部分型との一致を証明する。source側とtarget側の問題・slot型は異なっていてよく、有限なslot全体の列挙は要らない。

`resolve_supported_iff` と `querySubtype_supported_iff` は成功に必要なguard検査を実際に出現する行位置に限定する。行位置を持たない型では照会自体をしないため、別の成分に未対応guardがあっても比較できる。一方、型に現れる行が未対応なら `none` を保つ。出力行の共変・入力行の反変、非空effectの欠落の拒否、元の無限奇数行を持つ関数型の等価性、異なる行表示が意味的に等しいraw record型の反射律を実行検証する。ここでも各行の最小解を代入した型の比較であり、あらゆる後続scheme具体化における部分型関係ではない。

ここで有限なのは値型の構造であり、未知の型変数を解くbound propagationや、再帰値型の意味論を決めるものではない。Simple-sub全体のextrusion・intrusion・generalization、source elaboration、全言語のpreservation/progressは別の証明義務として残る。

## 10.17 実際のcomputation引数と潜在closureの衛生変換

この節は10.2・10.3.4で定めた計算体系への接続であり、新しいsource構文や注釈規則を追加しない（2026-11-06）。旧版の参照点は `yulang2-oracle:web/docs/ja/reference/type-theory.md` の「行表示だけでは実行時の由来を保てず、関数・thunk・構造値に衛生性を伴わせる」という意図である。符号付きの相殺とpermissionの意味は現行の10.3を使う。

### 10.17.1 実行値上のwrapper

`OperationalTransport` は `OperationalTyping.Value` と `Tree` を直接使う。既存の `DirectedHigherOrder` の関数は値を引数に取るが、この実行モデルの関数はcomputationを引数に取るため、そのまま同じ定理を適用することはできない。方向を `d`、逆方向を `opposite(d)`、値と計算の変換を `V`・`C` と書くと、arrowの規則は次である。

```text
V_d(f)(argument) = C_d(f(C_opposite(d)(argument)))
```

入力の変換は、その場のrequestと、computationが返す値の両方を対象とする。返り値のpairに格納された関数も再帰的に包むが、包むために関数を実行することはない。`value_opposite` と `tree_opposite` は、任意の有限resolved shape・任意の値と計算で両方向の相殺を示す。`value_apply_tree` は関数と引数interfaceをともに変換した呼出しの等式、`tree_bind` はsequencingとの対応である。未変換の同じ引数に対してdispatchが変わらない、という主張ではない。

### 10.17.2 checkerと主制約からの接続

静的な型の変換は、即時行とすべての潜在行を同じrequest写像の像へ移す。関数の入力型も静的には同じ向きで写す。実行時の入力wrapperが逆向きへ戻すことで、変換後の入力interfaceに適合する引数を元の関数へ渡せる。

`OperationalTransportTyping.validValue_iff`・`valid_iff` は有限行checkerの型について、`InfiniteOperationalTransport.typeHolds_iff`・`compHolds_iff` は既存の構造型について、変換後の型と値・計算の適合性が元の適合性と同値であることを証明する。後者の行は任意の集合行で、無限tail・負の重み・重みの上限なしを許す。型のunion/intersectionはそれぞれ選言・連言として保つ。

`closed_inferred_transport_valid` は既存checkerの受理から、`principal_transport_valid` は既存の `RecursiveEffects.principal` の集合行モデルでの解から、同じ `eval` へwrapperを適用した結果の適合性を導く。即時requestの上界に加え、返却・格納された関数へ適合するcomputationを渡したときの潜在interfaceも含む。handlerの各armの実行上界やcheckerの別途受理を、principal側の定理へ追加しない。

`OperationalTransportSubtyping.subtype_iff` は実行時の解釈を経由せず、元の `StructuralBase.Subtype Included` について変換前後の同値を証明する。推移則・union/intersection・pair・variant・recordの幅と先頭field優先・関数の型と両方の行の分散をすべて含む。recordとvariantの主張も空の実行時解釈から得たものではない。`comp_subtype_iff` はこの同値を既存の集合行モデルの `Inference.Comp.le` へ接続する。未知の型を探索するsolverを、この保存・反映の定理で代用したとは扱わない。

### 10.17.3 静的な出力行から非captureへ

`guarded_call_noncapture` は、元の関数の型、変換後の入力型に適合する引数、元の出力行が対象境界で重み0を持つという静的な `ZeroAt` から、既定の保護を付けた呼出しが任意の内側shallow handlerを素通りすることを導く。関数の型から逆変換した引数に対する実行上界を得て、行の原点条件から実行木の原点条件を構成する。実行木の上界や `ZeroAt` を新たな前提として受け取らない。

この出力行の条件は省略しない。局所callbackが持つ負の差分は、戻り側の正の差分と相殺され、元の呼出側で可視になる必要がある。すべてのclosure呼出しを永久に非captureにする規則ではない。

`principal_guarded_arrow_calls` は同じ保証を、変換後の評価が返す各closureへ接続する。結論の `AllReturns` は、返ってきた値すべてについての性質であり、値が返ることや計算の停止を保証しない。`fresh_output_call_noncapture` では出力行が `liftRow` であることから静的な原点条件を構成する。この系は既に拡張後の境界集合で型付けされた関数を受け取り、古いclosure自体を新しい境界集合へ持ち上げる処理は構成しない。

`OperationalTransportExamples` は、同じcheckerと評価器を使い、pair内のcallbackを即時境界だけで包む場合と高階wrapperで包む場合を区別する。前者は内側handlerに捕まり `99` を返し、後者は要求を通過させ、対応する解除で呼出側がpayload `7` を受け取る。高階invokerの入力では、callbackの値だけでなく、それを生成する途中のrequest `13` も保護する。invokerの入力にはrawと負の差分を明示し、実際のcallback・遅延producerの型と変換後の入力型との適合を検査する。出力行には相殺でraw要求が残るため、混在した由来の例を一律の非captureや純粋性の例とはしない。内側のglobが別の境界の負の差分を消さないことも同じ評価で確認する。

### 10.17.4 残る接続

今回の実行時shapeはatom・pair・arrowである。既存の構造型のrecord・variantはこの実行モデルでは空の解釈なので、その実行時表現の衛生変換までを証明済みと数えない。atom・operation payload・responseの内部も不透明のままである。

sourceからshapeと境界・permissionを決めてwrapperを挿入するpass、世界をまたぐ潜在closureの構成、任意の異種operation署名と再帰runtimeとの統合は別の義務として残る。既存の `Expr.boundary` はその場のrequestだけを変換する意味を保つ。Simple-subのbound探索・extrusion・intrusion・generalizationの全体定理も、この高階transportから自動的には従わない。

## 10.18 未知の値型の求解

### 10.18.1 下界の伝播と失敗の完全性

`ValueBounds` は、既存の `StructuralBase.Subtype` に対して未知の値型を実際に構成する。入力は有限個の未知変数と、次の有限個の制約である。

```text
A ≤ α       α ≤ β       α ≤ U       A ≤ U
```

`A` と `U` はgroundな有限構造型であり、recordの幅と先頭field優先、variant、union/intersection、関数の反変な入力と共変な出力を含められる。関数の潜在行は別途選んだ行モデルに従う。解となる未知型の候補集合や深さ上限を与える必要はない。

solverは `α ≤ β` を有向辺にし、各変数に到達する下界 `A` のunionを構成する。下界が届かない変数には既存のbottomを使う。worklistの容量は変数数から導き、同じ変数を二度展開しないことにより十分だと証明する。自己循環・相互循環を許し、呼出側のfuelや型サイズの打切りを使わない。構成した割当てを全制約に照合し、成功ならその割当てを返す。

`least_below` は、構成した割当てが、下界と変数間包含を満たす**すべての構造型割当て**以下であることを示す。したがって、何らかの解が上界 `U` を満たせば、構成した最小割当ても上界を満たす。`solve_none_iff` は失敗と解の不在を、`solve_exists_iff` は成功結果の存在と解の存在を同値にする。`solve_some_iff` と `solve_least` が、実際に返された割当ての健全性と最小性を結ぶ。

`ValueBoundSolvers.solveSigned` は符号付き有限行の比較器を内部で選ぶ。`solveSemilinear` は半線形な無限行の有限codeを入力とし、意味的な行の等価性を使う `SemilinearRowQuotient.compareCodes` へ接続する。この後者の失敗定理は、半線形な行で表現できる割当てだけでなく、**任意の集合行を含む有限構造型の割当て**を排除する。任意の解をcode化できると仮定せず、下界から作る最小解の構成とdecodeが可換である `least_mapTypes` を使う。

`ValueBoundExamples` は、相互循環を通る `int` と `str` の合流、矛盾する上界の拒否、下界のない循環、record幅と隠れた重複field、関数の分散、負のeffect差分を消せないこと、無限の潜在行を含む求解を実行して検証する。拒否例は実際の失敗から任意の割当ての不在へ接続する。

ここでの最小割当ては、多相関数の主型とは異なる。一般化すべき変数までbottomで置き換えると、入力と出力の関係や任意の具体化を失う。また、下界のないslotの数学的な最小解がbottomであることから、EOFの未定weak変数をbottomに既定化してよいとは結論しない。constructor内部の未知型、再帰値型、extrusion・intrusion・一般化を含む全Simple-subは、このflatなbound problemとは別の証明義務である。この節は既存の型代数に対する算法の追加であり、新しい言語意味論やdefaulting規則を決めるものではない。

### 10.18.2 元の再帰row制約から未知の値型まで

`RecursiveValueBounds.solve` は、元の `RecursiveRows.Problem` と、そのrow slotを潜在行に持つ値型bound problemを受け取る。ground boundに実際に現れるrowだけを `SolvedRecursiveTypes.resolve` で解決し、その後で値型の未知変数を解く。返り値は `unsupported`・`unsatisfiable`・`solved valuation` の三種類を区別する。

`solve_solved_least_eq` は、返された型をdecodeした割当てが、元の `RecursiveRows.Derives` で解釈したbound problemの最小割当てに等しいことを証明する。`solve_unsatisfiable_iff` は、失敗が「rowの解決対象が対応範囲にあり、任意の集合行を含む構造型割当てが存在しない」ことと同値であると述べる。`solve_unsupported_iff` は対応範囲外を別に特徴付ける。無関係なrow graphの未対応箇所は、rowを持たないboundの求解を妨げない。

row自体は、元の再帰問題の**固定された最小解**で解釈する。任意のrow解と値型を一緒に探索して、全制約の主解を得たとは主張しない。回帰例は、保護が積み上がる無限rowと未知値型どうしの循環を同時に扱う成功、その潜在rowを空行へ収める上界の拒否、active guardの未対応を区別する。

### 10.18.3 多相なparameterを残す消去

`ValueBoundElimination` は、既存の `Inference.TyTerm (Parameter ⊕ Fin n)` において、自由に具体化するparameterと、今回解く内部未知型を区別する。`polarity` はarrow入力で極性を反転し、出力・pair・variant・union/intersectionでは維持する。recordは固定されたspineを要求し、先頭field優先の意味を保つ。行の割当ては値型の内部未知変数とは独立して固定し、消去によって変更しない。

正の極性が検査できた出力型 `T` では、`inferTerm` がboundを解いて出力型 `T₀` を構成する。`inferTerm_exact` は、任意の観測型 `U` について、`T₀ ≤ U` が「元のboundを満たす割当てで `T ≤ U` となるものが存在する」ことと同値であると示す。`parameterized_exact` はこの同値をparameterの全インスタンスへ接続する。内部未知型の負の出現は、この消去方式では未対応として返し、解なしとは扱わない。

恒等関数では、引数の値型 `A` と行 `R` をparameterとして残し、内部の結果型 `β` に `A ≤ β` を課す。`identity_inferred` は、任意の `A` と `R` について実際のsolverが成功し、`A [R] -> (A | never) [R]` を返すと証明する。`identity_result_equivalent` により、これは `A [R] -> A [R]` と相互部分型である。`identity_principal_exact` は、この計算された型族の全インスタンスと、既存の `Inference.principal [] (lam (var 0))` の意味を同値にする。式自身の型付けやsolverの成功を前提に渡す定理ではない。

`negative_minimization_loses_instance` は、出力 `α -> int` に内部未知型 `α` を使い、boundが空のときの反例を与える。`α = int` なら `int -> int` に適合するが、最小解 `α = never` を代入すると適合しない。したがって極性の条件を外せない。二度の反変位置は正に戻ることも実行して検証する。一般化するparameterをsourceから自動で発見することは、この消去定理とは別の義務である。

### 10.18.4 核の式からの推論と元のprincipal formula

`ValueInference.solve` は既存の `Inference.Expr` を入力とし、変数・リテラル・分岐・let・pair・variantの値型を実際に構成する。途中のshape、未知型の割当て、式自身の制約解は入力に要求しない。入力環境は純粋に参照できる既知の値型の列で、内部には任意の構造型と符号付き有限潜在行を含められる。pairとvariantの型の形も式から決める。分岐は、条件型を `bool` と照合し、両枝からfreshな結果slotへ下界を流す `ValueBounds.solve` を呼ぶ。

`source_solved_exact` は、返された値型 `T` と任意の結果computation `(U, ε)` について、元の `Inference.Typing` が成立することと `T ≤ U` を同値にする。この断片は純粋なので、結果行 `ε` は任意の上位行でよい。`source_unsat_iff` は対応構文での拒否が、どの値型・符号付き行を選んでも元の型付けが存在しないことと同値であると示す。環境の条件は `monoEnvironment_principal` で既知型リストから構成する。

`closed_principal_solved_exact` と `closed_principal_unsat_iff` は、閉じた式について同じ結論を**元の `Inference.principal` が生成するformulaそのもの**へ接続する。fresh slotの存在量化も、値letの一般化経路と単相経路の選言も残したままである。健全性の証明は既存の `letComputed` を使い、完全性は `letValue` の各具体化も扱う。この断片では後者が計算済みの最小型に含まれることを証明するので、生成器の一般化経路を取り除く仕様変更ではない。

結果は `solved T`・`unsat`・`unsupported` を区別する。lambda/applicationはこの一般入口では未対応であり、型付けできる恒等関数も未対応になる例を置く。10.18.3の恒等関数の専用定理を、任意の関数推論の完成と混同しない。variantは既存の `StructuralBase` のconstructorについての結果であり、章4.5の同一tagのpayload合流、case残余、sourceの網羅性検査との統合は別に必要である。

`ValueInferenceExamples` は、混在分岐の `int | str`、不正な `int` 条件の全解の不在、pair/variantの構成、値let・計算let、shadowing、未束縛変数、値型内の負のeffect差分の保持をkernelと通常のコード実行で検証する。`lean/RunValueInference.lean` はこれらの入口を呼ぶ小さな実行例である。`never` を含む冗長なunionは内部表現に残り得る。章7.4bの完全な表示標準形を、このsolverの出力に仮定しない。

### 10.18.5 全体solverへ残る義務

ここまでで閉じたflat boundの求解と、上の核の式の推論については、解の構成・失敗の完全性・それぞれの主性または最小性・停止がそろう。constructor内部の未知型と再帰値型の制約は、後述10.21で独立に解く。一般のlambda/application、SCCと一般化変数の発見、extrusion/intrusionを含むsource全体への接続は別の義務である。任意のguardを含む再帰row問題や、未知の値型と未知の行を同時に解く全体手続きも、この結果から自動的には得られない。

値型注釈が公開型を決める章4.2の規則、T3の観測時点、role・cast・case・sourceの境界割当てを、この実行可能な推論入口へ接続する義務も残る。今回の追加で、既存の注釈・衛生性・EOFの非defaultingの意味は変更しない。

## 10.19 `any`・上界の双対・全解の型スキーム

出典は章4.1、章7.4b、およびhandoffの決定36・37（2026-11-06）である。

### 10.19.1 topを含む核

`StructuralBase.Ty.top` と `Inference.TyTerm.top` が、書ける型 `any` を表す。全型 `A` に `A ≤ any` が成立する。逆に `any ≤ int` や `any ≤ A -> B` は成立せず、任意の型へ暗黙に狭めるescape hatchではない。四つのliteral用の `Base` には追加しない。

topを含む独立の `Subtype` に対してcut eliminationと `StructuralDecisions.check` の完全性を拡張した。有限・集合の両行解釈、型内の行変換、cast表現との往復もtopを保つ。関数の入力が `any` でも、関数に付く保護済みeffectや負の解除差分を消せないことを検証する。

### 10.19.2 負の位置の最大解

`ValueUpperBounds.greatest` は、`αᵢ ≤ αⱼ` の辺を辿って到達する全上界を交差する。

\[
U_i=\bigcap\{A\mid i\leadsto j,\ (\alpha_j\le A)\in C\}.
\]

空の交差は `any` である。`greatest_above` は任意の上界モデルがこの割当て以下であることを、`greatest_models_iff` は元の制約が可解であることとこの最大割当てが全制約を満たすことの同値を示す。`solveGreatest_none_iff` の失敗は、型の深さや候補集合に制限のない解の不在と一致する。

`inferTerm_exact` は、内部未知型がすべて負の位置に現れる出力について、最大解を代入した結果の上位型全体が、元の全モデルから得る出力の上位型全体と一致することを示す。`negative_principal_exact` は、以前の `negative_minimization_loses_instance` と同じ例を、全インスタンスについて `any -> int` へ正確に閉じる。正負の両方に現れる変数は、この一方向の消去では扱わない。

### 10.19.3 混在する極性と自由parameter

`ValueBoundSchemes.solve` は、flatなbound problemの**全解**を表す有限な型スキームを構成する。`L_i` を下界の伝播で得たunion、`U_i` を上界の伝播で得たintersectionとして、各未知型に次の式を割り当てる。

\[
S_i(\rho)=L_i\cup\bigcup_{j\leadsto i}(\rho_j\cap U_j).
\]

`ρ` は制約のない自由parameterの割当てであり、正負の位置で同じparameterを共有する。返り値の `Term` はground型・parameter・union・intersectionだけの構文で、具体化の際に再検査する不等式を含まない。

`expand_models` は、元の制約が可解なら**任意の** `ρ` に対して `S(ρ)` が全制約を満たすことを示す。`expand_equivalent` は、元の任意の解 `v` を `ρ` に選ぶと `S(v)` と `v` が各slotで相互部分型になることを示す。この二方向が、解を失わず余分な解を加えないことの証明である。

`solve_models_exact` は計算されたスキームの全具体化と元の全モデルを対応させ、`principal_exact` は相互部分型を保つ任意の出力型へ接続する。出力の極性を正か負の片方に制限せず、恒等関数のような入力と出力の相関も維持できる。constructorの分配則は仮定しない。

これはboundがgroundである有限graphの完全な制約消去である。bound自体のconstructor内の未知型、再帰値型の `as`、source全体からの一般化・effect行の同時求解は別の接続として残る。EOFの未定weak slotをこの自由parameterへ勝手に一般化する規則は導入しない。

`ValueBoundSchemeInference.infer` は、この構成を既存の `TyTerm (Fin n)` と固定されたrow割当てに接続する。混在する極性を認め、固定record spineの検査だけを要求する。`infer_principal_exact` は実際の呼出しから得たschemeの全具体化を元のboundと出力termに対応させる。`infer_retains_rows` は、値型の置換によってrowや出力構文が書き換わらないことを示す。

## 10.20 共有parameterの意味を保つ簡約

出典は決定37(2)と、Simple-sub論文の§4.3である。資料と実装の固定revisionは [`lean/REFERENCES.md`](../lean/REFERENCES.md) に記す。ここで使うconstructorの法則は既存の構造部分型のままであり、論文のcompact representationが使う追加の分配等式は採用しない。

`TypeSimplification.occurs` は変数ごとの正負の出現を数え、`simplify` は正だけの変数を `never`、負だけの変数を `any` へ置く。両方に現れる変数は同じまま残す。値型の変数を置換しても、そのslotのrow変数は保持する。`simplify_instances_exact` は、具体的な一つの割当ての比較ではなく、存在的な全割当てとsubsumptionによるinstance集合の一致を示す。

共起とsandwichには、実行可能で健全なsymbolic subtype checkerを使う。`mergeCheck` は、二変数の共通unionまたはintersectionを両変数に代入した型が元の型以下になることを、任意の割当てについて認証する。`merge_instances_exact` は認証された統合の全instance保存を示す。`sandwichCheck` は置換対象に依存しない型への置換を同様に認証し、`sandwich_instances_exact` へ接続する。

実例は `α -> β -> (α | β)`、`(α & β) -> (α, β)`、`(α & int) -> (α | int)` を扱う。無関係な `α -> β` を共有変数へ統合すると `int -> str` のinstanceを失うことも証明し、その統合はcheckerが拒否する。

`simplifyAll` は有限の変数集合とscalar候補を走査して、単極除去・sandwich・共有変数統合を自動で行う。`simplifyAll_instances_exact` は任意の入力termに対する全instance一致である。checkerは安全な簡約の十分条件であり、すべての安全な統合を発見する完全な共起解析や、唯一の表示標準形を主張しない。対応範囲外のrecord tailは、該当する段階で元のtermを保持する。

## 10.21 入れ子の未知型と正則再帰型の完全な求解

### 10.21.1 有限の制約飽和

`NestedValueSolver` は、変数・base・`never`・`any`・pair・variant・record・arrowからなる有限の型node graphを入力にする。constructorの子は同じgraphのnodeを参照し、その内部にも未知変数や循環を置ける。arrowの二つのrowは、この層では固定したcarrierの値である。

solverはnode対のcacheを増やす。constructor比較を子の比較へ分解し、`L ≤ α` と `α ≤ U` から `L ≤ U` を伝播する。arrowでは入力の型と行の方向を反転する。recordでは先頭field優先を維持する。`FiniteHorn.saturate_exact` により、計算したcacheは独立な有限導出関係と一致し、`saturate_capacity` により対の追加数はnode数の二乗以下になる。呼出側のfuelや型深さの上限を用いない。

### 10.21.2 solverから独立した再帰値型

`RegularValueTypes.Layer` は有限のlattice式とconstructorを持ち、再帰参照をconstructorの子にだけ置く。有限stateのgraphで相互再帰する値型を表現する。値型のsubtypingは、すべての有限観察が既存の `StructuralBase.Subtype` を満たすこととして定義する。solverの成功やeffect行の最小解から定義しない。

`finite_conservative` は有限の型では元の部分型関係と完全に一致することを示す。`Derivation` は、直ちに使える仮定とconstructorを通過してから使える仮定を分離した循環的証明体系である。`Derivation.sound` はその健全性を全観察深さについて示し、裸の循環から `any ≤ never` を導くことを排除する。入力側と出力側それぞれの再帰について、一周期と二周期のgraphの同値も検証する。

### 10.21.3 成功からの実際の解構成

`RegularValueCoalescing.coalesceGraph` は、変数だけを辿る部分を有限のunion/intersectionへ展開し、constructorの子への再帰参照をgraphに残す。10.19.3の全解を表す式を各観察深さで使い、自由parameter graphは同じ深さで観察されるように組み込む。

`solve_instantiates_model` は、実際のsolverが成功すると、任意の自由parameterから元の全制約を満たすregular modelを構成できることを示す。型付けやモデル存在を前提に渡す必要はない。反変位置を含む再帰を、単調な最小不動点であると仮定する必要もない。

`coalesceGraph_retraction` は逆向きの構成である。元の任意のモデルをparameterに選ぶと、生成した全nodeが元の全nodeと相互部分型になる。`solve_models_exact` はこれを全モデルの同値へ、`solve_instances_exact` は任意の出力nodeとtargetに対する全instanceの同値へ接続する。scheme側のinstance条件には、元の不等式を満たすという残余条件がない。

`RegularNestedModels` は元のconstructorの意味とedgeの成立からモデルを独立に定義し、飽和が任意のregularモデルを保存することを証明する。したがって `solve_none_iff` は、solverの拒否とregular modelの不在を同値にできる。拒否を有限型の割当てだけへ限定しない。

### 10.21.4 推論入口と対象範囲

`RegularSchemeInference.infer` は元のgraph・制約・出力nodeから、失敗または自由parameterを持つschemeを返す。`infer_principal_exact` は、成功cacheを追加前提に要求せず、実際の呼出し結果の全instanceと元の独立な制約modelの全instanceを同値にする。`infer_none_iff` は解不存在に対応する。

`RegularValueCoalescingExamples` は、恒等関数適用と自己適用の実際のcache計算を、生成した解と全instanceの定理までつなぐ。関数入力の反変性や関数の出力内のpairから判明する矛盾については、再帰型を用いても解がないことを示す。`lean/RunRegularInference.lean` から通常のコード実行も試せる。

完成した対象は、固定されたrow比較の下での、有限の単相nested subtype graphである。自由parameterの各型自体は再帰してよい。source全体からのgraph抽出、rowの未知変数の同時求解、一般化とintrusion/T3の統合、`as` の最終表示、完全な表示簡約は、この定理と区別する。

## 10.22 元のprincipal formulaをsolverへ渡す正規化

`ConstraintNormalForm.normalise` は、元の `Inference.Formula` を有限の選択肢へ変換する。一つの `Clause` は有限個のfreshなcomputation slotと、型・rowの不等式の連言を持つ。conjunctionでは二つの局所slot集合を分離し、元のfree slotは共有する。存在量化は局所slotへ移し、disjunctionは両側の選択肢を保持する。

`normalise_exact` は任意の `Inference.Model` に対して元のformulaと正確に同値である。`closed_source_exact` は、元の閉式の `Typing` が、計算したclauseのいずれかに割当てを与え、最後の結果slotを元のresultと等しくすることと同値であると示す。lambda・application・value-restricted letを含む既存の全 `Inference.Expr` を対象にし、letの一般化側を削除しない。型と行は元のcomputation slotの組として保持する。

この正規化はatomの求解ではない。DNFを明示的に列挙するため、最悪では指数的に大きくなる。任意のclauseを10.21のgraphと行制約へ意味を保って下ろし、双方を解く接続が必要であり、normalizerだけでsourceの型推論が完成したとは主張しない。

## 10.23 元の型制約から主型スキームを構成する入口

`TypeConstraintGraph.compile` は、元の `TyTerm (Fin n)` の不等式列を有限の共有graphへ変換する。同じ型変数は同じnodeを参照し、制約中に現れない入力slotも保持する。左辺のunionと右辺のintersectionは既存の束の法則で分解する。constructor内部ではrigidな型項を要求し、recordのtailは固定されたspineに限る。対応しない項は型エラーではなく `unsupported` となる。

`TypeConstraintGraphEquivalence` はconstructorの実現を構文等号ではなく相互部分型で扱う。任意のsemantic realizerを元の型項の評価へ戻せること、共有入力の割当てを等号で保持すること、出力slotの全instanceを保つことを証明する。recordに要求する合同性は同じ有限field list内の値についてだけであり、未知tailへの合同性は仮定しない。

`RegularInferenceModel` は有限layerと有限の同時再帰blockから一つの型carrierを構成する。blockの内部参照は有限listの添字で表し、finite graphからの埋込みが範囲内に留まり、全観察を保存・反映することを示す。pair・arrow・recordなどのconstructorを組み立てても同じcarrierに収まり、coalescingの自由parameterもこのcarrier全体を動く。

`TypeConstraintInference.infer` はコンパイル、飽和、regular schemeの構成を実際に呼ぶ。返された `Scheme` はgraph・cache・入力参照を持ち、具体化時に元の不等式を再検査しない。`infer_correct` は成功したcompilerやcacheを追加前提に要求せず、実際の三分岐の意味を示す。対応範囲の検査が通ると、`infer_models_exact` と `infer_instances_exact` により元の全型割当てと全出力instanceが得られる。`infer_rejected_iff` は拒否とregular model不存在の同値である。

例は実際の型項の制約から、恒等関数、自己適用、双方向の再帰arrow equationを解く。反変入力とnested pairの矛盾は、正則再帰型でも解けないことを証明する。行はこの入口では固定した割当てであり、全sourceの推論入口とは区別する。

## 10.24 行の相関を残す求解と型graphとの接続

`RowFlowSchemes` は、空行・変数・joinからなるcoreの行不等式を扱う。右辺は変数または空行、左辺のjoinは分解できる。変数間の流れを辿り、空行以下に強制されるparameterだけを消し、その他のparameterを到達先のjoinへ残す。元の全行モデルとschemeの全具体化が、相互包含まで一致する。未拘束行をすべて空行へ決める構成ではない。

`NestedRowRequirements.solveRows` はsymbolic rowを持つ型graphをshapeだけで飽和させ、cache中の全constructor比較から必要な行不等式を回収する。arrow入力の行は反変方向、出力の行は共変方向である。明示されたsourceの行制約と合わせて行schemeを構成し、`solveRows_instantiates` は任意の自由parameterについて、同じcacheが実際の行比較の下でも成功することを示す。

`solveRows_models_exact_eq` は行包含の反対称性を明示した上で、元の行割当てをschemeから等号で回復する。これは集合行のような反対称なcarrierに適用できる。listの重複・順序まで同一になるという主張ではない。`TypeConstraintRowInstantiation.compile_instantiate` により、symbolicなcompiler出力に行を代入すると、最初からその行割当てでコンパイルした出力と一致する。

`ConstraintProblems.split` は正規化されたclauseから型制約と行制約の列を取り出す。値型と行は元と同じslot番号を共有する。`closed_source_problems_exact` は、計算したいずれかの問題の出力instanceが、元の閉式の `Typing` と同値であることを示す。型判断のsubsumptionにはcaptured polymorphic bindingも含める。この分割・行scheme・固定行での型solverの統合は10.26で扱う。

この行schemeの構文は `RowTerm` であり、operation head、保護、解除、handler residualを持つ一般の `RowExpr` の全解を消去したとは主張しない。既存の衛生性、負の差分、無限集合行の意味を変更しない。

## 10.25 record tailの意味論上の境界

**旧reference algebraについて証明済み。決定38により意味的合同性を持つモデルへ移行する。** 出典は10.5.1のrecord生成規則と、`StructuralBase` の構文的な `IsRecord` 条件である。章4.3のfirst-field-winsと幅部分型を変更する決定は行っていない。以下の反例は旧関係についての定理として保持し、新しいモデルについての反例とは扱わない。

`RecordTailBoundary` は次の閉record literalと二つの型を使う。行は純粋な `Unit` とし、effectには依存しない。

\[
e=\operatorname{record}(0,\operatorname{lit}(\mathrm{int}),\{\}),\qquad
P=\operatorname{record}(0,\mathrm{int},\{\}),\qquad
M=\operatorname{record}(0,\mathrm{int},\{\}\cup\bot).
\]

tailの `{} | never` と `{}` は相互部分型だが、前者は構文的なrecord spineではない。元の `Typing.record` はrestの型に `restType ≤ emptyRecord` を要求してその型を保持するため、`e` は `P` と `M` の両方へ型付けでき、両方が元のprincipal formulaのinstanceになる。一方で、現在の `Subtype.record` は両端に `IsRecord` を要求するので、`P ≤ M` も `M ≤ P` も成立しない。

`no_record_spine_represents_principal` は、特定の `P` に限らず、どのproper spine一つの上方閉包でもこのliteralの全instanceを表せないことを示す。これは制約式のprincipalityや一般solverの存在を否定するものではない。未知tailを同値なproper spineへ置換するだけでは、現在の意味を保存できないという境界である。

2026-11-06の決定38は、tailを含めてrecordの意味的合同性を持つモデルへ進む方を選んだ。checker・cut elimination・compilerの接続もそのモデルについて再証明する必要がある。`Typing.record` に構文条件を加えて既存instanceを落とす変更や、合同性を持たない旧モデルの単なる商を意味保存として扱う変更は行わない。新しい合同関係と保存定理の到達範囲は10.27に記す。

## 10.26 元の核の式からの主型推論の完成範囲

### 10.26.1 型と行を同時に解く

`JointConstraintInference.infer` は元の型・行不等式の対を入力にし、symbolicな型graphと行schemeを構成する。計算は具体的なrow carrierや意味論上の包含checkerに依存しない。結果の `Scheme` はsymbolic graph、飽和cache、入力参照、自由なrow式を保持する。具体化は任意の自由row parameterと任意のregular value parameterを受け取り、元の制約を再検査せずに型・行の割当てを構成する。

`infer_models_exact` は、反対称なrow join algebraについて、元の全型・行モデルと計算したschemeの全具体化を一致させる。元のrow割当てを等号で回復してから、同じrowsの下で値型のモデルを回復するので、入出力の型・行の相関を失わない。証明に使うclassicalなrow checkerは証明内部だけにあり、実際の `infer` や `Scheme.instantiate` はそれを呼ばない。

### 10.26.2 元の式からの実行と全instanceの一致

`SourcePrincipalInference.infer` は既存の閉じた `Inference.Expr` を受け取り、元の `Inference.principal` を生成し、正規化された各clauseをjoint solverへ渡す。成功した全alternativeを保持し、矛盾したalternativeだけを除く。元の値制限付きletの多相branchを単相branchへ置き換えない。一つでも未対応のalternativeが残れば、全体を `unsupported` と返す。

`SourceConstraintSupport.RecordFree` は部分式を含めてrecord構築だけを除外する。lambda・application・値制限付きlet・分岐・pair・fst/snd・field access・variant・emptyRecord・literal・変数を含む。`good_generate` は元の生成器に対する構造帰納で、scheme置換とcaptureを保つrenameを扱い、letの両branchに不変条件を示す。`closed_compiler_and_rows_supported` は正規化したすべてのclauseについて、型compilerの成功と行stageの非unsupportedを導く。可解性は前提にしない。

したがってこの構文範囲では、`recordFree_instances_exact` が次の形で閉じる。

\[
\operatorname{Typing}(e,T!\epsilon)
\iff
\exists S\in\operatorname{infer}(e),\ \exists\vec p,\vec\rho,\quad
  \llbracket S\rrbracket(\vec p,\vec\rho)\le(T,\epsilon).
\]

右辺は計算された有限familyの自由parameterによる具体化とsubsumptionだけで、元の制約を満たすという残余条件を持たない。左辺は `RegularInferenceModel` における元の独立な `Typing` である。任意のtargetを量化し、成功cache・途中の型・型付け導出・モデル存在・fuelを呼出側から渡さない。`recordFree_principal_formula_exact` は同じ結論を元のprincipal formulaへ接続する。

`recordFree_rejected_iff` は拒否と元の型付け不存在を同値にする。未対応と拒否を混同せず、`recordFree_ne_unsupported` はこの構文範囲で未対応の返り値自体が起きないことを示す。制約の正規化とcompilerは有限構文に対する再帰、飽和は有限node対の新規追加数に基づいて停止する。再帰型の深さを有限に打ち切る停止ではない。

### 10.26.3 `any` と共有行を持つ具体例

`SourceInferenceExamples` は元の `Typing` から独立に、恒等関数と整数定数関数の全結果を特徴付け、その結果を実際の `SourcePrincipalInference.infer` に接続する。以下の `! R` は説明用のcomputation行の記法であり、surface構文ではない。

\[
\lambda x.x:\quad \forall A,R.\ (A!R)\to(A!R),
\qquad
\lambda x.1:\quad \forall R.\ (\mathrm{any}!R)\to(\mathrm{int}!\varnothing).
\]

恒等関数では型・行の両parameterを共有する。定数関数では値の入力型だけが負の位置にあるため `any` に消去できるが、入力computationの行は自由な `R` として残る。`infer_identity_instances_exact` と `infer_constant_int_instances_exact` は、計算されたschemeの全instanceがこの簡潔な型の族と一致する定理である。内部blockをその文字列へ書き換えるpretty printerを実装したという主張ではない。

### 10.26.4 符号付き行と全言語への残りの接続

`SignedSourceInference` は上のsource主型性を、既存の `RecursiveRows.SetRow` へ具体化する。empty・join・包含は既存のeffect algebraと同じで、`rowView` は恒等decodeである。自由なrow parameterには保護済み出現、負の差分、無限supportを持つ集合行も入る。有限のscope interfaceに対して、符号付き重みの大きさやrowのsupportを制限しない。

完成したのは、record構築を除く既存core ASTの、値型とcore rowの主型推論である。10.25の一般recordモデル、operation・handler・保護・解除を生成するeffect ASTの一つの求解入口、再帰SCC・T3観測・注釈・role/cast・EOF判定との統合、surfaceからのelaboration、`as`を含む表示標準形は別の義務として残る。各層に既存の定理があることを、それらを統合した全言語の推論器の完成とは扱わない。

このreference solverは証明の対象として明示的なDNFと有限listを使う。letの選択肢の展開は最悪で指数的になり得る。停止と主型性を、production向けの時間・メモリ性能の保証とは区別する。`lean/RunSourceInference.lean` は元の式からの実行と具体化を確認する入口である。

## 10.27 意味的record合同性への移行

出典は章4.3とhandoffの決定38（2026-11-06）である。以下は移行の証明状況であり、一般tailの新しい部分型規則を決定する節ではない。10.26の実行入口は旧reference modelのままで、`SourcePrincipalInference.recordFree_instances_exact` の `RecordFree` 前提は残る。

### 10.27.1 最小合同閉包と意味的な商

`SemanticRecords.Subtype` は、旧モデルの構造・束の規則を新関係の下で閉じ、recordのheadと任意tailについて相互部分型の置き換えを認める**中間関係**である。`record_congr` に `IsRecord` の前提はない。`old_subtype` は旧関係の任意の導出を保存し、`Subtype.minimal` と `subtype_iff_all_closed` は、明示した規則からなる最小閉包であることを示す。任意tailに対する一方向の共変性、constructorの分配等式、`record(l,A,never) = never` はこの追加規則に含めない。

`boundary_pair_equivalent` は、任意の行関係・label・field型について `record(l,A,{})` と `record(l,A,{} | never)` の相互部分型を示す。新関係では後者も空recordへ幅包含できる。10.25の否定定理は旧関係に留め、主張や期待値を書き換えて消さない。

`SemanticRecordQuotient.QTy` はこの新関係の相互部分型による商である。任意の行関係で、`mk_eq_mk_iff` はraw型の相互部分型と商での等号を一致させ、`eq_iff_mutual_subtype` は商の部分型を反対称にする。recordを含むconstructorはwell-definedである。arrowと `Inference.Model` の構成には行関係の反射性を要求する。`boundary_pair_equal` は上の二つのrecordを実際に等しくし、`int_ne_str` は基本型を潰さないことを示す。合同性を持たない旧関係をそのまま商にしてはいない。

### 10.27.2 元のFormula・型付けの保存と反映

`Inference.ModelMap` は全型constructor・行演算・型と行の包含を保存する写像である。`formula_preserved` は任意の元Formulaとその任意の充足割当てを写し、存在slotのwitnessも値型と行を組にして保持する。型・行の包含の反映と計算型全体の全射性も仮定すると、`formula_exact` と `closed_typing_exact` が双方向の一致を与える。

`SemanticRecordInference.old_typing_preserved` は、旧有限モデルの任意の環境・元core式・結果計算型の型付けを新しい合同関係へ保存する。`mapEnvironment` は捕捉した多相束縛と明示署名も写す。`Typing.record` の規則に構文条件は追加せず、値制限付きletの両経路も除外しない。`SemanticRecordQuotientInference.formula_exact` と `closed_typing_exact` は、行関係の反射性の下で、任意のraw割当て・Formula、任意の閉core式・raw結果についてraw合同モデルと商モデルの同値を与える。`old_closed_typing_preserved` は旧有限モデルから商までを合成する。旧関係と合同閉包の逆向き保存を主張する定理ではない。

rawと商の `literal_typing_iff`・`literal_principal_formula_iff` は、任意のrow join algebra、label `l`、基本型 `b`、結果計算型 `C` について、元のliteral `record(l,lit(b),{})` の型付け／principal formulaの充足が、有限型 `record(l,b,{})` と空行から `C` への通常のsubsumptionと同値であることを示す。推論されたtailを構文的に制限せず、rowの反対称性も要求しない。

### 10.27.3 有限ground checker・cut elimination・商の等号判定

`SemanticRecordAtoms` は外側のunion/intersectionを構造atom間の比較へ分離し、`equivalent_atomic_witness` は必要な代表atomが元の有限atom列内にあることを示す。`SemanticRecordViews` と `SemanticRecordAtomNormal` はproper record viewとatom pathの形を特徴付ける。`SemanticRecordLatticeCheck` は既存 `StructuralDecisions` の有限束checkerへ接続する。

`SemanticRecordChecker.check rows A B` は型のconstructor depthから必要な層数を計算する全域関数である。任意の `Row`、`DecidableEq Row`、関係 `leRow`、Boolean関数 `rows` について、

- 任意の `r, s` で `rows r s = true ↔ leRow r s`、
- `leRow` の反射性と推移性、

を仮定すると、任意の有限raw型 `A, B` について `check_true_iff` は計算結果 `true` と `SemanticRecords.Subtype leRow A B` を同値にし、`check_false_iff` は `false` とその否定を同値にする。`cut_elimination` は宣言的導出と、前の構造depth層の**計算された**atom比較を前提に持つcut-free判断を一致させる。atomの意味的oracle・探索候補・外部fuelを前提にしない。row checkerの正確性は明示した前提として残る。

同じ前提の下で `SemanticRecordQuotientDecisions.raw_check_congr` は代表元不変性を示し、`Quotient.lift₂` により商型上の実行可能な `check` と `equal` を構成する。任意の商型 `A, B` について、`check_true_iff` は商の部分型と、`equal_true_iff` はLeanの実際の等号 `A = B` と一致する。標準形やcanonical代表元は構成していない。

これらが判定する関係は10.27.1の最小合同閉包に厳密に限る。任意tailの追加規則を含む最終的な関係の完全checkerを得たとは扱わない。

### 10.27.4 全coreから未知tailを保持するgraphへの完全なcompiler

`RecordConstraintSupport.good_generate` は元のすべてのcore constructor、scheme置換・rename・capture、letの両branchにpolarな生成条件を示す。`prepare` は下側unionを分割する。任意のmodelでunionがjoinなら、`prepare_exact` は任意の元の型・row割当ての充足を双方向に保つ。生成されるopen recordは型制約の下側rootに限られ、上側はrigidなdemand文法に従う。この事実に可解性は必要ない。

`OpenRecordConstraintGraph.compile` は任意の `ConstraintProblems.Problem m` を有限graphにする全域関数である。record nodeは `.recordExtend label headRef tailRef` としてheadとtailを両方保持し、union/intersection nodeも残す。未使用を含む元input slot、arrow内部のrow term、独立なrow制約は元の番号を保つ。

任意のmodel・problem・型割当て・row割当てについて、`compile_assignment_exact` は元制約の充足と、元inputへの制限が同じであるgraph解の存在を同値にする。`compile_retraction` はconstructorを実現する任意のgraph割当てを制限して再拡張すると全nodeで元に戻ることを示す。`compile_instances_exact` は任意の出力slot・結果計算型で全instanceを一致させる。これらのgraph変換定理自体にはrecord法則も型・rowのpreorder性も必要ない。

`compileSource e` は実際に `principal → normalise → prepare → compile` を実行する。任意のmodelについて、unionがjoin、型・rowの包含が反射的・推移的なら、任意の元core式 `e` と任意の結果計算型 `C` に対して、

```text
SourceInstance model (compileSource e) C ↔ Typing model [] e C
```

が `compileSource_instances_exact` により成立する。record構築を含み、`RecordFree`・compiler成功・解存在を前提にしない。`SemanticRecordQuotientInference.compiled_typing_exact` は任意のrow join algebraでこの同値を商モデルへ具体化する。**右辺と同じ解を持つgraphを計算する証明であり、graphの残余制約を消去した自由parameterの主型schemeを計算する証明ではない。**

### 10.27.5 仕様の確認点と残る義務

章4.3の幅部分型とfield利用は既存の義務である。最小合同閉包は任意のadmissible tailを持つrecordについて、そのhead/幅をすべて証明できる最終モデルではない。例えば `record(l,A,never) ≤ {}` はこの中間関係では導出できない。checkerのこの否定結果を、言語仕様での型エラーと解釈しない。

この時点の確認点は、一般の `R ≤ S ≤ {}` から `record(l,A,R) ≤ record(l,A,S)` を採用するか、というものだった。決定39は要求側 `S` がrigidな場合に限定する回答であり、その規則の証明状況を10.28に記す。`S = {}` に対応するhead/幅を再決定する問いではない。unionの分配等式やbottomでのstrictnessも、この回答だけで決まったものとしない。

`SemanticRecordVarianceBoundary.local_laws_without_tail_covariance` は、同値置換・proper record・head/幅・既知field存在・同じfieldの冪等性・異なるfieldの交換という明示した局所法則を満たしながら、一般tail共変性を満たさない有限のfield存在代数の存在を証明する。具体例は `R = ↑{y}`、`S = ↑{y} ∪ ↑{z}` に同じ `x` を加えるもの。payloadの型・実行・inhabited性の保存は含まないため、**Yulang全仕様からの独立性やsourceプログラムの型付け不能を示す反例ではない。**

**この段階からの残る義務:** head/幅を満たす決定39の限定規則とchecker/cutは10.28で更新する。独立な正則再帰値型モデルとcoalescingへの接続、新しいgraphの実際の制約求解、record構築を含む全coreの自由parameter scheme・全instance主型性・拒否完全性は引き続き残る。`SourcePrincipalInference` の `RecordFree` 制限はまだ外していない。effectのoperation/handler/保護/解除、再帰SCCと全注釈多相再帰、注釈の公開値型と一般化直前のeffect検査、role/cast/EOFは既存の個別定理のままで、この入口との統合は未完。表示の標準形・`as`の最終表示・一般の禁止点付きgraph到達は今回の変更に含めない。

## 10.28 rigidな要求tailへの共変性

出典は章4.3とhandoffの決定39（2026-11-06）である。10.27の最小合同閉包の定理を歴史的に保持し、`RigidSemanticRecords.Subtype` に限定された規則を追加する。従来の束・構造・合同規則に加えるのは、次の一つである。

```text
IsRecord S → R ≤ S → record(l,A,R) ≤ record(l,A,S)
```

`semantic_subtype` は決定38の任意の導出を保存し、`Subtype.minimal` は明示した規則の最小閉包を特徴付ける。一般の要求tailへの共変性、分配等式、bottom strictnessは追加していない。`record_head` と `record_width` は任意の行関係・label・field型・tail `R` について、`R ≤ {}` だけを前提にhead利用と `{}` への幅部分型を導く。`record_never_below_empty` は前回のwidth境界を解消する。

### 10.28.1 hidden fieldを比較しない必要十分条件

`RigidRecordFields.erase l P` は要求型 `P` のspineからlabel `l` のfieldをすべて除く。任意の `Row`、任意の行関係、label `l`、型 `A,R,P` について、`IsRecord P` を仮定すると、`RigidRecordDemands.record_mask_exact` が

```text
record(l,A,R) ≤ P
  ↔ (∀B, P.lookup l = some B → A ≤ B) ∧ R ≤ erase l P
```

を示す。供給側のtailはunion/intersection等を含めて任意で、行法則・判定可能性・可解性を前提にしない。`Fits` の宣言的導出に沿った反変単調性で必要性を、rigid-tail規則とproper record規則で十分性を示す。この範囲では、隠れたfieldを比較しないことによる完全性の欠落はない。

### 10.28.2 完全checker・cut・商モデル

`RigidRecordChecker.check` は入力のconstructor depthから層数を内算する。任意の `Row`、`DecidableEq Row`、行関係 `leRow` とBoolean row checker `rows` について、`rows r s = true ↔ leRow r s` が全行で成立し、`leRow` が反射的・推移的なら、任意の有限raw型 `A,B` に対する成功・失敗が新関係の成立・不成立と同値になる。`cut_elimination` は前層の実際のatom比較を前提に持つcut-free判断との同値であり、`StructuralDecisions` に接続する。row checker以外の意味的比較oracleや外部fuelは要求しない。

`checkDemand rows A P (rigid : IsRecord P)` は要求側の制限を明示する別入口で、同じrow前提の下で成功・失敗が完全である。`checkDemand_hidden_payload` は、任意のBoolean row checkerについて、外側の同名fieldに隠れたpayloadを変更しても計算結果が等しいことを示す。visible fieldのpayload内部は再帰的な比較に委ねるため、その内部にopaqueな要求型を許す場合には次節の境界が残る。

`RigidRecordQuotient` は新関係の相互部分型による商で、`Rigid` はproper代表元の存在として定義する。要求tailがこの意味でrigidなら、`record_tail_mono` が限定共変性を商へ持ち上げる。前段の商からの `fromCongruence` は全旧等式を保存する。`RigidRecordQuotientDecisions` は上のrow前提で代表元不変性・商の順序判定・実際の等号判定を与える。標準形を選ぶ手続きではない。

`RigidRecordInference.old_typing_preserved` は旧有限モデルの任意環境・式・結果の型付けを保存する。行関係の反射性の下で、`RigidRecordQuotientInference` は元Formulaと全閉式Typingのraw/商同値、前回の合同モデルとその商の全閉式instance保存を示す。任意のrow join algebra・元core式・結果計算型について、`compiled_typing_exact` は実際の `OpenRecordConstraintGraph.compileSource` の全instanceと新商モデルのTypingを同値にする。元の `Typing.record` を狭めず、残余graph制約が求解済みだとも主張しない。

### 10.28.3 rigid要求での先勝ちとopaqueな要求の境界

`RigidRecordOpaqueBoundary.hidden_field_rigid_comparison` は、任意の行関係・label `l`・型 `A,B,R` と全rigid型 `P` について、

```text
record(l,A,record(l,B,R)) ≤ P ↔ record(l,A,R) ≤ P
```

を示す。tailのadmissibilityも追加前提にしない。一方、今回の最小関係では、rigidな要求への全比較が一致しても、任意の型同士の相互部分型になるとは限らない。

`OpaqueTail R` は、どのproper spineとも相互部分型でないことを表す。`opaque_comparison_iff` は、任意の行関係・label・head型・供給tailと、opaqueな要求tail `S` について、

```text
record(l,A,R) ≤ record(l,B,S) ↔ A ≃ B ∧ R ≃ S
```

を示す。したがって、この場合の比較では内側の隠れたfieldも区別される。具体的に `R = never` と `R = {y:int} | {z:str}` について、`record(x,A,record(x,B,R))` と `record(x,A,R)` はともに `{}` の部分型だが、どちらも他方の部分型でない。unionについては構文的にnonrigidというだけでなく、properな同値代表元が存在しないことまで証明した。これは参照関係の境界であり、sourceプログラムの拒否や一般solverの不可能性ではない。任意opaque型でhidden fieldを同一視する法則を、この証明から追加しない。

前回の局所field存在代数について、`RigidRecordVarianceBoundary.local_laws_rigid_covariant` は任意の `LocalRecordLaws` を満たす操作がprincipalな要求tailへの共変性を持つことを示す。旧反例の右辺unionはnonprincipalである。したがって前回の具体例は決定39の反例ではない。この確認も、payload・実行を含むYulang全体の意味モデルを構成したという主張ではない。

`RigidRecordSourceBoundary` はこのunion-tailの境界を元の式へ接続する。異なるlabelを `x=0,y=1,z=2` とし、核ASTを

```text
record x (lit int) (record x (lit str) (record y (lit int) emptyRecord))
```

とする。任意のrow join algebraに対して、`source_has_incomparable_instances` と `principal_has_both_instances` は、`R={y:int}|{z:str}` を使った `record(x,int,record(x,str,R))` と `record(x,int,R)` の両方が、空行で同じ式の元Typing・principal formulaのinstanceになることを示す。前者は内側の `y` のrecordを `R` に広げ、後者は内側の `x` のrecord全体を `R` に広げて得られる。`same_rigid_results` は、任意のrigid要求型・任意の結果行に対して二つの結果計算型の包含検査が一致することを示す。これもsource拒否の例ではない。

4.3のfirst-field-winsと決定38は既存の規則である。上の非比較は、今回明示した規則のみの最小形式関係についての境界を示す。この別型性を仕様全体の確定した意味とは扱わず、nonrigidな推論tailに隠れた同名fieldにも型等価としての消去を適用するかは、追加の等式を実装する前の確認事項とする。同じ式に二つのinstanceがあること自体は、両instanceが等価である根拠にはしない。

### 10.28.4 recordを含むデータ式の実際の求解

`RigidRecordValueInference.infer` は元の `Inference.Expr` を入力とし、再帰的な `Data` 構文（literal・emptyRecord・pair・variant・record構築）から有限のplanを構成する。不正なrecord tailも `Data` の範囲に含める。`infer_unsupported_iff` は、任意の式について `unsupported` と `¬ Data` の同値を示す。対応範囲では成功したplanか、型付け不可能を表す `rejected` を返す。

planはrecordごとに2個の自由な値型parameterを導入する。子のschemeの値型が `H,T` なら、評価結果は

```text
record(l, H | α, (T | β) & {})
```

である。受理されたtailのplanは、任意の子parameterで `T ≤ {}` を満たすため、すべての `α,β` が有効な型付けを構成する。元の任意の型付けで実際に用いたhead `A` とtail `R` に対し、`H ≤ A`、`T ≤ R ≤ {}` から `H | A ≃ A`、`(T | R) & {} ≃ R` を導く。record合同性により、その元の型付けが使った構築型を回収する。型付けの導出やその中間型は完全性の証明に使い、推論関数の引数にはしない。一般のopaque要求tailへの共変性は使わない。

任意の `Row` と `RowFlowSchemes.Algebra Row`、任意の式 `e` と前提 `Data e`、任意の結果計算型 `C` に対して、`infer_instances_exact` は

```text
(infer e).Instance algebra C ↔ Typing (model algebra) [] e C
```

を示す。成功側の `Instance` は、ある自由parameter tuple `p` が存在して `(plan.evaluate p, empty) ≤ C` となることだけである。残余制約・graphのモデル・可解性・成功cache・外部fuelは前提にない。`infer_plan_correct` がplanの適格性と元式との対応を内部で保証する。`infer_principal_formula_exact` は同じ結果を元のprincipal formulaへ接続する。同じ量化範囲で `infer_rejected_iff` は、実際の拒否と `¬ ∃ C, Typing [] e C` の同値を示す。

`RigidRecordValueQuotient` はこのplanを決定39の商モデルへ移す。自由parameterは商の値型全体を動き、`infer_instances_exact`・`infer_principal_formula_exact`・`infer_rejected_iff` が商の任意の結果計算型について成立する。`infer_plan_sound` は、任意の式・実際に返されたplan・任意の商parameter tupleに対して、planの評価結果がその元式の型になることを示す。`inferred_boundary_has_both_instances` は10.28.3の同じ式に対するopaqueな両結果を実際のschemeが保持することを示し、`boundary_quotient_types_distinct` はその二型が現在の商でも異なることを示す。

この断片では正則再帰値型を導入せず、値型の量化範囲は有限raw型とその商である。行は任意の上記代数でよく、有限性やBoolean包含checkerは仮定しない。sourceに変数・一般lambda/application・let・field access・effect式は含めない。`RunRigidRecordInference.lean` は受理、scalar/pair/variant tailの拒否、構文範囲外の区別、parameter個数を実際の関数で確認する。旧solverの期待値は変更しない。

### 10.28.5 引数recordを拡張する関数族

`RigidRecordFunctionScheme.scheme l b : CompTerm (Fin 4)` は、元の核式 `lam (record l (lit b) (var 0))` に対する有限descriptorを構成する。任意の自由値型 `α,β,γ` と自由行 `ρ` に対し、

```text
I = α & {}
H = b | β
T = (I | γ) & {}
(I ! ρ) -> (record(l,H,T) ! ρ)     外側の行はempty
```

を評価結果とする。`instantiate_eq_eval` はこの計算とdescriptorの評価の一致を示す。`instantiate_sound` は任意のrow join algebra・label・base・全parameter tupleについて、元の関数の型付けを構成する。

`instances_exact` と `principal_formula_exact` は、任意の同じ行代数・label・base・結果計算型 `C` について、descriptorの自由parameter instanceとsubsumptionの族を、元Typingと元principal formulaの全結果にそれぞれ一致させる。成功条件・parameterへの制約は前提にない。完全性の証明では元の導出から引数型・head・tail・入力行を回収し、上の束によるretractionを使う。入力行 `ρ` は出力行でも共有し、それより広い元の出力行はarrowの通常の部分型規則で保持する。値の入力を独立な `any` へ消して相関を失う簡約は行わない。

`RigidRecordFunctionQuotient.instances_exact` と `principal_formula_exact` は同じ定理を商の任意の結果計算型へ移し、`instantiate_sound` は任意の商parameter tupleに対する型付けを示す。これはこの関数族の全instance主型性であり、任意のsource関数を推論するdispatcherを追加したものではない。値型carrierは引き続き有限raw型とその商である。

**残る義務:** opaqueな型同士の同一視とhidden fieldの扱い、独立な正則再帰値型モデル・coalescing、新graphの一般の制約求解、全coreの自由parameter scheme・全instance主型性・拒否完全性への接続。10.28.4のデータ構文と10.28.5の関数族は閉じたが、`SourcePrincipalInference` の `RecordFree` 制限は残る。effect式・再帰SCC・全注釈多相再帰・注釈確定・role/cast/EOFの統合、および表示標準形・`as`・一般の禁止点付き到達は引き続き未完である。


## 10.29 決定40：隠れたfieldの型上の消去

**状態:** 4.3と引き継ぎ決定40（2026-11-06）の形式化。言語規則の追加決定ではない。

`ShadowSemanticRecords.Subtype` は10.28の関係の規則を保持し、任意のraw型
`A,B,R` について次の両方向を加えた最小の関係である。

```text
record(l,A,record(l,B,R)) ≃ record(l,A,R)
```

`R` がrigid・admissibleであることは前提にしない。`Subtype.minimal` はこの
閉包の最小性を、`rigid_subtype` は以前の任意の比較の保存を示す。
`ShadowRecordQuotient.shadow` は任意の商型での等号を示す。
head/tail合同性、束の法則、rigid要求への共変性は保持し、一般tailへの
共変性・分配則は追加しない。`int_not_str` はscalarの区別が保たれることを示す。

`ShadowRecordInference.old_typing_preserved` は旧有限モデルの任意の環境・式・結果の
型付けを保存する。`rigid_closed_typing_preserved` と商版の
`rigid_quotient_typing_preserved` は決定39の全閉core instanceを保存する。
`ShadowRecordQuotientInference.formula_exact` はrawモデルと商モデルの任意の元Formulaの
全解を双方向に一致させる。`compiled_typing_exact` は任意のrow join algebra・
任意の元core式・任意の結果について、実際の `compileSource` が返したgraphの
instanceと新商モデルでの元 `Typing` を一致させる。graphの `Models` 条件は残る。

`ShadowRecordExamples.source_has_equal_instances` は10.28.3の元式を変更せず、
二つの型付けを保持して、その結果商型が等しいことを証明する。
`shadow_left_iff`・`shadow_right_iff` は任意の比較相手に対して消去前後を置換できる
ことを示す。以前の `opaque_comparison_iff`・`source_has_incomparable_instances` は
決定39の関係についての歴史的な定理として保持し、最新仕様の非比較とは扱わない。

**残る義務:** 未知tailを含む一般graphの求解、全coreの自由parameter主型性・拒否完全性、
open-tail graphの正則coalescing。有限ground checker・cut elimination・商等号判定は10.29.2、
正則モデル自体の接続とrecord要求の正確な分解は10.32で閉じた。
制約生成の正確性を、残余制約のない全core推論算法の完成とは扱わない。


### 10.29.1 同じ実行可能算法の全instance主型性

`ShadowRecordValueInference` は既存の `RigidRecordValueInference.infer` と `Plan` を変更せず、
新関係の型付けについて `infer_complete`・`infer_instances_exact`・`infer_rejected_iff` を証明する。
任意のrow join algebra・任意の `Data e`・任意の結果 `C` が量化範囲である。
成功側は有限の自由parameter tupleと通常のsubsumptionだけを使い、parameterへの残余制約、
graphの解、型付け導出、外部fuelは算法への入力にしない。完全性は新関係の元Typingから
parameterを回収するので、以前のinstanceの保存より強い。

`ShadowRecordValueQuotient` は商型全体を自由parameterの値域として同じ一致を証明する。
`infer_plan_sound` は実際に返ったplanの任意の商parameter tupleが元式の型付けを与えることを示す。
`inferred_boundary_instances_equal` は以前のopaqueな二つの結果をschemeが保持し、型等号で一致させる。
対象構文は10.28.4と同じで、一般lambda/application・let・effect式・正則再帰値型を含めない。

### 10.29.2 有限ground型の完全checkerと商の実等号判定

`ShadowRecordHeadViews.headView` は、tail全体が旧関係で相互部分型になる同名record atomを、
入力型の有限なouter atomから探す。候補の残りtailは元のconstructor depthより真に小さい。
意味的にproperなtailは保持し、それ以外で見つかった同名headだけを `strip` が除く。
`headView_complete` と `headView_tails_equivalent` は、必要なheadを探せることと選択結果の
旧等価性を示す。union/intersectionの各枝へ消去を配る操作は導入しない。

`ShadowRecordNormalization.normalize` は、このsmart constructorを型全体へ構造再帰で適用する。
`smartRecord_shadow` は追加した等式、`smartRecord_rigid_comparison` と
`smartRecord_tail_mono` はrigid要求の比較と共変性を保持する。
`normalize_equivalent` は元の型との新関係での等価を、`normalize_subtype` は新関係の
全規則から正規化後の旧関係への保存を示す。したがって任意の有限型 `A,B` について

```text
RigidSemanticRecords.Subtype (normalize A) (normalize B)
  ↔ ShadowSemanticRecords.Subtype A B
```

が成立する（`normalize_exact`）。前提は `DecidableEq Row`、正確なBoolean行checkerと
行関係の反射性・推移性で、以前のground checkerと同じである。

`ShadowRecordChecker.check` は正規化後の旧checkerを実行する。
`check_true_iff`・`check_false_iff` は新しい最小関係の成立・不成立と実判定を一致させる。
`cut_elimination` は計算済みnormal formsに対する既存のcut-free `Comparison` との同値で、
構造atomの前提は実際の前層Boolean比較である。意味的oracle、外部fuel、成功cache、
未知の中間型の推測は入力にしない。

`ShadowRecordQuotientDecisions` は代表元不変性から比較を商へ降ろす。
`equal_true_iff` の右辺は実際の商型の等号であり、`decideEq` もこのBoolean比較から構成する。
canonicalな表示文字列や正則再帰型の判定は対象外である。
`RunShadowRecordCheck.lean` はopaqueな二型の双方向比較、束の法則で隠れた重複の露出、
関数・variant・pair内部の正規化、visible payloadの不一致を実行する。
追加していない枝ごとの消去は、この最小関係の性質として別に検査し、言語全体の拒否とは扱わない。

## 10.30 決定41：handler armの許可検査と実際のcapture

**状態:** 5.5・T2・引き継ぎ決定41（2026-11-06）の形式化。

`HandlerPermissions.check permission arms` は全armのkeyがincoming actionの許可maskに
含まれるかを有限に検査し、`diagnostics` は不許可keyの一覧を返す。
`diagnostic_iff_unreachable` は、あるkeyが診断されることと、そのkeyがarm一覧にあり、
そのkeyを持つ任意のincoming occurrenceが境界後に捕捉されないことを同値にする。
既存の重みには任意の符号付き整数を許す。境界は `FreshBoundaries` のfresh座標を実際に
割り当てて構成し、古い座標の`−1`で新しい保護が相殺されることを防ぐ。

`discard_denied_arms`・`denied_arm_bodies_irrelevant` は任意のincoming request treeについて、
不許可armの削除・本体変更が実際の `Directed.Computation.shallowHandle` の結果を変えないことを示す。
`permitted_request_dispatches` は許可されたmatching keyで既存重みがすべて0なら実際のarmを呼び、
`old_nonzero_request_forwarded` は既存の正負の重みが残れば許可keyでもforwardすると示す。
`permitted_resume_is_original` は再開時にhandlerを再設置しないshallowの継続を保持する。

`checkedHandleIncoming` は、許可検査に成功した場合だけこの実行へ進み、失敗時は非空の
診断一覧を返す。成功・拒否の必要十分条件と、行のresidualとの一致も証明した。
検査対象はその注釈付きincoming actionの境界契約であり、handler arm内で局所的に
発生するeffectへ同じmaskを適用する規則ではない。source全体のelaboration、注釈からの
mask抽出、mixed-origin actionの許可推論、全言語の型安全性はこの定理の対象外である。


## 10.31 元core式の型付け・データ推論から実行安全性へ

**状態:** 既存の元AST・Typingと4.3/決定40のrecord規則に対する実行接続。

`SourceDataRuntime.eval` は元の `Inference.Expr` と値環境を入力とする全域関数である。
literal・変数・pair/射影・record/field・variant・非再帰letを評価し、未束縛変数、
非pairへの射影、非recordのtail、欠けたfieldはそれぞれ独立にエラーを返す。
record構築では両式を評価した後に古い同名fieldを保存データから除く。
`Fields.insert_shadow` はlookupだけでなく保存値そのものについての等号である。

`DataTypeSemantics.Holds` は有限値と型の適合を定義する。recordのtailには隠れたlabelの
maskを渡すが、headやpair/variantのpayloadではmaskをリセットする。
`record_shadow` は任意のtail・mask・値について決定40の等式がこの値意味を保つことを示す。
`ShadowDataSafety.subtype_preserves` は新しい部分型の全規則について意味保存を証明する。
これは一方向のsoundnessで、意味的集合包含による部分型の完全な特徴付けではない。

`SourceDataSafety.typing_evaluates` は上の対応構文にある任意の元式・型環境・適合する値環境・
結果型に対し、独立な元Typingから評価成功と返り値の型適合を導く。
多相letは右辺の一回評価値を固定し、別instanceの型付けから得られる評価値を決定性で
同一視する。単相letも右辺を評価してからその値を格納する。
shape certificate・intrinsically typed AST・評価成功・部分式のruntime安全性は前提にしない。

`ShadowDataSafety.quotient_typing_evaluates` と `principal_evaluates` は、任意の行join algebra・
対応する任意の元閉式・商の任意の結果型について、この保証を決定40の商と元principal formulaへ移す。
商の値意味 `QuotientHolds` は部分型の意味保存から代表元に依存しない。

`ShadowDataSafety.inferred_evaluates` は任意の元式・実際に返されたplanについて、
`infer e = inferred plan` だけから次を導く。

```text
∃ v, eval [] e = ok v ∧
  ∀ p : plan.Parameters QTy, QuotientHolds (plan.evalWith p) visible v
```

自由parameterへの残余制約はない。`instance_evaluates` は最後のsubsumptionを含む
全instanceを扱う。`inferred_no_error` はこの実際の評価器のすべてのエラー結果を除く。
推論成功からの入口はdata構文、元Typingからの入口は変数・let・field・射影を含む断片であり、
二つの射程を同一視しない。

**対象外:** literalの具体的payload、一般lambda/application・branch・effect・再帰sourceの実行、
Rust runtime、parserから核へのelaboration、全言語のpreservation/progress・実行停止。
`SourcePrincipalInference` の正則再帰型を扱うsource solverから、現在のshape解決済みの
高階実行モデルへの全域elaborationも未接続である。型推論の停止とprogram実行の停止は別の義務である。

`ShadowRecordFunctionScheme`・`ShadowRecordFunctionQuotient` は10.28.5の同じ有限descriptorと
自由parameterを使い、決定40のraw/商モデルで全instance主型性を再証明する。
その対象は明示したopen-record拡張関数族であり、上の第一階評価器へ関数を追加するものではない。

## 10.32 決定40の要求分解と正則モデルへの接続

**状態:** 10.29の有限関係、既存の正則有限観測モデル、元coreの制約生成に関する証明。
新しい言語規則や構文の決定を追加しない。

### 10.32.1 rigid要求の必要十分条件

`ShadowRecordDemands.record_mask_exact` は、任意のraw供給型 `A,R` とrigidな要求 `P` について、
決定40の関係で次を証明する。

```text
record(l,A,R) ≤ P
  ↔ (∀ B, lookup(P,l)=some(B) → A≤B) ∧ R≤erase(l,P)
```

`Fits` のpayload比較も新しい関係を使う。必要性は全Subtype規則への帰納法であり、
`shadowErase` と `shadowInsert` の両方を扱う。先頭fieldを処理した要求ではそのlabelが消えており、
二度目の消去は同じ要求になるため、隠れたpayloadの比較を加える必要がない。
十分性はrigid要求へのtail共変性と既存record規則から導く。
供給tailの形、行のpreorder、部分型の決定可能性は前提にしない。

### 10.32.2 全元coreが生成するsingleton要求

`SingletonRecordDemands.good_generate` は元の `Inference.generate` に対する構造帰納で、
要求型に現れる明示的なrecordがsingleton spineであることを示す。
payload内の関数・pair・variant・recordや未知slotは許し、生成側の最外recordだけは
元のhead/tail slotを保持する。lambda・application・値制限付きletの両分岐を含む。

rename、grammarを保つscheme置換、normalise、clauseのpackとsplit、既存のpolar prepareまで
この性質を保存する。`closed_prepared_polar` は全閉core式について環境前提を内部で満たす。
`RecordFree`、型付け、解存在、solver成功は仮定しない。
任意の外部schemeには強めた `GoodEnv` が必要であり、旧finite-spine前提だけでは足りないことを
`older_goodEnv_insufficient` が示す。これは閉式の言語構文を新たに制限するものではない。

`SingletonRecordGraph.compileSource_upper_grammar` と `compileSource_proper_subterm` は、
実際のcompiler出力の要求上端とconstructorのproper subtermへこの性質を移す。
未知slotへ代入される型自体をsingletonに制限する主張ではない。
明示的なrigid要求からlabelを消すと、残る要求は元のsingletonかemptyRecordである。
`maskReference` はこの残りを元の有限pool内の参照として計算し、`maskReference_source` と
`compileSource_erasure_closed` が正確性を示す。`compileSource_upper_record_tail` は、
要求record nodeのtail参照が実際にemptyRecord tagを持つことまで導く。

### 10.32.3 既存nodeを保つ実行可能なinspection

`RecordDemandInspection.inspect` はopen-record供給と空/singleton要求を直接分解する。

| 供給と要求 | 生成する辺 |
| --- | --- |
| record供給、emptyRecord要求 | 元tailから同じemptyRecord nodeへ |
| 同じlabelのsingleton要求 | headから要求payloadへ、およびtailから要求のempty-tail nodeへ |
| 違うlabelのsingleton要求 | 元tailから元の要求nodeへ |

元の型slot、node数、constructor等式、row問題は変えない。`none` はこのinspectorの未対応pairであり、
型矛盾を意味しない。全域な `expand` はその場合に元の辺を残す。
`inspect_exact` と `expand_exact` は任意の元のrealizationについて分解前後の制約を同値にし、
`expandCompiled_instances_exact` は同じvalue/row割当てで全target instanceを保つ。
有限モデルと下記の正則モデルの両方で必要なrecord法則を実際に証明して使う。

`SourceRecordDemandInspection.prepareSource` は全source alternativeを保ってこの一回の分解を適用する。
`source_record_pair_inspected` は元compilerのrecord対record制約が実際に分解されることを示す。
`shadow_source_typing_exact` と `shadow_regular_source_typing_exact` は、それぞれのモデルで、
分解後のgraph族のinstanceと独立な元の閉Typingを一致させる。
ここにもconstructor realization・値型制約・row制約を含む `Models` 条件は残る。

### 10.32.4 決定40を満たす正則carrier

`ShadowRegularValueTypes` は既存の `Layer`、graph、`observe` を変更せず、各有限観測の比較を
`ShadowSemanticRecords.Subtype` で解釈する。全観測深さを量化し、外部fuelは使わない。
任意の既存Layer tailについてshadow等価とhead/tail合同性が成立する。
`record_tail_covariant` はrigid要求への共変性だけを使う。

`observe_tree_mono` は新しい有限関係の全規則を保存する。十分な有限観測では元の有限treeが
復元されるので、`finite_conservative` は保存だけでなく反映も成立する。
`ShadowRegularInferenceModel` は既存共通モデルの `subTy` だけを更新する。
record constructorの同一性は `model_record` の `rfl` で確認できる。
`embed_subtype` は任意の有限raw型 `A,B` について

```text
ShadowRegularSubtype (embed A) (embed B) ↔ ShadowSubtype A B
```

を示す。有限blockやfiniteGraphの埋込みも比較を保存・反映する。
旧正則モデルと有限Shadowモデルからの任意の閉core式のTypingは新モデルに保存する。
正則側には追加の存在量化witnessがあるため、Formula/Typing全体の逆向き保存は主張しない。

### 10.32.5 全coreの自由parameter求解へ残る義務

今回閉じたのは要求の正確な分解、元source graphの要求表現の閉包、分解前後の全instance一致、
正則モデルの整合性である。これを使う全graphの飽和と、自由parameterからの一般解構成は別の定理である。

既存 `RegularValueTypes.Layer.record` のtail位置は有限Layerであり、payloadのようなState参照ではない。
`OpenRecordConstraintGraph.Node.recordExtend` はtailもnode参照として持つので、一般のtail依存を
そのまま既存blockへ写す構造的なcoalescingはまだない。State参照に単に置き換えると観測深さが
減る位置が変わるため、同じ意味を保つ証明が必要になる。tail-cycleに解が存在しないという主張でもない。

必要な出力側の契約は、既存の `coalesceGraph_satisfies` と `coalesceGraph_retraction` に対応する、
新関係・open-record graphでの次の二点である。

1. 任意の自由parameter割当てから構成した解が、全constructorと全制約を満たすこと。
2. 任意の元の解をparameterに取ると、共有された元slotをすべて保持してその解へ戻ること。

一般の任意tail共変性を追加することは、この接続の前提ではない。
全coreの自由parameter主型性・拒否完全性、`SourcePrincipalInference` の `RecordFree` 除去、
effect式・再帰sourceを含む全言語の実行安全性は引き続き別の未完義務である。
