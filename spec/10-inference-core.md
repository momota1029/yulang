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

handlerの結果 `out : CompTerm α` と外側のscheme環境 `SchemeEnv α` は局所slotを含まない。`EffectInference.local_result_no_escape` はどの局所割当てでも結果の型・行が元の `out` の評価と一致することを、`local_outer_environment` はどの局所割当てでも同じ外側binding環境を表すことを証明する。したがって局所変数のescapeは核の規則の構造で排除され、存在型へ包んで外へ出す規則はない（章5.1、確定2026-11-05）。source上でescapeを検出しエラーを報告するelaboratorまで証明したものではない。局所slotの行成分は空行であり、局所行変数は導入しない。atomのkeyと追加effectは局所割当てによらず固定する。atomのpayload内部に現れる局所変数と、局所変数のrole制約はこの形式化の対象外である。

`SignedStructural.generated_poly_request_at_any_type` は任意の構造型での呼出しを受理し、`generated_poly_requests_independent` は同じ署名・同じ外側の割当てでintとstrへの二回の独立した具体化を受理する。`generated_poly_handler_resumes_payload` は任意の局所型で `k payload` を受理する。一方 `generated_poly_handler_payload_escape_rejected` はpayloadを固定のint結果へ直接返す腕を拒否する。負例は局所型をstrとしたときの `str ≰ int` によるもので、任意のモデルや任意の固定結果上界について拒否を示した定理ではない。

`SignedStructural` は共通の構造部分型を実際の `Directed.Row` へ具体化し、`RowView` を恒等写像で実装する。このモデルでは、operationの生成制約が自身の行を含む結果を受理し、空行を拒否する。また、保護前の解除が作る負の差分を持つ行は受理され、その差分を空行へ消すことは拒否される。これらは任意のscope数と解決済みkeyについての定理である。

`DirectedBounds` 内の `Directed.Computation.shallowHandle_bounded` は、符号付きcomputationのactionと両armに実行時の上界があることを前提として、上の残余と和がhandler全体の上界になると証明する。継続の前提にも元の行を使う。境界での保護・解除によるcomputationと行のtransportは双方向に上界を保ち、この主張自体には `ZeroAt` を必要としない。上界のtransportと非captureを混同しない。

`RowInference.generated_signed_handler_composes_effect_bounds` は、成立したhandler生成制約を独立の型判断へ戻し、action・armの明示された実行時上界と組み合わせて、実際の符号付きshallow handlerの出力上界を導く。この合成定理は `DirectedHandlerInference` に置く。型付けからaction・armの上界を導くpreservationを、前提の中へ隠して証明済みと数えない。

この層では、payload・action・armを前節のcore `Expr` で表し、一つの解決済み規則ごとに生成する。effect構文を再帰的に含む一つのsource ASTからの翻訳まで証明したものではない。また、境界規則がここで変換するのはその場のcomputation行である。値の中にある関数の潜在行と10.3.4の高階transportを結び付けるには、型に沿ったelaborationの証明が別に必要になる。

### 10.5.3 sourceへ接続するときの義務

- **一般化**: 構文的な値だけを一般化する。環境由来の未確定変数を量化してはならない。計算された binding は単相で共有する。再帰 SCC は同時に扱い、computed-value cycle を通さない。
- **operation の多相性**: 呼出側は operation-local 型変数を具体化する。handler 側は抽象型として受け取り、任意の具体型へ単一化しない。role 制約があれば、その証拠だけを利用できる。
- **method / role**: receiver の下界が定まるまで解決を保留する。field/with、role、effect 行の優先順位を守り、同じ階層の複数候補は曖昧とする。
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

## 10.7 既存仕様に残る判断

ここでは未確定の意味論を補って定理を強く見せない。

- generic role、再帰する where、associated type の解決についての循環・停止条件。
- 章4.5の残余と、source の網羅性・guard の組合せ。

上の判断に依存しない核の定理は先に閉じる。未解決制約を受理済みプログラムと同一視しない。

`Annotations.no_substitution_invariant_extensional_check` は、さらに次の三つを同時に満たす単純なcheckerが存在しないことを証明する: 未知の行を常に受理すること、許可外の具体headを拒否すること、任意の行置換に対して受理が不変であること。未知行をその具体headで置換すれば矛盾する。したがってT3の注釈検査は、**注釈を検査した時点で見えている具体 effect** だけを対象にする（確定, 2026-11-05）。共変の注釈は行変数を束縛せず、検査するだけで、反変の許可と同じ変数に集まって干渉することはない。その時点で見えていない行変数が後で具体化されるのは、一般化された型の具体化（代入）であって、注釈の再検査ではない。注釈の時点で既に分かっている effect（例えば引数の型が `undet` を出すと分かっている場合）は、その時点でエラーになる。局所snapshotの検査はこの方針に対応し、実装・証明した。
