# B4r5: head grammar の同値と、捕捉後の合流

状態: **設計判断待ちの case analysis**（2026-11-07）。E1/E2の終了報告ではない。
新規 `CommonRoleCaptureNormalization` の局所定理を記録する。
旧E2は保存するが、第五回の承認済み規則への反例として流用しない。

## 1. completeness を主張する前の grammar 監査

spec4.5 / 4.7b / 4.8 / 6.3を読むと、sourceのheadと、推論/合流後のproducer型を区別する必要がある。
次の表は全文法のnormalizer実装や完全性証明ではなく、必要な同値の列挙と現在の境界。

| 形 | 表面の許可と同値 | size監査で必要な扱い / 現状 |
| --- | --- | --- |
| 基底型、any、never、unit | 注釈に書ける。top/bottomの順序とunit/0-tupleの同一視 | groupingと0-tupleのelaboration後carrierで数える。集合論的な「pair(never,T)=never」等は持ち込まない。既存Commonのpair/variant/arrow inversionが各成分を保存する |
| tuple/pair | 位置とarityを保持。共変producer unionの成分ごとの合流はspec4.7b | 一般unionを直接source要求位置へ追加しない。実mergeが作るproducer payloadではpair_union_group等も考慮する |
| 関数、effect行 | arrowはdomain反変/result共変。行はextensional carrier。effect注釈はT2/T3契約 | 既存common_arrow_iffが成分と両行の順序を反映。source行のリスト順や重複セルを型サイズに持ち込まない。任意row代入を注釈から推測する規則は未指定なので仮定しない |
| nominal型 / named再帰 | declaration ID、arity、kind、順序を保つinvariant引数。同じbodyでも別名は別型 | bodyを展開しない。型aliasとは区別する。CommonNominalHeadsの既存定理が根の同値を扱う。新しい一般nominal integration定理はまだない |
| transparent alias | spec4.6のaliasは新型を作らない | head elaborationで展開後に数える。phantomなalias引数をnominal引数のまま数える反例は採用しない |
| record | first-field-wins、隠れた同名field除去、field順序の交換、幅の部分型 | 可視fieldの順序交換はsize/occを変えない。hidden fieldはNで除く。tailは具体goalから明示labelを引くcanonical residual。任意同値代入を選ばない |
| optional field | spec4.3/7.5の推論/表示形。optional-anyは既存OptionalPayload意味ではrecord幅以外を要求しない | `x?`がparserでidentifierとして読めても、optional annotationの意味が許可された証明にはならない。sourceに書けるoptional headと勝手に仮定せず、E2に使わない |
| variant row | tag一意、同tagのpayload合流、表面の二綴りが同じ行。重複tagは宣言エラーでない | 承認済みNで合流/冪等縮約後に数える。異なるtagは新しい要求を加えるので不可視paddingにしない。open row注釈はspec4.5で不可、推論された残りを任意に分割しない |
| 一般union/intersection | 直接の型注釈は不可。要求位置の型unionはない。variantの行区切りは別物 | 合流後payload等のproducer側に生じる場合だけ扱う。冪等性/合流/吸収等の全正規化は、source grammarと実producerの橋を伴って示す必要がある |
| associated type | 選択後は普通の変数と等式。他roleのassociated RHS参照は禁止、HDA必須 | 任意のprojection展開をhead matchingへ追加しない。定数RHSを用いた局所例はHDAを破らない |

この列挙から、record hidden field / repeated variant tag以外の新しい**閉じたsource由来**paddingを見つけたとは言わない。
optional-anyやsource行のrawセル数を新E2として報告しない。
また、N後sizeが全Common同値headについて不変であることを証明したとも言わない。
以下では、同値不変性だけでは元Paterson置換補題を回復しない点を切り分ける。

## 2. 直接捕捉と、遅延mergeの順序

質問のsourceは一般unionを含まず、roleの第一引数がplain変数。
goal `R int (:{tick (int,int)})` の第一引数が'aをintに直接決める。
新moduleの `capture_zero_actual` は既存 `Roles.matchingSubst` / `extractArgs` が実際にこの値を返すことをrflで示す。
したがって、逆向きのCommon同値方程式に対して都合のよい存在代入を選ぶ例ではない。

```text
head:  R a (tick(union(pair(int,a), pair(a,int))))
child: R a (tick(pair(a,a)))
direct capture: a := int
```

変数が未確定のsymbolic Nでは二payloadは異なるため縮約できず、実size9/5、変数occ3/3。
捕捉後は両payloadがpair(int,int)になって合流し、実sizeはhead/childとも5。
`N(subst head)` と `subst(N head)` は異なる。

spec4.7bの成分ごとのpair合流を先に行っても、
headは `R a (tick(pair(union(int,a),union(a,int))))` となり、symbolic size9、捕捉後size5。
`coalesced_meaning` は任意Common解釈について元headとこのheadの同値を証明する。
したがって、「pairの合流を一段加える」という別分解でも、このtiming問題は消えない。

任意Common代入を量化する `normalize_meaning` / `subst_eval` / `coalesced_meaning` は、
構文解釈のcongruence/意味保存の定理。実solverがその代入を探索すると定義していない。
運用上の捕捉は固定した実extractorによって別に証明する。

## 3. 問いにした三場合

spec6.3は宣言時にwhereのsize条件を検査するとし、同時にpayload mergeは型が分かるまで遅らせるとしている。
捕捉で新たに生じる縮約にも宣言checkが安全である必要があるか、具体化時にcheckするかが明示されていない。
一問を [capture-before-size](../questions/2026-11-07-b4r5-capture-before-size.md) に置いた。

1. **capture-safeな宣言check**：提案条件CaptureSafeは、任意Form割当てでN後child size<head size。
   これは新規の提案であり、承認済みcheckerと同じだとは扱わない。決定可能性/完全性も未証明。
   `capture_safe_rejects` が局所例を拒否する。証明に使う反例割当ては実第一引数捕捉と同じ固定capture。
2. **具体化後check**：`late_check_rejects` / `coalesced_late_check_rejects` が、実checkerは捕捉後の例を拒否することを示す。
   これを採用するならK2以外の新しいuse-site拒否を意味論へ明示する必要があり、実装都合で黙って採用しない。
3. **symbolic宣言checkのみ**：`symbolic_checked` は受理を、`captured_head` / `captured_child` は実instanceの自己遷移候補を示す。
   この読みでの強いE2を、未決のtimingを決めないまま現在の言語へ適用しない。

このlocal familyに再帰型、record tail、associated projection、nominal bodyはなく、両K2で止めるものではない。
拒否先行は従来どおり未決の作業上の選択であり、今回確定していない。

## 4. 正確に欠けるlemmaと、試した分解

元Rolesの `size_decreases` の代わりに、実matcherへ必要なのは次。

```text
任意verified declaration i、任意型/行確定の有限regular goal g、
実matcherがgから計算したcanonical capture σ、任意実where child c∈i.constraintsについて、
  N後の宣言checkがiを受理し、K2で禁止されるroot/constructor検査がないなら、
  size(N(c[σ])) < size(N(g))。
```

σを任意のCommon解やresolver成功仮定として外から渡していない。
必要な新lemmaは「実captureの計算からこの不等式を導く」もの。
symbolic Nのsize/occ check**だけ**から導く版は局所定理
`symbolic_check_does_not_imply_captured_descent` が否定する。
しかし、それが承認後checkerの全条件だという前提を確定していないため、full E2にはしていない。

試した別分解：pair成分ごとのcoalescingを先行させた場合も同じsize9→5を証明した。
一方、capture-safe宣言conditionを先行させる場合と、具体化後checkerを用いる場合は、この例が拒否されることを証明した。
今後の全域resolver証明をどちらへ接続するかは、上の一問の答えに依存する。

## 5. qualifiedと全目標の残り

全Common Nの完全性、正準matchの全source grammar、全regular resolver、一般finite-tree/nominal agreementは未証明。
今はE1/E2のいずれにも達していない。

qualifiedの未証明interfaceは、任意有限検証済D/visible V/method表M、有限kind付き自由名集合A、
有限scheme環境Γ、任意full式e、結果型/行項outについて、
実有限生成Cがmethod ID/ordinary・associated等式/pending goals/weak-captured-generalizedを保存し、
任意kind保存ρ（type名→任意Common.Ty、row名→任意Common.Row）で、
独立QualifiedTyping(D,V,M,Γ.evalρ,e,out.evalρ) iff あるlocal割当てιがCのordinary/associated制約、
canonical residual・K2を含む独立全role辞書、共有captured/各使用generalizedの条件を満たすこと。
未解決record tailは生成時には解かず、具体化までpending。
さらに全返却schemeの任意無制約parameterがmodelを与え、全元modelを同じrow/要求同値の全type slotとして回収する全familyが必要。
Satisfiesを外部parameter条件へ移さない。これらは未証明であり、今回その単独非存在も示していない。
