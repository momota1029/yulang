# computed Call の dependent Bind result 構成

COMPUTED-RESULT-DEFINITION-20261024/r2。著者 `/root`。前稿の「元 relation/interface grammar が既に complete descriptor を形成する」という CB2/CB3 の主張は、独立査読 MAJOR により撤回した。CB1 と operational composition は受理された。以下で T_e と Bind graph はまず関係・interface の構成とし、descriptor の形成・導入は明示した追加橋を必要とする。新しい [EvalInvoke constructor](../design/2026-10-24-computed-call-result-constructor.md) は、その欠けていた生成 case を別途定義する。r2 と新定義は再査読待ち。

## 1. 元の不足と今回の対象

[FO1](2026-10-24-finite-observation-source-bridge.md) は、callee の genuine computation proof、actual callable Return、whole argument checking を入力として、computed Call の全実行 phase を構成した。一方、最後の DescMem(R_c,O,w;ξ) に必要な computed-result constructor は残っていた。

[選択済み ReadInvoke](../design/2026-10-08-pure-read-call-result-constructor.md) の identity result clause は structural Name callee に限る。その clause を一般 callee に適用せず、元 [source Bind/Call](2026-10-08-source-generalize-definition-and-proof.md#31-source-constructor-rules)、[dependent Bind interface](2026-10-08-call-source-interface-construction.md#5-constructor-cases-generating-the-structural-suppliers) と元の computation-constructor image を用いて **別の合成 endpoint** を構成する。

本稿の無条件な結論は relation/interface graph と operational composition である。generated endpoint の typing は、下に明記した descriptor 橋の追加前提の下で成り立つ。独立に固定された foreign R_c、production resolver がこの graph を実際に選ぶこと、既存 source inference の全成功をこの graph に移すことは別の命題である。type variable の sort や scope を変えてこの endpoint を代入することも許さない。

## 2. 独立入力と形成時点

実 Call occurrence e と、元の全 dependent frame IF_e を固定する。callee code E_f、argument code E_a、raw source operation と ξ=(ν,K,D)、binder tree、original origins を保持する。

* C_f は E_f の独立に形成済みの complete computation descriptor。d_f は同じ E_f の全 prefixes/Requests/Return/futures に対する genuine source proof。任意の actual CalRet で、同じ callable v、実 decomposition U、provider r、current world w と **genuine hereditary F certificate** を取り出す一様な result projection がある。この projection は C_f の実 Return interface とその元 checking proof に由来する。
* F は実際の checked callable view。D_F は元の独立 complete challenge domain、I_F は同じ whole-carrier interface。D_F に actual acceptance、Q、望む結果 typing を入れない。
* 各 actual CalRet/current event の下で、同じ E_a の inert licensed formation と whole designated execution checking がある。その proof function は同じ capture/origin/guards を保持する。単なる返却 endpoint inclusion ではない。CA3 は明記した actual-source component、CA4 は target-specific arm leaves がある場合の complete component を供給する。
* 原 raw transitions、receiver/role/entry/consumer/return laws、licensed formation、whole-map restriction laws、全 applicable independent alternatives の元契約を保持する。独立 arm について必要な genuine full typing はその owner の入力であり、source branch が作るものではない。

F、C_f、I_F、IF_e と以下の有限 graph を **callee 実行前・comparison 前**に形成する。actual CalRet の値は graph の内側の元 ResultBind telescope で束縛する。後で返ってきた都合のよい値を先に自由変数として埋めた endpoint ではない。

## 3. post-CalRet receiver suffix の構成

元 Call raw operation は、callee computation の後に、その実 Return が渡した provider/current world で argument Delay と dispatch を行う。ここに既に存在する continuation を S_e(b) と書く。b は元の actual CalRet tuple とその同じ typed result fields。新しい source binder、Name lookup、runtime transition を挿入しない。

### CB1（ReadInvoke の receiver 側に Name inversion は不要）

選択済み ReadInvoke の各 phase clause のうち、actual CalRet **以降**の semantic obligations は、同じ b、元 F/I_F/D_F、argument と receiver の元 interface、原 guards によって構成できる。Name 固有の lookup/Return inversion はこの suffix の証明に使わない。

証明。定義 §3 の全 clauses を次のとおり展開する。

| stage | 必要な元入力 | Name 固有情報の使用 |
| --- | --- | --- |
| actual CalRet の直後、Delay 前 | b の same-provider F certificate、元 current-world/capture/formation guards、未実行 argument/receiver suffix | なし。b の supplier が前半の computation へ移る |
| actual Delay formation 後 | 元の inert carrier c、independent whole checking、同じ tuple の d∈D_F | なし。c の形成は元 E_a の origin による |
| actual receiver receipt/entry | 同じ U/r と c に対する F membership の admission elimination、元 receipt/role/entry law | なし。callee の code shape は admission rule の前提ではない |
| body/consumer/Return | 同じ d に対する全 P_F(d)、元 IF_e の receiver/result/future incidences | なし。実行するのは actual returned U |
| Request/resume/FutureUse | actual raw handle、後の current world、元 response と未実行 suffix、同じ provider の hereditary certificate | なし。昔の Name event を再実行しない |

ReadInvoke にある「initial/lookup prefixes」とその Name binding obligation はこの表の前に属する。computed E_f に対してそれらを使うのではなく、d_f がその実 callee prefixes と CalRet supplier を与える。receiver に残る source-origin/whole-frame fields は消さず、元 general IF_e の同じ実 callee-result/argument/receiver slots を用いる。interface injection から guard truth を推測せず、上記 genuine inputs の同じ fields を入れる。

各 phase の定義をこの入力で直接満たし、元 Request/Bind 式と receiver theorem E の Value/Retained/Operation cases を使えば、全 finite developments と合法 restrictions を扱える。これは Name 証明の statement を広げたものではなく、suffix の clause ごとの proof function である。□

### 形成する open suffix contract T_e

T_e(b) は以下の元 constructor graph の略記とする。

1. b の actual returned-provider telescope の下に元 **Call continuation constructor image** を置く。初期位置は実 CalRet 直後で、まだ Delay/challenge/receipt はない。
2. 元 Delay の inert formation と complete carrier interface を、その実 formation region へ置く。元独立 challenge constructor は actual c の形成後の region に置く。
3. 元 receiver-operation interface を same b.provider/current-world における contextual Ref として挿入する。receiver の complete obligation は元 P_F のままであり、body result だけにしない。
4. 元の receipt、entry、body、consumer、invocation return、pending/resumption/future の constructor-image clauses と hard/scope/authority guards を、それぞれ元の position で conjoin する。各 prefix はまだ実行していない部分を suspended obligation として保持する。
5. receiver-local independent arms は元 receiver reference の中に、argument-local arms は元 carrier interface の中に残す。全体 Call の独立 arms は §5 の別 slots に残す。

これは original Return/Request/Bind/Call continuation の constructor image、同じ tuple 上の conjunction、scoped binding、元の relation references から成る有限 graph である。§3 の T_e は、Call continuation の実 source constructor で形成する **open relation/interface contract** の表記であり、whole source image を DescMem と定義する表記ではない。例えば receiver の P_F は元の全 independently compatible observations を保持し、特定 E_f/E_a の実行に限定していない。

その formation を確かめる。依存する b は元 Call/ResultBind telescope で宣言済み。c と d はその形成後の同じ event telescope で束縛され、どちらも前へ逃がさない。raw handle/response/current-world は元 Request binder、returned provider/future は元 result binder にある。全 negative/universal predicates は元の独立 domain と意味を保った typed primitive/reference のまま。有限 source frame の constructor/registration induction により全 slots、scopes、共有 incidences が well-formed である。これが **構文的形成**。CB1 の genuine operand/guard proof が、それぞれの phase の **semantic introduction** を与える。両者を一つの「frame があるから真」という推論にしない。

この construction 自体は relation/interface grammar の結果にとどまる。T_e を complete computation descriptor にする形成規則と、その意味・導入規則はここから自動的には出ない。以下の CB2–CB4 の descriptor 主張には、同じ phase tuple に対するその明示的な橋を前提とする。新 EvalInvoke 定義の EI-Form/EI-Intro は選択した generated-result case についてその橋を供給する。固定 foreign descriptor に対する橋は供給しない。

## 4. dependent Bind による generated endpoint

まず元の関係・interface Bind constructor により

```text
R_e^Bind = Bind(C_f,
                CalRet(v,U,r,current_world,typed_result_fields),
                T_e(v,U,r,current_world,typed_result_fields))
```

を形成する。Call の callee-return と argument/receiver slots の middle equation は元 IF_e の ResultBind のもの。ここに元 raw source operation の callee-phase/continuation decomposition を用いる。新しい source Bind expression への書換えではない。

### CB2（明示した descriptor 橋の下での形成と、元 operation の同じ tuple）

同じ Bind relation/interface graph に対する complete descriptor formation と staged interpretation の橋を仮定する。この追加前提の下で R_e^Bind は complete computation endpoint として読める。その source branch の operation は元 Call(E_f,Delay(E_a)) と同じ全 phase tuple を保持する。

証明。関係/interface の形成は C_f の frame と §3 の T_e graph を元 Bind formation に入れる。descriptor の形成には、ここで明記した別の橋を適用する。ResultBind が束縛する値・provider・current world は、C_f の同じ actual Return fields そのものである。callee Return projection は source endpoint を変更する conversion ではなく、同じ returned value の genuine F checking を供給する。T_e の各依存はこの telescope または元外側 telescope 内にあるので、R_e^Bind は execution 前に閉じた schema として形成される。

原 Call の structural operational equation は callee computation を実行してその continuation S_e に接続するもの。元 Bind の式は

```text
Return(b) >>= S_e = S_e(b)
Request(q,w,k) >>= S_e
  = Request(q,w,(a,w′). k(a,w′) >>= S_e)
```

である。両者の initial/admin/CalRet/Delay/receipt/entry/return の phase labels は元 IF_e の同じ phase embeddings を用いる。completed prefix を二重実行せず、zero/incomplete prefix は callee が本当に到達した stage のまま保持する。callee Request はまだ Delay を作らず、その **形成を含む**全 S_e を残す。receiver Request はすでに済んだ callee を継続へ再接続せず、T_e 内の未実行 receiver suffix だけを残す。これで任意 finite raw development への帰納により whole observation、provider、world、handle、witness の対応が恒等的に得られる。□

CB2 は単なる入出力等価や ANF/beta law ではない。元 Call の定義に既にある sequential decomposition をそのまま使っているので、余分な Name lookup の prefix を消す必要がない。

### CB3（明示した descriptor 橋の下での introduction）

CB2 の descriptor 橋と、それに対応する genuine phase evidence からの introduction rule を追加前提とする。その前提と §2 の genuine inputs の下で、元 source-base Call の各 structural observation O に対し、同じ w/ξ/source derivation を保持した

`DescMem(R_e^Bind,O,w;ξ)`

を構成できる。M_E はこの結論を前提にしない、元 source-base relation のままとする。

証明。前半の実 source prefixes には d_f の C_f introduction を使う。Request ならその実 handle と response/current-world telescope の下に、以下の後半証明関数を suspended suffix として保持する。ここでは b や receiver receipt を作らない。

actual CalRet の時だけ d_f の genuine result projection による same-provider F certificate を取り出す。同じ current world で argument の inert/whole checking proof function を使い、独立 d∈D_F を形成する。F membership の admission と observation clauses により、同じ actual U/r/c に対する元 receiver 全 P_F を得る。CB1 の phase introduction に入れて T_e(b) の descriptor evidence を得る。

その C_f evidence と、元 ResultBind の同じ b を middle とする T_e evidence を **追加前提で明記した descriptor introduction** に入れる。CB2 の同じ phase tuples により、結論は別の source operation についてではなく当該 O についての DescMem である。Return/future は T_e の元 actual provider と certificates、resume は実 current world の同じ関数を使う。合法 restriction に対する自然性は d_f、whole argument proof、F certificate と各元 Bind map の自然性の合成で従う。□

証明は callee/body が Return することを一律に仮定しない。callee の full computation proof が発散・Request を許せば、それらの全 prefix も R_e^Bind に残る。純粋な実 source の CA2 は d_f を供給できる一例であり、CB3 が一般 callee に純粋性を要求するわけではない。

## 5. 全 independent alternatives と固定 target

complete Call には callee-local、argument-local、receiver-local、whole-Call の独立 alternatives があり得る。前の三種類は C_f、whole carrier、P_F の各 **元 complete** input の中で保持した。whole-Call の独立 arm α は callee/receiver の structural sequence を実行する必要がない。

その arm の元 complete endpoint R_α と genuine typing、guard/provider/future/admission fields がある場合、元 tagged Union/result formation で

`R_e^gen = Union(source-slot:R_e^Bind, arm-slots:{R_α}_α)`

を構成する。登録された parameterized family は元の Ref とその同じ binder に保持し、無限世界を列挙しない。arm が独自に scope/role/provider を変える時も、その actual arm-local tuple を自身の slot に運ぶ。

### CB4（同じ descriptor 橋の下での complete result と fixed R）

CB2/CB3 の descriptor 橋と全 genuine arm-local inputs がある場合、元 complete Call の全 alternatives に対する R_e^gen の descriptor introduction を構成できる。独立に固定された R_target への checking は、各同じ arm/source slot から R_target への genuine **target-specific** inclusion がある場合に限り、その元 checking grammar で合成できる。

証明。実 alternative の tag で場合分けする。source は CB3、whole-Call arm α はその元 complete typing に Union injection を適用する。別 tag の provider/witness を選び直さない。callee/argument/receiver 内の arm は既に各 full operand の proof に含まれ、その contextual IF insertion を通じて同じ依存 fields を保つ。固定 target の結論は元有限 Union elimination と各 actual inclusion の合成。□

この生成 result の Union は元の全 alternatives を表す result formation であり、新しい W/Z law や source tightness を選んだものではない。独立 arm が存在しても、その target-specific inclusion を持たずに pure target へ弱めることはできない。CA4 の残項はこの構成によって消えない。

## 6. FO/CA と元 source endpoint への適用

actual source family の computed G callee について、CA2 は同じ actual gκ/current world と TU の F certificate を渡す。CA3/CA4 が必要な whole argument checking を供給する範囲では、FO1 の phase 証拠を、明示した橋がある場合の CB3 introduction に入れられる。従って **generated composite endpoint R_e^Bind/R_e^gen** を result とする場合の最後の descriptor judgment はその橋に条件付けられる。新 EvalInvoke の EI-Form/EI-Intro は別途定義・証明する具体的な橋であり、古い grammar から自動的に得られたものではない。

source の未固定 result slot が元の complete computation sort とこの constructor graph の依存 telescope を許す場合、その slot への具体的な代入候補は R_e^gen そのものである。graph 内の CalRet/response/future binders は元の position に残るため、later challenge の値を source inference の外側へ逃がす代入ではない。適用には slot の **元 introduction と sort/scope** を使う。native の単なる新 row 名から complete source Desc declaration を捏造しない。

本稿の既存規則だけによる結果は relation/interface graph と operational composition。descriptor の形成・導入は CB2/CB3 の明記した追加橋に依存する。元のアルゴリズムが発行した全 result slots がこの sort/scope を持つこと、その各 native constraint がこの graph を保つこと、solver がこの source certificate を受理することは別の source/native correspondence である。Name route の既存 R_c=ReadInvoke はそのまま使えるが、R_e^Bind と自動的に definitionally equal だとは宣言しない。

また foreign に固定された R_c の DescMem までを CB3 の結果から引き出さない。そこには本当の interpretation/target inclusion が必要である。これは旧 FO の「任意の独立 R_c でも同じ証拠が使える」という未証明な主張を復活させないための境界である。

## 7. Receipt と残る親義務

契約 [LOCAL-LET-COMPUTED-RESULT](../../tasks/agent-loop/sprints/local-let-computed-result-20261024.md)、SHA-256 `f3a1ce51332e32d53310944ef8e44a9fde1465b843b882e2f7a92eaabac84dd2`。使用したのは元 ReadInvoke の staged clauses、source/Bind/Call constructor grammar、IF、genuine input-realization、受理済み FO/CA の明記した範囲である。実装・tests・build・probes・compiler run はない。primary 単著、独立査読待ち。

既存規則からの受理済み結果は Name 依存を除いた suffix proof と元 Bind/Call の actual whole-tuple operational composition。complete descriptor formation/introduction は追加橋を要する。full original source/native emission、foreign embedding、未知 primitive/arm laws、一般化/主型性、actual extrusion receiving qualification と全体停止性はこの結果だけでは閉じない。元の全 source/A/B 量化は維持する。


## 8. MAJOR の訂正と新 constructor への適用

初稿査読 SHA-256 `d99b651b589090b102068b4f02db11837cccc7e2b81e308cc247ef66de364f4e`。独立査読は、source-contracts §2.1 の relation graph と独立 DescMem の区別を指摘し、元 IF-Bind から Bind-Desc を導いた箇所を MAJOR とした。primary はその無条件な descriptor 主張を撤回した。上の CB2–CB4 は正確な追加橋を持つ条件付き主張であり、CB1 と operational composition は元の受理済み範囲を保つ。

新 [EvalInvoke 定義](../design/2026-10-24-computed-call-result-constructor.md) は EI-Form、全 staged DescMem、generated-result identity case を **新たに**定義する。EI-Intro は CB1 と元 genuine operands からその解釈を満たす証拠を作り、EI-Name は元 Name-only ReadInvoke との両方向の一致を証明する。その definition が選ばれた generated case では、上の relation/interface graph を同じ full tuple の EvalInvoke descriptor として実現できる。任意の fixed foreign R や native fresh row への対応は別のままである。

再査読契約 [COMPUTED-RESULT-DEFINITION](../../tasks/agent-loop/sprints/computed-result-definition-20261024.md)、SHA-256 `db4aaa97df00ba5349b662ac62cd027698da3f713835f650c780dbbc2ccdb834`。新しい descriptor 規則を既存規則として記録しない。独立再査読待ち。


## 9. r2 の再査読

r2 査読対象 SHA-256 `a233d2bfe7be9beff75bdec1086f031d81b6a2090aad33f78516fe6d24e57f67`。新 EvalInvoke 定義とともに独立再査読を通過した。一般の CB2–CB4 は明記した descriptor 橋の条件付き主張のままであり、選択した新 generated case では EI-Form/EI-Intro がその橋を供給する。固定 foreign R と native slot 対応は閉じない。旧 MAJOR の修正を、IF だけで descriptor を作れるという旧主張の復活として扱わない。本文の再査読待ち表記は r2 freeze の履歴。この receipt 以外の数学本文は再査読時と同じ。[outcome](../../tasks/agent-loop/sprints/computed-result-definition-20261024-outcome.md)を参照。
