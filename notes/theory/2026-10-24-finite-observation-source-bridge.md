# 有限 next 観測の actual callee・Call phase 構成

FINITE-NEXT-COVERAGE-20261024/r1。著者 `/root`。状態: FO1 は明記した前提の下で独立査読受理。FO2 の無条件な適用には MAJOR 指摘があり撤回し、以下の正確な edge checking 前提を持つ条件付き合成だけを残す。

## 1. 使用する原 source family

[TU1–TU4](2026-10-24-two-input-recursive-source-use.md) の同じ h₀=λz.0、同じ f/root、同じ joint world と complete certificates を固定する。U=Int|Bool、A=Record(a:U)、Q=Record(first:Int,next:G_U)。F_U は A の entry 後に actual inner closure G_U を返す。G_U の entry は U、body は元 h Call、再帰 f Call、Record の順であり、全 complete/pending/future clauses は TU3 のものを保持する。

本稿は computed callee の actual Return と receiver を source rules から構成する。Name-only ReadInvoke を computed source code の result descriptor に流用しない。最後に原 source の独立 result judgment へ戻すために必要な、残る constructor field を区別する。

## 2. 有限の観測 graph と共有

次の sort を持つ有限導出を考える。矢印は型のみの略記であり、各 edge に元の complete source interface が付く。

| node | raw constructor | returned endpoint |
| --- | --- | --- |
| Root | resolved Name f | F_U |
| G | Call(Root,Delay(Record(a:P)))、または Select(Qnode,next) | G_U |
| Qnode | Call(Gnode,Delay(P)) | Q |
| First | Select(Qnode,first) | Int |
| P | 0 等の Int literal、true/false の元 Bool binding、First、succ(P_Int) | U への原 checking を持つ ground value |
| Aggregate | 有限 ordered Record of nodes | 元 field endpoint の Record |

succ の引数は元 Int checking を持つ場合だけである。これは選択した構文の型付き導出の前提であり、Bool を Int に扱う許可ではない。元 primitive succ の complete contract を保持する。

構文 tree で同じ式を二回書けば、その式の計算も別々である。fan-out は、元 Bind が actual Return を入れた immutable monomorphic alias を複数の Name が読む場合に限る。その alias では same value/provider/certificate を restrict し、新しい closure や fresh source value を作らない。native root scheme の別 freshening frames と、runtime f/root が同じであることを区別する。

各 child の順序は元 source constructor の順序で固定する。とくに Call の P は callee より先に実行しない。まず callee、次に inert Delay の形成、その後 actual entry の指定 Force で初めて P を実行する。Record(a:P) も carrier 内の元 ordered Record code であり、proof induction に P の証拠があることは、その P を先行実行したことを意味しない。

## 3. 元の Bind/Call の phase 規則

source-interface construction は一般 Call の callee-result、whole carrier、actual receiver、result/future を含む FrameCall を既に作る。[receiver theorem E](2026-10-08-call-semantic-input-realization.md) §6.1 は effectful/computed callee の場合、callee 自身の typing と actual Return が別の前提になることを明記する。以下はその前提を観測 graph に沿って供給する構成である。

### 補題 FO1（computed callee Return からの receiver phase）

元 raw callee code E の各 prefix と actual Return に、その original source interface と同じ returned callable v/provider r/current world w、および genuine hereditary F certificate が構成されているとする。argument の inert formation と指定 Force の full checking が同じ event にあり、元 independent challenge/guards/arms の証拠を持つとする。

この時、元 Call(E,Delay(P)) の全 raw phase を次の一つの dependent function で証明できる。

1. **callee prefix。** E 自身の証拠を元 FrameCall.callee に入れ、未実行 suffix `form Delay(P); assemble challenge; receive/enter; return/consumer/future` を保つ。callee が Request ならその actual handle に suffix を一度だけ Bind する。まだ argument carrier、receipt、callee の Return は作らない。
2. **actual CalRet。** E が本当に返した v,r,w を original Call の callee-result slot に入れる。binding の別 provider に差し替えない。F の certificate は同じ Return projection から得る。
3. **Delay/challenge。** P の元 reify/license と captures を current w で使って inert carrier c を作る。P の実行はまだ行わない。独立 context と c の typing から元 D_F の same whole challenge d を構成する。actual acceptance を d の形成条件に入れない。
4. **receiver。** 完成した同じ v の F membership の admission clause により、その actual decomposition U_v が c を受け取る。observation clause は全 P_F(d) と、その same r/c/receipt/entry/body/consumer/result/future を供給する。現在状態の guard と各 response を保持する。
5. **pending/Return。** receiver が Request ならその raw handle と残りの元 suffix。Return の時だけその actual result/provider/current world を次の Bind へ渡す。callee phase や既に行った receipt を resume で再実行しない。

証明。Call の原実行式を callee phase と receiver phase に反転する。前半は E の仮定、後半は同じ actual Function membership の独立 challenge への elimination。接合 middle は CalRet(v,r,w) そのものである。Call/Bind の Request 式

`Request(q,w,k) >>= S = Request(q,w,(a,w′). k(a,w′) >>= S)`

を各 phase に適用すると、任意の有限 response/resume prefix で同じ順序を保つ。whole IF injection はこれらと同じ dependent tuple を使う。provider ごとの marginal を別々に選び直していない。完了しない prefix の suffix は関数として保持されるので、Return を仮定する必要はない。□

FO1 は元 contextual Function membership の本来の量化を使う。証明に Name lookup の inversion が必要なのは E が実際に Name の case だけであり、一般 E にその inversion を適用しない。任意の F の安全性を新たに仮定する補題でもない。以下では F_U/G_U を TU3、succ をその元 primitive 契約が供給する。

## 4. 観測 graph 全体への同時帰納

### 定理 FO2（明示した whole-carrier checking の下での有限合成）

§2 の有限導出に、各 Call edge e について実際の finite source checking proof χ_e を添える。χ_e は、その同じ argument code/capture/source origin の inert license と全 designated execution interface から、選択された受け手の I_F への whole-carrier inclusion を構成する証拠である。returned endpoint の inclusion だけではない。全 effects、requests、raw responses/continuations、current-world guards、independent arms、latent/future fields を同じ元 tuple で運び、合法 restriction に従う。元 source §3.2 の同じ計算に対する checking constructor による実証拠を要求し、成功した native query や空の schema を χ_e としない。

この χ_e family と元の独立入力の下で、source が生成する全 finite observations の phase 証拠、actual typed Return projections、全 suspended suffix/future functions を構成できる。computed next value を呼び出す時の callee/provider は、その同じ選択結果である。

証明。finite client graph の依存順序に沿って constructor functions を作る。各関数内部の raw prefix については有限 phase derivation に帰納する。client graph の有限性と、元 recursive f/G の全未来を扱う TU3 の coinduction は別々である。

* **Root / aliases。** Root Name は元 r_f の完成した F_U certificate。alias Name はその alias の actual Bind Return certificate。scope/current-world restriction は同じ immutable binding 上で行う。native freshened row を新しい runtime root にしない。
* **ground / succ。** Literal/true の原 primitive evidence、TU1 の Union injection。First は後述。succ callee は本当の Name なので、Int argument の全 checking と元 primitive contractから GC/ReadInvoke と FO1 を適用できる。original effects/arms を printed Int→Int から推測しない。
* **G=Call(Root,Record argument)。** P の帰納結果は carrier 内で指定 Force が実行された場合の証拠として使う。P の actual Return は U、Record depth により同じ value を field に持つ A。Record の returned A だけから inlet compatibility は出ない。この同じ carrier に χ_e を適用して全 checking を得た後、Root の F_U と FO1 を使い、TU3 の actual f Return は新しい gκ/root と G_U certificate を返す。Call prefix に fake result を置かない。
* **Qnode=Call(Gnode,P)。** Gnode が単なる Name でない場合も、その帰納証拠が actual CalRet(gκ,r_gκ,w) と genuine G_U certificate を与える。P の returned U と別に、その same-code carrier の χ_e を current event に適用する。その whole checking と同じ CalRet tuple で FO1 を使う。TU3 の receiver contract は元 h/recursive f/Record の全 phases を保持し、actual Return は Q の same fields を持つ。source prefix の Gnode を Name に書き換えていない。
* **Select first / next。** Qnode の計算と元 designated elimination を順に適用する。Qnode が Request なら selection は残り suffix。actual Return の同じ Record から first はその Int certificate、next はその actual gκ′/root/G_U certificate を選ぶ。next の selection 自体はその latent closure を呼ばない。後の Call node がこの returned provider を使う。
* **Aggregate / fan-out。** 元 field order の Bind で各 child を実行する。前の child の actual fields を後の current world に合法 restriction して Record に入れる。fan-out では元 alias の一度の Returnを複数回読み、computed source式の二回実行と混同しない。全 required output checking は独立 source checking proof がある場合、その同じ returned tupleに適用する。

各 case の Request は FO1 の Bind 式で未実行 suffix だけを追加する。任意の合法 response/current world を受け取る関数を構成しているため、各 prefix ごとに異なる証人を選ばない。全 local formation/profile は PF の同じ whole packet maps、独立 arms はその元 law のまま。これで有限 depth/branching と全 raw finite developments の両帰納を尽くす。□

これは明示した χ_e family の下で `next` を有限回なら任意にたどれる source supplier である。χ_e family の一般構成をこの定理自身が与えたとはしない。g の内部再帰 f は新しい closure を返し、source 観測 graph の次の Call がその closure を使う。returning g と invoking g を同一視せず、source 全体の停止性をここから導かない。

## 5. native 比較へ与える情報

native 側の Root/App/Sel/Record node に、本稿の同じ original source constructor と full interface を添えることができる。Call の actual callee slot、入力の指定 Force、next の selected actual provider、first の actual Int projection は FO2 が構成した証拠で埋まる。native type inference は body の実行前に比較を発行するので、対応は実行順の一 trace ではなく、これらの全 independently compatible events を index とする proof family である。

全 source client inputs は U に入る。native の `p≤τ`、source の U membership、native model の Top は別々の主張である。P1 の Top を source U の意味と同一視しない。native reverse repair の「新 endpoint が旧 endpoint 以下」から、任意の full source Function/permission/result inclusion を引き出さない。

## 6. 元の complete source result へ残る一箇所

FO2 は χ_e family が供給された場合、computed callee の actual prefix/Return、same-provider admission、receiver 全 P_F、pending/future、source IF の whole middle を供給する。従って「callee が Name でないため、actual returned provider の証拠がない」という前提は、この有限 client envelope では取り除ける。

一方、元の complete Call result `R_c` と観測 O に対する最終判断

`DescMem(R_c,O,w;ξ)`

の constructor は区別する。[選択済み pure-read result](../design/2026-10-08-pure-read-call-result-constructor.md) §4 は **structural Name callee に限って** R_c=ReadInvoke を定義している。FO1 の computed callee prefix をその Name-only prefix に押し込める規則はない。source Bind/constructor-image grammar が phase contracts を合成できることと、任意の独立 R_c がその合成を意味することも別である。

従って本稿は computed route の元 result descriptor まで含む全 `CIncl`/`TypedCallCert` を宣言しない。そこへ戻す残項の一つは、元の result endpoint formation が、この actual callee/receiver の staged composite contract をどの admitted constructor で表すかを構成し、その same-tuple interpretation を証明すること。もし実際の既定 R_c がその composite constructor なら、FO1/FO2 の各 phase をその definition に入れることで最後の judgment を得られる。既定 constructor の存在自体をここでは仮定して閉鎖扱いにしない。

この残項は source の raw operational bridge 全体の欠落ではない。FO2 は新しい complete descriptor 意味論を選ばずに原 Call/Bind rules から構成した結果である。native 稿の MonoBind は実 `App(Lam(a,body),value)` を用いる。本稿の source Bind alias とそれが同じ complete observations を持つという Lambda/Bind 対応も、この phase 証明だけでは主張しない。ordinary let の Generalize/freshening 対応、intrusion T/Y の actual receiving qualification、任意 client の principal coverage、full source termination は元の親義務として保持する。

## 7. 固定入力と receipt

契約 [FINITE-NEXT-COVERAGE](../../tasks/agent-loop/sprints/finite-next-coverage-20261024.md)、SHA-256 `518bc12e5f09ad83e5ec1e2af6d96c512959ec056726e7766188fd3c33a29feb`。TU/PF/GC と元 source checking、一般 FrameCall、receiver phase theorem、Name-only result authority を直接使用した。数学的 constructor/finite-prefix 帰納と静的 source 読取りのみ。実装変更・tests/build/compiler run はない。独立査読範囲は outcome に記録する。

## 8. 独立査読による訂正

査読入力 SHA-256 `fc25c7a637668e1a899a0678b5518f45f61613df46cdd66d8d4a58f972dabead`。査読は FO1 と、whole-carrier premise が実際にある場合の FO2 合成を受理した。元稿の「returned U/A から full argument checking まで供給した」という適用は MAJOR 指摘により撤回した。ここではその χ_e を明示し、構成済みとは主張しない。この訂正は新たな χ_e 証明の認証ではない。

分離例は、Int を返すが I_U/I_A の許さない Request を持つ独立 primitive contract である。returned-value inclusion は成立しても、同じ code の whole-carrier inclusion は成立しない。これは frozen builtin succ に実際にその効果があるという指摘ではない。literal/immutable pure data の個別 χ_e は TU1 の全 Return/Delay 構成から得られるが、一般 succ/first/computed P の χ_e までそれで埋めない。

したがって次の source 義務は、各実 argument-forming constructor の complete observation interface と受け手の inlet を比較する元 checking proof の構成である。その source judgment が偽の client を型付き扱いにはしない。原全 source theorem と、native coverage の固定 grammar は変更しない。今回の査読・訂正は [outcome](../../tasks/agent-loop/sprints/finite-next-coverage-20261024-outcome.md) に記録する。
