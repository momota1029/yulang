# Computed Call の生成記述と元の結果欄の対応

LET-POLAR-RESULT-SLOT-20261024/r1。著者 `/root`。独立査読前。

本稿は、選択済み [EI constructor](../design/2026-10-24-computed-call-result-constructor.md) を元 Call の静的形成へ適用する構成を与える。結果は **元の結果欄を保持する、定義された complete computation view** である。独立な `Comp(E,A)` と EI の等式を仮定せず、ordinary value row を complete computation descriptor に変更しない。

## 1. 実際の owning rules と区別する三つの対象

[Source generation G](../progress/2026-10-06-source-call-generation-construction.md) §§3,5 の Application は、元 `I(c)=Computation(E_c,A_c)` と

```text
CIncl(ExecuteCallableImage(J_f,Delay(J_a),F_c,e;ξ),
      Comp(E_c,A_c);ξ,e_result)
```

を保持する。G の適用範囲は同稿の decorated rule envelope であり、全 frontend がこれを発行済みという意味ではない。[SG](2026-10-08-source-generalize-definition-and-proof.md) §§3.1–3.3,4 は、実 Call の元 operands、source checking、owner/dependency records と、各規則の有限 program construction を与える。[IF](2026-10-08-call-source-interface-construction.md) §§4–5 の Application は、この Call の実 return/future slots、元 symbolic result/check origins、actual CalRet の ResultBind telescope を形成する。

従って区別すべき対象は次の三つである。

| 対象 | sort / owner / 意味 |
| --- | --- |
| `E_c,A_c` と既存 `Comp(E_c,A_c)` | 元 source synthesis/checking の endpoints と独立解釈。既存 annotation の target を含む。 |
| `IF_c.return` と `IF_c.future` | 元 Call の actual result/provider/current world と、その provider に依存する future の incidence slots。membership の証明ではない。 |
| `R_c^EI` | EI-Form / EI-All-Form により構成する complete computation descriptor。元 Call の全 phase tuple に対する新しく選択済みの view。 |

以下は、この三つを明示した同一の source occurrence に結び付ける。`Comp(E_c,A_c)=R_c^EI` という第四の前提を追加しない。

## 2. 静的生成手続き

入力は、元の有限 source/rule graph、その binder tree と実 Application inventory である。各対象 Call c について、次がその元 owning rules により well-formed であることを要求する。

1. callee の complete computation interface `C_f` と Return interface `A_f`。名前または登録された参照でもよい。
2. 元 complete checked Function `F_c`、その独立 `D_c,I_c,P_c`。F_c は未解決の型付き変数でもよい。
3. 元 inert argument code/capture/origin と license/checking **obligation** の形成欄。
4. 元 IF の ordered frame、全 source/arm slots と各 arm の complete descriptor formation。

これらは EI-Form の静的 operand premises であり、callee membership、argument checking の真理、whole Call typing、Q success は入力ではない。opaque な新しい constructor の sort が未宣言なら、この生成の instance はまだ得られない。

**構成 `DefineResultView(c)`。** 次の操作を同時に行う。

(a) c の元 source address に `complete-result-view` という静的 constructor label を付け、q_c とする。同じ occurrence は同じ label を参照し、別 occurrence は別 label を持つ。q_c は新しい型未知数でも runtime provider でもない。既存の result-check address はそのまま別 field に保持する。

(b) IF の元 CalRet/ResultBind binder を b とし、その内側に元 ArgumentFormationSchema を置く。c,d,receipt,response,future の各 binders は EI の元の位置に保持する。外側への witness の持ち上げは行わない。

(c) EI-Form に operands を入れ、

```text
R_c^EI := EvalInvoke(C_f,F_c,D_c,A_c^form,IF_c)
```

を形成する。whole-Call independent arms がある場合は EI-All-Form の同じ元 tags と complete arm descriptors で全 result case を形成する。`A_c^form` は argument formation schema であり、元 result endpoint A_c ではない。

(d) 元 source description region に `ViewLogic(C,q_c,σ_c,Δ_c)` の owning record を置く。ここで σ_c はこの Application の元 description scope、Δ_c はそこで利用できる上記静的 operands の依存 telescope である。q_c の payload は (c) の **定義された式**。新しい ordinary flexible `Desc`、自由な witness 選択、別の入場許可を導入しない。SG の logical interface-description record をこの既に選択済み EI case に適用している。

(e) q_c の result/future fields は IF_c の **同じ** return/future slots を参照する。元 `E_c,A_c`、CIncl address、original guards、独立な receipt/profile obligations を元の場所に残す。

この手続きは EI の constructor を元 source rule の実 operand fields へ適用する静的構成である。元 scalar solver の row を再分類する手続きでも、IF incidence だけから descriptor を得る規則でもない。descriptor formation の供給元は明記した EI-Form である。

## 3. 形成、スコープ、有限性

**GR1（typed result-view construction）。** §2 の任意の有限 Application inventory から、全 q_c と R_c^EI を execution 前に構成できる。R_c^EI は元 σ_c,Δ_c における CompleteComputationDescriptor であり、内側 event の値を自由変数として漏出させない。全 registered references、共有 operands、元 constraints は保持される。

**証明。** まず全 source occurrence と既存の登録 root を列挙し、q_c の labels と typed reference destinations を確保する。各 label は同じ有限 graph の address に constructor tag を添えたものなので、一意で有限である。これは未証明の recursive descriptor membership を登録する操作ではない。

次に、各 c で元 child frames と IF の Call construction を使う。C_f,F_c,D_c と各 arm の sort は入力の formation derivation が与える。ArgumentFormationSchema の依存は元 b:CalRet の下にあり、その中の c,d,receipt 等はそれぞれ元の内側 binder に属する。EI-Form の結論は complete computation sort なので、IF の slot をその sort と推測する必要はない。

自由依存の計算を明示すると、R_c^EI の FV は、その constructor operands の FV の合併から、その各 operand を包む元 b/carrier/challenge/response/future binders を除いたものである。元 operand が well-scoped なので、残る全 FV は Δ_c に属する。後に選ばれる actual CalRet や response の値は bound occurrence であり、σ_c の descriptor のパラメーターにならない。静的 F_c が open である場合は元の同じ declaration を参照し、その introduction より外へ移動しない。

EI-All の各 arm でも、その arm 自身の binder を使って同じ計算を行う。別 arm の provider を source branch の provider と同一視しない。既存 recursive references は登録済み complete interfaces を参照し、cycle を unfold しない。q_c を指す新しい未認証 recursive membership は生成しない。従って有限 graph の二回の traversal で構成が終わる。

最後に SG の ViewLogic owning rule を元 description region に適用する。(e) は既存 references を格納するだけなので、新しい flexible coordinate も旧 constraint の削除もない。□

**GR2（whole substitution と共有）。** 元 source graph の任意の legal whole substitution/restriction θ に対して、`DefineResultView(c)[θ]` と `DefineResultView(c[θ])` は一貫した bound-label renaming を除き同じである。同じ q_c を読む aliases は同じ定義を読む。

**証明。** label は source occurrence の元 transport と一緒に移す。F_c、C_f、argument captures、IF と全 arms に θ を一度ずつ適用する。EI の各 constructor と元 Ref が substitution を構造的に保つため、その組み立てと θ は可換する。event binder の下では θ をその binder に沿って弱化し、自由な未来 witness を追加しない。shared source field は最初から一つの reference なので、二つの読出しで別値を選べない。有限 recursive graph では各 node の同じ substitution を保持した辺同士を対応させればよく、無限展開による帰納は用いない。□

この定理は lawful freshening の追加 evidence にはなるが、native `freshenAbove` が q_c/Δ_c を既に保持するという命題ではない。

## 4. 実 tuple と結果 field の一致

**GR3（result/future correspondence）。** 元 Call の任意の actual observation O において、R_c^EI の result field が存在するのは、元 Call が同じ result を実際に Return した時である。その時、元 IF_c.return と EI result が指す値・provider・current world は同じであり、future index も同じである。callee の途中や receiver Request に result を捏造しない。

**証明。** EI の stage に場合分けする。callee phase は C_f の現在の prefix と suspended suffix のみで、whole-Call result はない。CalRet は actual callee value を b に束縛するものであり、whole-Call result slot へは入れない。Delay/receipt/entry の各 phase もその元 slots だけを持つ。receiver の actual invocation Return に到達して初めて、EI §3.3 と IF の return map が同一の元 triple `(v,r,C')` を result に入れる。future は両側ともこの triple の provider/current world を index にする。

Request は元 raw handle と current response telescope を保持し、未実行 suffix だけを接続する。callee Request の suffix は argument formation を含み、receiver Request の suffix は完了済み callee/receipt を含まない。従って resumed Return でも同じ triple を共有し、過去の receipt を繰り返さない。whole-Call arm ではその同じ arm tag の actual output map を使用する。図式の両辺は同じ slot の projection なので可換する。□

GR3 は実 tuples の一致である。provider の型所属がこの一致だけから得られるわけではない。

## 5. 元 source 証明からの導入と target の保持

`Inputs_c` を EI-Intro の genuine child judgments、same-provider F checking、whole-carrier checking、独立 challenge/guard evidence の package とする。これは Call の result typing や完成した TypedCallCert を含まない。全 alternatives を扱う時は元 independent arm-local laws も加える。

**GR4（元 Call における定義 view の導入）。** 任意の `Inputs_c` と元 `M_E(c,O,w;ξ)` derivation に対し、GR1 の **実際に構成した** q_c における

```text
DescMem(R_c^EI,O,w;ξ)
```

を構成できる。実行 graph、witness、current world、independent challenge domain は元のままである。

**証明。** GR1 が EI-Form/All-Form の具体的 instance とその元 source/binder location を供給する。EI-Intro に Inputs_c と元 derivation を渡す。GR3 により、その証拠の result/future fields は別 Call のものではなく q_c に格納された同じ元 slots である。whole-Call arms は同じ arm-local law を同じ tag に入れる。GR2 と EI-Intro の lawful action により、全 admitted future/restriction に同じ構成を使える。□

この段階で、旧 CB2/CB3 の「generated descriptor の sort と scope が許すなら」という留保は、§2 のこの source construction について GR1 の結論へ置き換わる。旧 `Comp(E_c,A_c)` に関する inclusion は別のままである。

**GR5（固定 target への正確な適用）。** 元 source derivation が同じ actual Call image から元 `R_target=Comp(E_c,A_c)` への genuine checking derivation k_c を持つなら、GR4 の evidence と k_c の evidence を同じ O,w,ξ に対して同時に構成できる。逆に、GR4 の evidence だけではその target checking は得られない。

**証明。** 元 image derivation を δ とする。GR4(Inputs_c,δ) と k_c(δ) を同じ tuple に対して pair にする。k_c は SG の finite checking derivation であり、任意の extensional inclusion oracle ではない。q_c や EI の定義を消去しても k_c と元 result/check origins は残る。証拠を足す操作は code/receipt/guards を変更しない。

特に `Image_c ⊆ EI_c` と `Image_c ⊆ R_target` から `EI_c ⊆ R_target` は従わない。EI は arbitrary compatible callee/carrier/provider observations を保持し、特定の source image と等しく定義されていないからである。従って元 CIncl を `CIncl(EI_c,R_target)` に置換することも、EI の導入だけで CIncl を削除することも、この証明では許されない。□

**GR6（証明の定義拡張）。** 上の finite source proof envelope に q_c と GR4/GR5 の derived views を付加し、元全 constraints をそのまま保持した proof representation と、その元 representation の間には、合法な **元 proof objects** の存在を保つ extension/erasure がある。

extension は全 genuine local source derivations に GR1/GR4 を適用して定義式とその derived evidence を付ける。erasure は付加した定義 view だけを除き、元 proof/constraints を返す。erasure∘extension は元 proof をそのまま返す。extension∘erasure は canonical に付加した representations に限り同じである。非 canonical proof witnesses の一意性や全 constraint solutions の意味的一致は主張しない。外部 binder/共有 evidence/actual runtime choices は両方向で同一なので、view を足す際に strategy の量化順を変えていない。これで証明済み source の正当な view extension としての適用を閉じる。

## 6. 既存結果への適用と残項

checked immutable Name C_Read(F,n) の場合、生成した R_c^EI は EI-Name により元 ReadInvoke と全 fields を保って相互変換できる。GC の同じ元 result/check address を保つ。計算した callee については CA/CB の genuine inputs が与える範囲で GR4 を適用でき、generated complete result view の sort/scope は追加仮定ではなく GR1 が供給する。

この成果は元 `Comp(E_c,A_c)` の全包含証明、genuine operand laws の自動発見、actual native solver の encoding を供給しない。CA の未証明な succ/arm inclusion、original actual inference の成功からの source proof、receiving/SCC qualification、全局所一般化・主型性・停止性は残る。

とくに、元 G の scalar-looking endpoint 表記を見ただけで EI が代入可能とする旧候補は採らない。実 source constructor で complete view を形成し、その元 result slot との incidence と actual tuple の一致までを証明した。未知の solver がその complete view を保持・消費することは別の conformance obligation である。

## 7. Freeze / review seam

契約 [LET-POLAR-RESULT-SLOT](../../tasks/agent-loop/sprints/let-polar-result-slot-20261024.md)、SHA-256 `f9866914a67be89a28e1e42114d81935b9cd0f97ab8d2be5d6033ecc7ae9d1b9`。構成は source mathematics のみ。新 raw syntax、既存 target の再解釈、production 変更はない。GR1 の owning record と scope、GR3 の actual field equality、GR5 の inclusion の向き、GR6 の proof-object に限る量化が fresh independent review の対象である。全体閉鎖を宣言しない。

## 独立査読記録

`/root/astra_semantics_review` による current80sec の独立査読は、本稿の明記した範囲で BLOCKING/MAJOR なし。査読対象 SHA-256 `60b03af7dbf3e019a1d0601473b9f6cabb36f48780d757323a7275df45347fba`。数学本文は変更せず、この receipt のみを追加した。全 Let theorem、元全 target inclusion、全 source/native 対応は未完。[統合記録](../../tasks/agent-loop/sprints/let-polar-result-slot-20261024-outcome.md)に正確な受理範囲と残項を保持する。
