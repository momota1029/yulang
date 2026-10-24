# Signed client updates と extrusion の段階合成

SIGNED-EXTRUSION-CORRIDOR-20261024/r1。著者 `/root`。独立査読前。

本稿は、個別 client を増やす代わりに、任意有限 nonrecursive-Let client の全 native updates に関する不変条件と、二段 extrusion から一段 extrusion へのモデル輸送を構成する。一般 LET-POLAR-PUB 全体は最後に残る対応を必要とする。

## 1. 原対象と記法

原 [LF](2026-10-24-let-free-client-reverse-coverage.md) の f prepublication store、P1 regular-tree structural preorder、unique-label Record domain と固定 external/output contracts を使う。source grammar に任意の有限 nonrecursive Let を加える。全 lexical caller levels は1以上、元 anchors H,C,D,T はlevel1。全実 `constrain/extrude/freshenAbove` は pinned Typer.scala のまま。Let は RHS をlevel+1で推論し、body は元levelへ戻る。recursive f の元 store は既に形成済みの入力であり、新しい client LetRec はこの定理の対象ではない。

row の証明用 color を P,N,Z とする。元 o,J,R はP、B,Y はN、H,C,D,T と全通常 client allocations/builtin if rows はZ。freshening と extrusion の新 row は actual parent の color を継承する。これは型、source owner、SCC や実装 field の変更ではなく、実 allocation derivation 上の帰納的 annotation である。高い/低いという分類とは独立である。

構造項の二つの文法を相互に定義する。

```text
Pos ::= Primitive | Z-row | P-row | Function(Neg,Pos) | Record(Pos fields)
Neg ::= Primitive | Z-row | N-row | Function(Pos,Neg) | Record(Neg fields)
```

Z-only の構造型は両方に属する。P-row は Neg でなく、N-row は Pos でない。membership は有限の構造項について判断し、変数の bounds をその場で unfold しない。

store invariant S は次の通り。

```text
P-row: 全 lower payload が Pos。upper list の文法には制限を置かない。
N-row: 全 upper payload が Neg。lower list の文法には制限を置かない。
Z-row: 全 lower payload が Pos、全 upper payload が Neg。
```

この非対称性が元 f の内部相関を保持する。たとえば o.upper の Function(Record(Y),R) と B.lower の Record(Y) を消さず、Pos/Neg と偽って分類しない。

## 2. SU1: signed extrusion と全 bound の保存

**SU1。** S を満たす finite store で、`extrude(t,+,k)` の t がPos、または `extrude(t,-,k)` の t がNegなら、全実 writes は S を保ち、返却項はそれぞれPos/Negである。P-row は positive key でしか、N-row は negative key でしかこの traversal に現れない。Z-row は両方で現れてよい。

**証明。** Function の domain では文法と native polarity がともに反転し、result/Record はともに保持する。低level early return と Primitive は文法を変えない。

positive P の miss はP-copyを作り、parent.upperへP-copyを入れる。この list は S で制限しない。copy.lower は元 Pos lower payload を同じpositiveで運んだものなのでPos。negative N は対称に、無制限な parent.lower にN-copyを入れ、Neg upper payload をnegativeでコピーする。反対 polarity のP/N keyは、相互文法の variable case から到達できない。

positive Z では parent.upper に入れるZ-copyはNegにも属し、copy.lower はPos。negative Z では parent.lowerのZ-copyがPosで、copy.upperはNeg。copy の反対 list は初期に空である。

各 key は selected-list recursion 前に memo 登録される。相反する polarity が途中で同じZ親に加えた link はZ-rowなのでPos/Neg両方に属する。selected list がこの新 entry を読む場合も同じ検査が成立する。memo hit は同じ color の既登録copyを読む。よって実 finite evaluation events への同時帰納で、書込み中の全 store と返却項を同時に保つ。旧 clause は全て残る。□

## 3. SU2: 全 client comparisons と freshening

**SU2。** S の下で `constrain(s,t)` がPos≤Negなら、その全実再帰 requestsもPos≤Negであり、全 writes はSを保つ。成功・cache return・型エラーのいずれで終わる finite prefixにも成立する。

**証明。** Function comparison では s=Function(n,p)、t=Function(p',n') なので child comparisons は p'≤n と p≤n'。Record の同名field比較もPos≤Neg。missing field/異種headの場合は失敗するが新しい誤分類を作らない。identity/cache returnは書込みをしない。

lhs Variable branch ではlhsはPまたはZだけである。upperへのNeg追加は許され、opposite lower listはSにより全Posなので各replayがPos≤Neg。rhs Variable branchではrhsはNまたはZだけで、lowerへのPos追加とNeg upperへのreplayが同様に成立する。**実コードが lhs Variable branch を先に選ぶことを保持する。** 同じvar-var comparisonを両側のlistへ挿入するとは仮定しない。

level mismatchでは、lhs Variable側はNeg rhsをnegative extrusionし、rhs Variable側はPos lhsをpositive extrusionする。SU1がSと正しい返却文法を与えるので、rewritten requestもPos≤Neg。以上で全分岐を尽くす。□

**SU3（both-list freshening）。** S の下で任意の実 `freshenAbove(b,t)` を行い、各cloneが元rowのcolorを継承すればSは保たれる。tがPos/Negなら返却項も同じ文法に属する。

**証明。** 高いrowは両listをコピーするが、各payload内の構造は変わらず、参照先rowのcolorも同じである。従ってPのlower、Nのupper、Zの両listの要求は各cloneで保存される。制限していないP.upper/N.lowerも丸ごとコピーする。低rowは同じobjectで止まり、memoは一つの元rowを一つの同color cloneへ送る。bound cycleは事前登録memoを参照し、Pos/Neg判断のために無限展開しない。□

**SU4（全有限 nonrecursive-Let clients）。** §1の任意の実有限 client inference prefixについてSが成立し、各完成subexpressionのresultはPos、全client-generated comparisonsはPos≤Negである。全 publication boundariesでSU3を適用できる。

**証明。** 元 store を検査する。Pのlowerは o:Function(B,Function(Y,Record(J,R)))、J:D、R:Function(Y,Record(J,R)) で全てPos。NのupperはB:C、Y:TでNeg。Zの非空listsはH.upper=Function(C,D)、C.lower=Record(T)でそれぞれNeg/Pos。その他は空。元 constraints を全て保持してSが成立する。

source syntaxとnative writesへの同時帰納を行う。通常formal/App/Sel rowsは空listのZ。Var fはPos root oのSU3 instance、他の既存schemeもPos rootをfreshenする。monomorphic formalはZ。Literalは両文法。LambdaはFunction(Z,Pos)でPos、RecordはPos fields。AppはPos callee≤Function(Pos argument,Z result)というPos≤Neg seed、SelはPos≤Record(Z result)。SU2を適用し、result Zを返す。

Let RHSはlevel+1でも同じ帰納仮定が適用される。その実Pos rootと全storeを元boundaryで保存する。bodyの各resolved useはSU3なので、内側でlowだったrowを外側でfreshenする場合にも成立する。bodyは元levelの同じ帰納。aliases/capturesは同じreferencesを読み、fのshadowingは通常formal/schemeの場合に従う。外部の閉型または保持Z座標からなる型とbuiltin if schemeは両文法で、同じ議論を受ける。固定出力 upper contracts もNegなのでSU2の範囲に入る。□

この証明は「producerは正だから」と仮定したものではない。元fの反変B/Yを含む相互文法、片側の可変lists、実branch orderと両listのfresheningを同時に検査した。

## 4. SU5: 消える Y 系コピーへの upper update はない

Y-rowという追加の系譜注釈を、元Y、そのactual f freshening clone、さらにそのextrusion/freshening descendantsに付ける。B系とは区別する。

**SU5。** §1の全client prefixesで、各Y-rowはNであり、そのupper listは元共有Tを一つ持つ元listの同じコピーである。clientから別の upper payload を追加されない。全B-rowについても共有Cで同じ命題が成立する。

**証明。** 初期Y.upper=[T]、B.upper=[C]。SU2の新upper insertionはPos lhs、すなわちP/Zにしか行われないため、Nのupperを書き換えない。SU1ではNをnegativeにしかextrudeせず、parentにはlower linkだけを加える。新Y-copyのupperは[T]のnegative extrusionだが、全target levels≥1かつT.level=1なのでTでearly returnする。B/Cも同じ。

freshening boundaryも全て1以上なのでT/Cはコピーされない。SU3の新Y/B cloneが同じ一要素upper listを持つ。通常source allocationはZでありY/B注釈を新造しない。これで全write constructorsを尽くす。□

従ってLPで残っていた「disappearing yに後着 upper y≤Uが入り、τ≤Uを別途要する」という具体的危険は、この **全finite nonrecursive-Let client domain** では起こらない。native推論が意味論上の全推移的upperをlistへ記録するわけではなく、ここでの命題はactual listsについてである。Yのlower、Pのupper、Zの両listには任意の正当なclient constraintsが依然として残る。Sだけでそれらの全joint model repairはまだ得られない。

## 5. EC1: extrusion の二段合成から一段へのモデル

ここからは固定fに限らない一般補題である。finite store Σが元NLのlevel invariant（各bound leaf.level≤owner.level）を満たすとする。任意のfinite structure term t、polarity ε、levels k₂<k₁を取り、元nativeを次の二通りで実行する。各callのpolar memoは新規で、途中に他の処理を挟まない。

```text
staged: Σ ─extrude(t,ε,k₁)→ Σ₁,t₁ ─extrude(t₁,ε,k₂)→ Σ₁₂,t₂
single: Σ ─extrude(t,ε,k₂)→ Σ₂,t_D
```

それぞれの新allocation identitiesはdisjointな名前を使う。元rowsは共通。局所extrusionのfinite completionは、有限な元rowsのpolar keysと、target以下の新copiesでearly returnすることから従う。

**EC1。** Σ₁₂の任意のP1 model ρから、Σ₂のmodel ρ_Dを構成できる。全元rowsの値を保持し、`⟦t_D⟧ρ_D=⟦t₂⟧ρ`。全single parent linksとselected boundsを満たす。ρの存在を結論として仮定し直すのではなく、その各copy値を以下で明示する。

### 5.1 canonical maps と key の存在

singleの各key(a,σ)に対し、a.level>k₁なら第一callのそのkeyのcopyをa₁^σとし、第二callのkey(a₁^σ,σ)のcopyをc(a,σ)とする。k₂<a.level≤k₁なら、第二callのkey(a,σ)のcopyをc(a,σ)とする。a.level≤k₂の項は元aのまま。

これらのkeyが存在することを示す。singleの到達keyは、input tのsigned occurrenceから、wrong-level rowの**元 selected bounds**を同じsignで辿る有限closureである。call内で新しくparentに加わるentryはtarget-level copy一個なので、それを読んでもearly returnし、新しい元keyを追加しない。

この到達pathがlevel>k₁の元rowsを辿る間、第一callは同じsigned keysを登録し、元boundを第一copyのselected listへ運ぶ。第二callはそのcopyの同じsignからその運ばれたboundを辿る。pathが初めてlevel≤k₁の元rowへ入った後は、NLによりその元boundsからlevel>k₁へ戻らない。その区間は第二callが元rowsを直接辿る。従ってsingleの全keysに上記cが存在する。memo再訪は同じkeyを使うので選択は一意である。

定義するmodelは

```text
ρ_D(a)=ρ(a)                       (全元rows)
ρ_D(single-copy(a,σ))=ρ(c(a,σ)).
```

同じsingle memo keyを別の値へ送らない。

### 5.2 全 clauses の検査

任意のcompleted extrusionの元term uと返却u'について、positiveなら`⟦u⟧≤⟦u'⟧`、negativeなら逆向きである。これはwhole boundsを展開せず、structure inductionとvariableのactual parent linkから従う。Functionではdomainのsignを反転する。

従ってpositive keyのsingle親linkは

`ρ(a)≤ρ(a₁^+)≤ρ(c(a,+))`

で満たされ、negativeは逆向き。第一callがaでearly returnした場合は一段の同じ不等式でよい。

singleがコピーするselected entryが元Σのpayload lなら、staged側にもその同じpayloadを二段で運んだentryが残る。元term lの構造各leafについて、二段で運んだ先は§5.1のcなので、その最終termの解釈はsingleで運んだlのρ_D解釈と等しい。第一callがearly returnしたsubtermも第二callの同じkeyを使う。したがってstaged copyの当該selected inequalityが、single copyの必要なinequalityをそのまま与える。

single内のmutable listから読む**新 entry**は、同じ親aへ反対polarityが加えたsingle-copy(a,−)またはsingle-copy(a,+)である。これらの必要比較はnegative copy≤positive copyだけであり、上の親link列から

`ρ(c(a,−))≤ρ(a)≤ρ(c(a,+))`

が従う。したがって二段側が反対polarityの中間copyをさらに別keyでコピーしていても、そのcopyをsingle側へ同一視する必要はない。余分なstaged keysはρ内に残したままにする。

extrudeは元clausesを削除しないのでΣの全clausesは元値保持で成立する。新clausesはparent linksと上のselected entriesで尽くされる。t自体にはsingleで新しいlist entryから生じた項を挿入しないため、そのstructure leaf actionは全て§5.1のcで一致し、出力等式を得る。□

同level k₂=k₁なら第二callはt₁でearly returnするため、第一callとsingleを一貫して改名すれば同じ結論になる。これはnativeのmutable storesが同一という命題ではなく、stagedの全modelからsingleへ送る、old-value/outputを保持した構成である。

## 6. EC2: 間の公開境界と任意有限個の使用

k₂≤b<k₁を固定する。root rは元Σのrowsだけからなる任意のfinite structure termとする。Σ₁₂側とΣ₂側で、このrをboundary bで保存し、それぞれ任意有限個の実freshenAbove(b,r)を行う。両側で同じ各useのcaller levelを用い、これらのfresheningの間には別のconstrainやextrusionを挟まない。これは固定publication snapshotの補題であり、全client historyの代わりではない。

**EC2。** staged storeとその全fresh instancesを同時に満たすρから、single storeとその全instancesを満たす一つのρ_Dを構成できる。元rows、各useにおける対応する元rowのclone値、各rootの意味値を保持する。singleのlow copiesは全usesで同じc(a,σ)の値を共有する。stagedの中間copiesを各useで同じ値に強制しない。

**証明。** singleの新copyはlevel k₂≤bなのでfresheningで止まる。single側でfreshenされる元rowsは、rからΣの元boundsを辿って到達する高いrowsだけである。staged側もΣの全boundsを残すので、その各元rowに対応するcloneが同じuseのmemoに必ずある。stagedはさらに中間copyを辿って余分なrowsをcloneしてよい。

元rowのsingle cloneには、同useのstaged cloneのρ値を割り当てる。元Σからコピーしたboundsは同じ元rowsの同じclone referencesを持つため保存される。singleが元rowへ追加したparent linkの相手はlow copyなので固定値ρ(c(a,σ))である。

a.level>k₁のpositive caseでは、stagedのa cloneから第一copy a₁^+ のcloneへのlinkと、そのcloneからlow c(a,+)へのlinkがある。第一linkは第一call、第二linkは第二callの実parent.upper entryで、freshenAboveは**両listを残す**。従って`ρ(a_i)≤ρ((a₁^+)_i)≤ρ(c(a,+))`。negativeは`ρ(c(a,−))≤ρ((a₁^−)_i)≤ρ(a_i)`。k₂<a.level≤k₁の場合は第二callの直接linkをcloneするだけでよい。aがboundary以下ならcloneせずEC1を用いる。

single-copyの自身のselected boundsは全leafがlevel≤k₂なので新たにfreshenしない。これはEC1の同じρ_Dで既に成立する。以上で全保存clausesを満たす。root rの全元row occurrencesは同じclone値または同じlow元値を持つのでroot意味値は等しい。一つのρに含まれる全useへ同時にこの定義を行えば、共有lowは一つ、high clonesは各useの元値となる。□

従って、対応する元/clone coordinatesと出力rootに対する同じ追加制約は、その式を変更せずに保持できる。未対応の中間copyを直接外部座標として指定する制約は、この結論に紛れ込ませない。

## 7. actual replay corridor への適用と cache の境界

SU5により、client中のY-row yのupperは共有T。cache missした実 `constrain(L,y)` について場合分けする。

* Lがstructural Function/Recordでlevel(L)≤level(y)なら、rhs Variable branchがLをy.lowerへ入れ、同じstack内で`constrain(L,T)`を呼ぶ。after quotientの直接boundary requestと同じLである。
* structural Lがyより高ければ、まずpositive extrusion target level(y)を行い、そのL₁をyへ追加して`constrain(L₁,T)`を呼ぶ。L₁がTより高い場合は二段目のpositive extrusionになる。**途中で他の処理が介在せず同じ二段callに該当する場合**、EC1/EC2はこれをdirect target level(T)へ運ぶmodelを与える。実storeへのy.lower insertionなど、pure extrusion以外のclausesは別途保持すべき対象であり、EC1だけで消さない。
* LがVariableなら、lhs Variable branchが先に選ばれる場合がある。この場合はL.upperへyを入れてL.lowerをreplayし、単にL≤y≤Tというpathがあるだけでは`constrain(L,T)`が直ちに処理されたとは言えない。
* pair cache hitも新しいextrusionを行わない。以前の処理記録または現在のstack frameへの参照と、その時点のselected boundsを用いる必要がある。cache entryの存在を「最新snapshotを処理済み」と置き換えない。

`typeLetRhs(false)`は同期的に`typeTerm(rhs)`の返却を待ってからPolymorphicTypeを作る。従って成功したRHSでは、実際に呼ばれた各再帰処理のstackは戻っている。これは**呼ばれていないcomparisonの実行**や全最新boundsの再飽和を含意しない。fairnessを追加せず、この区別を保つ。

## 8. 元 parent に対する進展と残る合成

SU1–SU5は全finite nonrecursive-Let clientsを対象に、LPの未証明だったsigned update/both-list fresheningの不変条件を構成する。とくにY系の後着upperという候補障害を一般に排除する。nested publicationでlow/highが変わることはcolorを変えないため、LP2の例もこの帰納に含まれる。

EC1/EC2は任意のfinite NL storeと任意のpolar structure termについて、staged/direct extrusionと間のpublicationを一つのmodelで結ぶ。中間copiesの数や各fresh instanceの値を同一にする必要はない。これは個別clientのvaluation列挙ではない。

一般 LET-POLAR-PUBに残るのは、元の実interleaved source history全体でこれらを合成すること。具体的には、(i) Variable/cacheのpathを含む各実boundary demandの対応、(ii)間に入るbound insertionと全client-added constraints、(iii)Y.lowerだけからreachableだったsubgraphの公開前後の全作用、(iv)同じ共有anchorsを持つ全historyでの一つのmodel選択、である。EC2の固定snapshotをこの全historyへ無条件に拡張しない。source receiving/SCC資格、full source effects/provider証拠、原主型性・combined terminationも元の親として残る。

## 9. Freeze / checks

契約 [SIGNED-EXTRUSION-CORRIDOR](../../tasks/agent-loop/sprints/signed-extrusion-corridor-20261024.md)、SHA-256 `ae96542b551eadec58de58ac15643bc107e003355da9e37fdfe4b7c05a3dfa68`。Primary単著。旧producerは停止済みで本稿にwriteしていない。実native constructorsの静的読取りと紙上証明のみ。tests/build/probes/compiler/実装変更なし。fresh independent reviewは特にSU2のbranch順、SU3の両list、EC1のmutable cross-sign links、EC2のclone到達と共有low、§7のactual processing境界を検査する。

## 10. 独立査読

Current `/root/astra_semantics_review`100sec のfresh independent reviewは、SU1–SU5、EC1、固定snapshotにおけるEC2と§7の未完了境界を受理した。BLOCKING/MAJORなし。査読対象SHA-256 `72178ff2ff9c5a34cea0a47211023f51796ce59fd046fb59e56f418f00e030a0`。このreceipt以外の数学本文は同じである。全interleaved historyへの合成と元全親定理は未完。[固定版と査読範囲](../../tasks/agent-loop/sprints/signed-extrusion-corridor-20261024-outcome.md)に記録する。
