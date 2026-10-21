# Yulang 型推論・実行の証明編

## 型付き小核の健全性と、現実装の Capture・FreshUse・intrusion 保存定理

2026年10月21日

## 1 証明の結論と対象

**本書では、役割付きCall、遅延計算、厳格なlet、再帰関数、単相operation、浅いhandler、raw resumeを含む明示的な型付き小核について、型保存・進行・効果安全性を証明する。** さらに、現在のRust実装のreplayとCapture、scope transformer、極性付きコピー、intrusion後の共有、実行時のCall・request・continuationに対応する保存定理を証明する。

前の文書が与えた一般的な依存閉包・名前変更の補題だけで終わらず、どの実装分岐がどの帰納段階を実現するかまで示す。一方、これらを接続せずに「現行コンパイラ全体の健全性が証明された」とは扱わない。sourceの全構文から型付き導出を作る橋、generic operationの開封、一般のreceiving、主型被覆、solver全体の停止は、現在の定義と実装の未完箇所を含む。最終章に、完成した定理を再利用して残りを閉じる順序を固定する。

### 1.1 固定した対象と確認方法

対象は momota1029/yulang の research/simple-sub-intrusion、固定commit

5596b1598388f629f95a44ef203e4f760b615803

である。Yulang2 Oracleの比較基準は

a58eefc31e22141574b6f20c6a5748151c6d79f1

とする。本文の行番号とリンクはこの固定版を指す。異なるHEADの挙動まで推測しない。

本書の証明は、定義・帰納法・代数計算と固定コードの静的読解による**手証明**である。Lean、Coq等による機械検証済みの証明ではない。Rustのビルド、compiler fixture、Oracle実行を今回新たに行ったとは報告しない。実装・test expectation・研究の承認状態も変更していない。

この区別は証明の効力を曖昧にするためではない。数学的な核の定理はその定義に対して完結させ、実コードについての主張は検査した分岐と不変条件に限定する。資源確保失敗や未対応構文で停止するprivate機構の「成功遷移の保存」は、「型付けできる全sourceが必ず成功する」とは別である。

### 1.2 前文書のCapture診断を訂正する

前文書『Yulang 型推論の統合設計と証明計画』の第1章と実装段階1は、Captureの逆向き探索が省略可能なcompletion receiptに依存する点から、Capture修正を最優先の必須修正として述べた。**この優先順位の根拠は強すぎたため、本書で訂正する。**

実際の通常replayまで含めると、古いshared anchorから同年齢のlocal行へ伸びる有限identity-chainには、終点へのshortcutが必ず作られる。そのshortcutは通常のlower laneからCaptureされ、receiptの有無に依存しない。R244/R245の候補で使われた、anchorに効果がありfreshなreturnを空にする割当ては、このshortcutを満たさない。したがって、それを現行実装の不健全性の反例として用いることはできない。第3章でこの事実をコードに対応させて証明する。

元の辺の列挙が省かれ得るという観察自体と、意味的制約が失われるという結論は分ける必要がある。全incidenceによるCaptureは完全な構成を与える有力な選択肢だが、現在のCaptureを全面的に置き換えることが必須だと証明したわけではない。

もう一点、LocalSchemeとmodule useは使用のたびにlive rootから再Captureする。固定snapshotを永遠に複写する機構ではない。新しく作る使用への反映と、既に作った使用への後続制約の反映を分けて検証する。

### 1.3 完成した命題の一覧

| **命題** | **本書で証明する内容** | **適用範囲** |
| --- | --- | --- |
| 型付き小核の健全性 | preservation、progress、外向きeffect safety | 明記したrole・Delay/Force・浅いhandler等の小核 |
| replayからCaptureへの保存 | older anchorのfinite identity-chainがshortcutで捕捉・復元される | 同年齢local、identity/default flow、正常drain |
| scope/context輸送 | transformer合成とremapの全状態意味論、ordered DAG再構築 | 実装の成功grammarと明示した単射条件 |
| contextual Capture | 任意個の使用と任意のjoint clientに対する関係同型 | 完全な境界、元のbinder木、同時α観測 |
| ordinary extrusion消去 | 全retained parent/copy pairの消去が元のdemandとboundsへ戻る | ordinary row・Function skeleton |
| intrusionと一般化 | classがlocalであることと全memberがlocalであることの同値 | 現行min-level / non-generic ORとFreshUse |
| scope下降 | 過去のscopeへ移せる依存条件とwell-scopedな値域条件 | 明示したsemantic strategy |
| nonescape | 局所guardから、循環readbackを含む自由剛体名の非脱出 | 全更新が局所条件を保つdiscipline |
| runtimeの同一性 | actual Call、認証されたGrant、raw suffix、response/event保持 | 固定Rustの成功遷移 |

「小核の型安全性」「制約変換の保存」「主型性」「現コンパイラ全体の安全性」は同じ命題ではない。以後もこの四つを区別する。

### 1.4 元の設計条件を保つ

推論の骨格は、制約生成、蓄積、伝播、変数のlevel、extrusion、実Value参照SCCによるintrusion、一般化である。別候補を探索する推論器やrollbackを証明の結論に持ち込まない。Value SCCはresolved Name→Valueのグラフであり、型の上下界のSCCではない。具体的なoptional-record adaptationへ一般の推移律を追加しない。constructorにlevelを新設しない。[P01][P02]

存在開封のlevel guardは、生成時・比較時に働き、aliasとreplayから導出した比較も同じguardへ戻す。第6章のnonescape証明は、この局所的な方針から大域的な性質を導くものであり、必須のexit-time checkerや別の量化solverを加えるものではない。[P02]

Oracleの正常な受理例を削って定理を簡単にすることも行わない。本書の小核は証明が閉じた部分であり、今後のYulangの受理仕様をそこへ縮小する提案ではない。独立したproduction viewや将来のclientを、現在のsource imageだけへ制限してall-viewの定理を済ませることもない。[P03][P04]

### 1.5 読み方

第2章が型安全性そのものの証明、第3章が現行Capture・FreshUseの証明、第4章が任意の共同利用文脈への持ち上げ、第5章がextrusion/intrusion、第6章がnonescapeである。第7章は、これらを合成して元のYulang全体の命題を閉じるための、具体的な残りの接続を示す。

章内の補題名は各章に属する。コードの引用は事実の出典、数式の導出は本書内の証明である。既存研究の未閉鎖の定理を、名前を変えただけで完成済みに数えない。

#### 設計上の一次資料

- **P01** [推論の上位原則](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/design/2026-10-11-yulang-inference-top-level-principles.md)

- **P02** [SCC intrusion charter、§§22–23](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/design/2026-09-29-scc-intrusion-redesign-charter.md#L603-L645)

- **P03** [production proof architecture](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/design/2026-10-07-successor-production-proof-architecture.md)

- **P04** [原命題・量化順序・既存証明の引継ぎ](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/theory/2026-10-07-successor-pro-theorem-handoff.md)

## 2 Call・効果・浅いhandlerの型安全性

### 2.0 実際の評価順序

Yulang の Apply を、呼出し側で引数を先に評価する通常の CBV Apply と同一視できない。現行実装は callee を評価した後、**引数式全体を inert な Delay として作り、receiver activation を確立してから Value parameter の引数を force する**。Computation parameter は Delay を保持し、未使用なら引数を実行しない。これは machine.rs:662–674,910–1042 の実処理であり、既存の ordinary semantics の第3節 とも一致する。[S01][S02]

ただし通常の local binding は、initializer を実行して得た値を cell に保存する厳格な逐次実行である。したがって「引数が遅延される」ことを理由に、let initializer の効果を捨ててはならない。begin_local と Frame::Local がこの区別を実装している。[S03]

### 2.1 型付き小核の定義

#### 2.1.1 値、computation、effect の区別

値型を次で生成する。

$A,B::=1∣Int∣Bool∣String∣{U}_{ϵ}A∣{F}_{r}(A,{ϵ}_{a};B,{ϵ}_{b}).$

U_ε A は、実行すれば A を返し、効果 ε を持ち得る inert な computation value。F_r は一個の関数型であり、その四ポートは

$(AV,AE,RE,RV)=(A,{ϵ}_{a},{ϵ}_{b},B).$

r∈{Value,Comp} は元の parameter の役割で、実行結果の型や値の tag から後付けで選ばない。以下の return/force/thunk はソースに新設するキーワードではなく、既存の source role と consumer の導出を表示する記法である。[S02]

小核の環境は binder から actual value への有限写像、再帰閉包の場合はその有限 graph とする。型付き環境は各 binder の同じ actual value が割り当てられた型を持つこと。ここでは任意の mutable store 操作を primitive として追加しない。現在状態を渡すという記法は、closure creation 時の snapshot へ戻らないことを指定するものであり、未定義の store typing theorem を暗に輸入するものではない。

値と computation の構文を次とする。

v ::= x | literal | λ^r x.c | recfun^r f x.c | thunk c\
    | operation(ℓ) | request(ℓ,v)\
\
c ::= return v | force v\
    | let x ← c1 in c2\
    | call cf ca\
    | if v then c1 else c2\
    | catch h H c

recfun は自分の binder を参照する関数値を表す。再帰を無限に展開した構文を入力に取らない。operation(ℓ) の完全な型規則と、実行中に生じるcontinuationは§2.4以降で定める。一般的な mutable reference、Role/method adaptation、optional record、generic operation の existential opening は、この小核の新しい型付け場合としてはまだ証明していない。これらを Yulang の意味論から削除するものではない。

各 operation の宣言は op:A_op ⇒ B_op とする。A_op、B_op は単相だが、B_op は関数や computation を含んでよい。したがって operation-v1 の function-valued response を、単に primitive response に縮小していない。

#### 2.1.2 effect の粒度

数学上の effect ε は request label の集合とする。label ℓ は operation identity と、当該 contribution を区別する route を持つ。runtime の繰返し実行で生じる event identity は別であり、一つの label が任意個の新しい event を生成できる。

remove(ε,D) は集合 ε から D の要素を除いた集合を表す。

effect row の表示で family へ射影することはできる。しかし handler による除去を証明するときには、異なる route を同じ family の一要素へ潰さない。集合は数学的な仕様に用いる。これを新しい集合 solver として実装する要求ではない。

handler h は、実際に処理できる label の集合 D_h を持つ。ℓ∈D_h という証明には、operation の一致と、その**同じ contribution の、同じ受け手に対する処理許可**を含める。単なる nominal family の一致を D_h の証拠にはしない。型付き小核では、この label classification が型付けと実行で一致する。一般の Yulang source からこの classification を構成する証明は §2.16 の未接続事項である。

この一致条件は隠れた健全性仮定ではなく、対象小核の明示的な構文データの一致条件である。以下の型安全性定理は任意の classifier について成立するが、Yulang の正しい classifier であることまでは与えない。後半の実コード定理は、現行 runtime が実際に使用する positive classification の認証を別に閉じる。

#### 2.1.3 handler と raw continuation

handler H は、戻り値の節 return x ↦ c_v と、operation ごとの節 op(p,k) ↦ c_op を持つ。戻り値節を省略した場合は return x とする。payload の binder/wildcard と、宣言に対応する単相操作を扱う。一般の effectful pattern/guard は追加場合である。

k は選択された handler を外した **raw suffix**。型は

$k:{B}_{op}{⇒}_{ϵ}A.$

ここで A ⇒_ε B は、応答引数の評価効果も許す value-entry 関数の略記

$∀ζ. {F}_{Value}(A,ζ;B,ζ∪ϵ)$

とする。つまり resume の引数も receiver entry で評価し、その効果を捨てない。k の latent effect を自動的に ε\D_h にする規則はない。

### 2.2 操作意味論

#### 2.2.1 inert な値と同じ provider による invocation

閉包は body と lexical environment を持つ。Delay は **whole argument code** とその application site の lexical environment を持つ。閉包も Delay も、作るだけでは本体を実行せず、現在の handler stack や mutable store の snapshot を保存しない。

Call は次の順序で進む。

eval cf\
  └─ returned actual f\
       ├─ make t = Delay(ca, caller lexical references), inertly\
       └─ create fresh invocation r for this actual f and this call\
            Value entry: force t; bind the actual returned value; run f.body\
            Comp entry:  bind the actual t; run f.body

関数値の共有は許す。同じ閉包 handle p を二回使えば、provider p は同じで、invocation r1≠r2 とその receiving view は別になる。共有された閉包自体を、片方の呼出しの permission に合わせて書き換えない。

正規形で書けば、Value entry の β 規則は

$call (return {λ}^{Value}x.c) {c}_{a}→enter r (let x←{c}_{a} in c),$

Comp entry は

$call (return {λ}^{Comp}x.c) {c}_{a}→enter r (c[thunk {c}_{a}/x]).$

enter r は source invocation の制御用表示で、効果を追加・削除する型変換ではない。正常 return はその activation を終了する。request が外へ伝播した場合、raw suffix に owner re-entry を保存する。resume は現在の状態を使い、既存 owner がまだ live なら借り、終了していれば新しい execution occurrence を作る。古い handler の権限を復活させない。

#### 2.2.2 operation の producer と consumer

request(ℓ,v) の構築は inert。force(request(ℓ,v)) で初めて request が発生する。

operation を value payload に適用する規則は、概念上次の展開となる。

introduce t = thunk ca\
let q ← enter r (let p ← force t in return request(ℓ,p))\
in force q

最後の force は、operation declaration の result port による consumer である。任意の関数の結果が computation tag だったら再帰的に force する規則ではない。この順序は現行 OperationPayload、ReceiverReturn、OperationResultConsumer に対応する。[S04]

#### 2.2.3 resumptive tree と浅い handler

有限の観測 prefix を考えるため、計算を次の tree で表示できる。

$t::=Ret(v)∣Tau(t)∣Req(q,k),$

q=(fresh event,ℓ,payload)。k は宣言された result 型の応答を受け取る。実際には return/request と continuation は現在の world/store を引数に取る。以下の bind はその現在状態を左から右へ渡し、snapshot へ戻さない。

$Ret(v)bindF=F(v), Tau(t)bindF=Tau(tbindF), Req(q,k)bindF=Req(q,λb.k(b)bindF).$

handler の action は次の三場合である。

1. Ret(v)：handler activation を外し、value arm を実行する。

1. Req(q,k) で label(q)∈D_h：handler activation を外し、同じ payload と **raw k** を arm に渡す。

1. Req(q,k) で label(q)∉D_h：同じ q を外へ渡す。応答後の continuation は、**未選択だった** handler の復帰を伴う λb.catch H(k(b)) になる。

3の場合の復帰は、後の resume 時に新しい handler activation として起こる。2の場合には選択済み handler の再設置はない。したがって deep handler と shallow handler を混同しない。途中で crossed した未選択 inner handler は raw suffix に残る。

### 2.3 型付け規則

judgment は Γ⊢v:A と Γ⊢c:A ! ε。変数は環境の対応する型を持つ。() : 1、整数literalは Int、真偽値は Bool、文字列literalは String とする。型の変数を使う模式的な導出では、同じ型置換を全premiseへ適用する。effect weakeningを使う。今回の基本定理は optional-record adaptation の推移性を仮定しない。

effect weakening は computation の上界を広げる操作と、δ⊆ε に対する U_δ A から U_ε A への view の変更を含む。後者は実行コードを変えず、同じ computation の許される request 上界を広げるだけである。一般の値型を任意に同一視する subsumption は導入しない。

主要な規則を列挙する。

#### Return / Thunk / Force

$\frac{Γ⊢v:A}{Γ⊢return v:A!⌀}  \frac{Γ⊢c:A!ϵ}{Γ⊢thunk c:{U}_{ϵ}A}  \frac{Γ⊢v:{U}_{ϵ}A}{Γ⊢force v:A!ϵ}.$

この規則は一層の force のみを行う。A=U_δ B であっても、返った値を自動的にもう一度 force しない。

#### Strict Bind

$\frac{Γ⊢{c}_{1}:A!{ϵ}_{1} ; Γ,x:A⊢{c}_{2}:B!{ϵ}_{2}}{Γ⊢let x←{c}_{1} in {c}_{2}:B!({ϵ}_{1}∪{ϵ}_{2})}.$

x が未使用でも ε1 は残す。

#### Closure / Call

Value closure では

$\frac{Γ,x:A⊢c:B!{ϵ}_{c} ; {ϵ}_{a}∪{ϵ}_{c}⊆{ϵ}_{b}}{Γ⊢{λ}^{Value}x.c:{F}_{Value}(A,{ϵ}_{a};B,{ϵ}_{b})}.$

Comp closure では

$\frac{Γ,x:{U}_{{ϵ}_{a}}A⊢c:B!{ϵ}_{b}}{Γ⊢{λ}^{Comp}x.c:{F}_{Comp}(A,{ϵ}_{a};B,{ϵ}_{b})}.$

呼出し規則は

$\frac{Γ⊢{c}_{f}:{F}_{r}(A,{ϵ}_{a};B,{ϵ}_{b})!{ϵ}_{f} ; Γ⊢{c}_{a}:A!ϵ{′}_{a} ; ϵ{′}_{a}⊆{ϵ}_{a}}{Γ⊢call {c}_{f} {c}_{a}:B!({ϵ}_{f}∪{ϵ}_{b})}.$

**四ポートはこの一つの**** ****c_f**** ****と、一つの invocation について同時に使用される。** AV の witness には f、RE の witness には同じ型の別の g を選ぶ導出は、この規則の instance ではない。正負の型変換を挟むなら、関数の同じ値と四ポートを保つ adaptation の定理を別に要求する。

recfun^r f x.c は上の closure 規則の premise を Γ,f:F_r(...) の下で確認する。body の再帰参照は同じ f の型を使う。適用時には actual recursive closure を f に戻す。この小核は polymorphic recursion を勝手に認めない。

#### Operation

$\frac{Γ⊢v:{A}_{op} ; operation(ℓ)=op}{Γ⊢request(ℓ,v):{U}_{{ℓ}}{B}_{op}}.$

operation result が関数型なら、その関数型全体が応答型である。「Closure tag なら何でもよい」とはしない。

#### If

分岐の規則も明示する。

$\frac{Γ⊢v:Bool ; Γ⊢{c}_{1}:A!{ϵ}_{1} ; Γ⊢{c}_{2}:A!{ϵ}_{2}}{Γ⊢if v then {c}_{1} else {c}_{2}:A!({ϵ}_{1}∪{ϵ}_{2})}.$

#### Shallow Handler

入力 c:A!ε に対し、次を満たす。

- Γ,x:A⊢c_v:B!ε_v。

- ε 中で handler が処理する各 label の operation op について、Γ,p:A_op,k:B_op⇒_ε A⊢c_op:B!ε_op。

- 同じ operation の複数 label に同じ arm を使う場合、同じ arm 導出をその各分類に適用する。

このとき

$Γ⊢catch h H c:B!{ϵ}_{out},  {ϵ}_{out}=(remove(ϵ,{D}_{h}))∪{ϵ}_{v}∪⋃op{ϵ}_{op}.$

この row 規則は安全な上界であり、主型規則との同一性を主張しない。とくに k に入力全体の ε を渡すので、raw suffix の実際の効果より広い場合がある。既存の解を拒むために採用してはならない。

**精密化。** 捕捉した continuation の文脈導出から ε_k⊆ε が得られる場合、同じ証明により k:B_op⇒_{ε_k}A を使える。必要なのは actual suffix に対する導出であり、機械的な ε\D_h ではない。later bound と generalized use を含むこの文脈導出の生成が、現行実装への未完の接続である。

### 2.4 固定する構文データと型の範囲

operation signature は固定された写像 Σ(op)=(A_op,B_op) とする。両型は小核の値型であり、operation ごとに単相である。関数型や computation 型を含んでよい。新しく量化する effect variable ζ は signature、captured environment、既存の hole 導出に自由出現しない。

label ℓ は operation identity と route を持ち、その signature を Σ(op(ℓ)) から読む。runtime の個々の request event は新たな identity を持つが、型の label と同一視しない。handler は全域の分類関数 χ_h(ℓ)∈{hit,pass} を持ち、D_h={ℓ | χ_h(ℓ)=hit} とする。型付けと実行は同じ χ_h を使う。D_h を有限集合や閉じた allowance とする必要はない。一般の Yulang source からこの安定した分類を得ることは、別の対応定理である。

値の monotype と effect weakening は本章§2.1・§2.3のものを使う。すなわち任意の値型を同一視する subsumption はなく、computation の effect 上界の拡大と U_δ A から U_ε A への view の拡大（δ⊆ε）だけを使う。

上記の文法へ、次の runtime 構文を追加する。

v ::= ... | operation(ℓ) | cont(E)\
c ::= ... | perform ℓ v | enter ι c\
E ::= []\
    | let x ← E in c\
    | call E c\
    | catch h H E\
    | enter ι E

E は現在実行する hole を一つだけ持つ。call の argument に評価文脈は置かない。callee を得た後に receiver entry の規則が whole argument を扱う。force と if の引数は元から値なので、その内部の評価文脈もない。

enter ι は kernel 上では制御の owner marker であり、型付けと label 分類を変えない。実機の「live owner を借りるか、新 execution occurrence を作るか」という管理、provider の認証、world、permission の移動はこの marker の型付けだけからは導かない。kernel の再入時にも選択済み handler を自動で復活させる規則はない。これが現 runtime の owner 再入を模擬することは、別の simulation 義務として残す。

### 2.5 intrinsic scheme と runtime continuation の型導入

次の略記を、monotype 内の暗黙の二階量化にはしない。

$Cont(C;A,ϵ)=∀ζ. {F}_{Value}(C,ζ;A,ζ∪ϵ).$

環境の entry は通常の monotype、またはこの形の intrinsic scheme とする。scheme entry の変数は occurrence ごとに effect set δ を一つ選び、その monotype instance で使う。任意の effectful computation を一般化する規則を追加しない。scheme を値に与えるのは、ここで明記した operation と cont の導入規則である。返却値や高階関数の引数として使う際は、必要な一つの monotype instance を選ぶ。

#### Operation constant

$Γ⊢operation(ℓ):∀ζ. {F}_{Value}({A}_{op},ζ;{B}_{op},ζ∪{ℓ}),  op=op(ℓ).  (Op)$

これは同じ operation value の typing family である。instance ごとに別の provider を選ぶ量化ではない。request(ℓ,v):U_{ {ℓ} }B_op は上記の規則のまま、追加した runtime computation は

$\frac{Γ⊢v:{A}_{op}}{Γ⊢perform ℓ v:{B}_{op}!{ℓ}}  (Perform)$

と型付けする。

#### Continuation constant

z が E と Γ に自由出現しない fresh variable のとき、次の有限な hole 導出を certificate として用いる。

$\frac{Γ,z:C⊢E[return z]:A!ϵ}{Γ⊢cont(E):Cont(C;A,ϵ)}.  (Cont)$

ζ はこの certificate に自由出現しない。任意の instance δ では、Value-entry が応答引数を評価してから、この同じ E に返答値を入れる。そのため結果 effect は δ∪ε になる。cont(E) が別々の instance で別の frame や provider を選ぶことはない。

この規則は「continuation が安全」を前提にしない。既存の有限な型導出 Γ,z:C⊢E[return z]:A!ε だけを前提にする。証明上は λ^Value z.E[return z] の body 導出と同じであり、raw continuation を runtime 値として明記したものにすぎない。

owner marker の型付けは

$\frac{Γ⊢c:A!ϵ}{Γ⊢enter ι c:A!ϵ}  (Enter)$

とする。

handler の arm 環境にあった k:B_op⇒_ε A は、正確には k:Cont(B_op;A,ε) という scheme entry である。この定義で上記の handler rule は文法上も意味を持つ。

### 2.6 すべての runtime redex

以下で、requestの個々のevent identityを省略して perform ℓ v と書く。必要なら perform^e ℓ v とし、Force(Request)の際にfreshな e を一度発行する。型規則は e を型のlabelと同一視せず、forwardingは同じ e とpayloadを保持する。実Rustのevent保存は後の局所定理で別に証明する。

通常のβ規則と次の規則を E の下で閉じる。z、p、q は必要に応じて fresh とし、代入は capture-avoiding とする。

force (thunk c)  → c\
force (request(ℓ,v)) → perform ℓ v\
\
let x ← return v in c → c[v/x]\
enter ι (return v) → return v\
\
call (return (λ^Value x.c)) ca\
  → enter ι (let x ← ca in c)\
\
call (return (λ^Comp x.c)) ca\
  → enter ι (c[thunk ca/x])\
\
call (return (recfun^Value f x.c)) ca\
  → enter ι (let x ← ca in c[recfun^Value f x.c/f])\
\
call (return (recfun^Comp f x.c)) ca\
  → enter ι (c[recfun^Comp f x.c/f, thunk ca/x])\
\
call (return operation(ℓ)) ca\
  → let q ← enter ι (let p ← ca in return request(ℓ,p))\
    in force q\
\
call (return cont(E0)) ca\
  → enter ι (let z ← ca in E0[return z])\
\
if true then c1 else c2 → c1\
if false then c1 else c2 → c2\
\
catch h H (return v) → cv[v/x]

ι はその invocation に対する制御 marker である。Value と Comp のどちらでも、callee は先に得られている。Value-entry の引数効果は enter の内側にあり、Comp-entry では引数全体が thunk ca のまま渡される。したがって Comp parameter が未使用なら ca は実行されない。

operation Call では、**payload の評価と request carrier の生成を receiver activation の内側で行い、正常な receiver return の後に外側で request を force する**。上の規則を enter ι (let p←ca in perform ℓ p) へ縮約しない。kernel の集合上界だけを見ると同じでも、元の runtime の producer/consumer 順序と activation 境界は異なる。

handler の Hit は次の一つの規則とする。

$catch h H {E}_{0}[perform ℓ v]→{c}_{op}[v/p,cont({E}_{0})/k],  (Hit)$

ただし χ_h(ℓ)=hit、E_0 の内側に ℓ を hit する handler delimiter がないことを条件とする。これにより最も近い選択済み handler が使われる。E_0 は途中の **pass した inner handler** を含むが、今選ばれた catch h H は含まない。

Pass 自体を別の書換え規則にする必要はない。request の外側文脈が大きくなることで、同じ event/payload とその suffix が外側の handler へ伝わる。top-level で E[perform ℓ v] が残り、E のどの handler も ℓ を hit しなければ、外向き request である。型の合う実 response b:B_op を得た後は E[return b] から再開する。これにより pass した handler は suffix に残り、選択済み handler は再設置されない。

### 2.7 代入と文脈置換：安全性を前提にしない準備補題

**補題K4.1（同時代入）。** 上記の monotype 代入に加え、Γ,k:Cont(C;A,ε)⊢c:B!δ と、同じ runtime 値 w の intrinsic scheme 導出 Γ⊢w:Cont(C;A,ε) があれば、Γ⊢c[w/k]:B!δ が成り立つ。

**証明。** 有限な型導出に関する帰納法。変数 k の場合、元の導出が選んだ instance ζ=η を、与えられた **同じ** w の scheme に適用する。それ以外の変数は変わらない。各 constructor では全 premise に同じ代入を行う。新しい (Cont) の場合も、その finite hole certificate に帰納法を適用する。hole variable を fresh に取れば、代入は E[return z] の E 部分だけに作用し、E[w/k] は同じ形の評価文脈になる。(Op) は固定 signature の同じ値を返す。handler と recfun の binder は fresh に改名してから適用する。どのケースも runtime safety を前提にしない。□

この補題は同じ continuation を複数回使う場合も、そのまま使える。w の物理コピーや、各 instance で異なる body witness を許す補題ではない。

**補題K4.2（typed context replacement）。** 導出 Γ⊢E[c]:A!ε があるとき、hole に現れる導出 Γ⊢c:C!δ を取り出せる。同じ C!δ を持つ d に置き換えれば Γ⊢E[d]:A!ε を再構築できる。

**証明。** E と既存の型導出に関する帰納法。Bind・Call・Enter は hole 側の premise を置き換え、それ以外を再使用する。Catch でも scrutinee の **同じ型と同じ effect 上界** の導出を置き換えるため、value arm と operation arm の型は変わらない。effect weakening は同じ最後の weakening を再使用する。E の文法に binder が hole を束縛する場合はないので、hole の環境は Γ のままでよい。□

ここで δ は exact effect である必要がない。元の導出の上界を保持することが、handler arm の continuation 型を変えずに置換する鍵である。

### 2.8 request 分解と raw suffix の完全な構文的証明

**定理K5（unhandled request decomposition）。**

$Γ⊢E[perform ℓ v]:A!ϵ$

の有限な型導出があり、E に ℓ を hit する handler delimiter がないとする。op=op(ℓ) とすると、次の三つが同時に成り立つ。

1. ℓ∈ε。

1. Γ⊢v:A_op。

1. fresh z:B_op に対して Γ,z:B_op⊢E[return z]:A!ε。従って任意の Γ⊢b:B_op について Γ⊢E[return b]:A!ε。

**証明。** 評価文脈 E の構造と、その型付け導出に沿って帰納する。最後の effect weakening がある場合は、それを外した導出に帰納法を適用し、label の集合包含と同じ weakening で結論を戻す。

- **E=[]****。** (Perform) から payload の型と ℓ∈{ℓ}⊆ε を得る。return z は B_op!∅ を持ち、∅⊆ε で weaken する。任意の異なる response 型を選ぶことはできない。

- **E=let x←E′ in d****。** inversion により E′[perform ℓ v]:C!ε₁ と Γ,x:C⊢d:A!ε₂、ε₁∪ε₂⊆ε を得る。帰納法から ℓ∈ε₁ と同じ C!ε₁ を持つ E′[return z] が得られる。Bind の suffix 導出を変更せず再使用すれば3を得る。payload は hole の環境 Γ で型付けされる。

- **E=call E′ d****。** inversion により callee 側は一つの F_r(C,δ_a;A,δ_b)!ε_f を持つ。帰納法は callee を作る計算に適用でき、ℓ∈ε_f と同じ callee 型・上界を持つ置換を得る。argument 導出と同じ四ポートの Call 規則を再使用する。ε_f⊆ε_f∪δ_b⊆ε から1を得る。

- **E=enter ι E′****。** (Enter) は型も effect も変えないので、帰納法の三結論をそのまま持ち上げる。

- **E=catch h H E′****。** inversion で body は C!δ、handler の結果上界は (remove(δ,D_h))∪δ_v∪⋃δ_op⊆ε。帰納法から ℓ∈δ を得る。仮定により ℓ∉D_h なので、ℓ∈remove(δ,D_h)⊆ε。置換 body は、帰納法によって **元と同じ**** ****C!δ** を持つ。そのため arm に割り当てた Cont(B_op′;C,δ)、value arm、全 operation arm を一切変更せず同じ handler rule で再構築できる。これで3が成立する。このステップは handler safety や実行の preservation を用いない。

これが全評価文脈を尽くす。最後に補題K4.1の monotype 場合を z に適用すれば、任意の実 response b の結論を得る。□

**系K5.1。** この **同じ** E に対し、Γ⊢cont(E):Cont(B_op;A,ε) が導ける。証明は3を (Cont) の premise にするだけである。ε\D_h はこの結論に現れない。

**系K5.2。** inner handler を pass した raw suffix は、その handler 自体を含む E によって型付けされる。selected handler を除いた raw suffix と、未選択 handler の復帰を同じ深い handler と見なさない。

### 2.9 Preservation

**定理K6。** Γ⊢c:A!ε かつ上記の kernel 内部ステップ c→c′ なら Γ⊢c′:A!ε。外向き request についてはK5の payload・response continuation の型を持つ。

**証明。** まず一つの redex を証明する。最後にK4.2で任意の外側評価文脈へ持ち上げる。

- **Force(Thunk)。** thunk d:U_δ A の inversion と、必要な U effect weakening から d:A!δ′、δ′⊆δ を得る。computation weakening により元の force と同じ上界にする。

- **Force(Request)。** request の型導入から payload の宣言型と A=B_op、{ℓ}⊆ε を得る。perform ℓ v:B_op!{ℓ} を元の上界へ weaken する。

- **Bind(Return)。** v:C と suffix Γ,x:C⊢d:A!δ にmonotype代入を適用する。δ は元の union 上界に含まれる。

- **Enter(Return)。** 値型をそのまま使い、return の空 effect を元の上界へ weaken する。

- **Value closure Call。** inversion で引数は C!δ′、δ′⊆δ_a、body は A!δ_c、δ_a∪δ_c⊆δ_b。entry Bind の effect δ′∪δ_c は δ_b に含まれ、Enterで保持する。callee の元の上界 ε_f も含めて weaken できる。

- **Comp closure Call。** thunk ca:U_{δ′}C を U_{δ_a}C に widen し、body の Comp parameter へ代入する。引数はこの時点で実行されず、結果は body の A!δ_b を持つ。

- **再帰 Call。** 有限な recfun の型導出そのものを self binder に代入してから、上の Value/Comp の証明を使う。型証明は再帰を無限展開しない。

- **Operation Call。** (Op) の使用 instance を ζ=δ_a とする。payload を評価する内側Bindは effect δ′、request(ℓ,p) の生成は空 effect、Enterも δ′ を保つ。外側Forceは {ℓ} を追加する。したがって全体は B_op!(δ′∪{ℓ}) を持ち、δ′⊆δ_a より instance の result effect δ_a∪{ℓ} に含まれる。

- **Continuation Call。** (Cont) の certificate は Γ,z:C⊢E₀[return z]:A!δ。応答引数 ca:C!δ′ を先に entry Bind で評価するので結果は A!(δ′∪δ)。使用した instance は F_Value(C,δ_a;A,δ_a∪δ)、δ′⊆δ_a なので Callの元の上界に含まれる。

- **If。** Bool の canonical forms から真偽のどちらか一方を選ぶ。両branchが元の結果型・effect上界を満たす。

- **Handler(Return)。** 入力から得られた v:C を value arm へ代入する。結果 effect δ_v は handler の上界に含まれる。

- **Handler(Hit)。** body の型を C!δ とする。K5を body の E₀[perform ℓ v] に適用し、同じ payload の型と cont(E₀):Cont(B_op;C,δ) を得る。ℓ∈δ∩D_h なので handler rule がこの arm の導出を保証する。この二つの **実値** を armの p,k へ同時代入する。結果は A!δ_op、δ_op は handler出力の unionに含まれる。選択済みhandlerを cont(E₀) に含める必要はなく、実際に含めない。

これは全redexを尽くす。未選択handlerを含む外側文脈へはK4.2を適用する。外向きrequestはK5を直接適用する。証明中にtree safetyやhandler safetyを使った場合はない。□

閉包・Delayを環境付きの実装値として表す場合、各自由変数を同じ型の同じactual valueに置き換える型付き環境代入が必要になる。純粋な有限環境・recfunの共有についてはK4.1の同時代入の表現変更である。未定義の可変store規則やpermission規則の安全性までこの説明で補ったことにはしない。

### 2.10 Progress と有限実行の effect safety

**定理K7（progress）。** 閉じた ⊢c:A!ε は、次のいずれかである。

1. return v で ⊢v:A。

1. ある c′ への内部ステップを持つ。

1. E[perform ℓ v] で、E に ℓ を hit するdelimiterがなく、ℓ∈ε、⊢v:A_op、⊢cont(E):Cont(B_op;A,ε)。

**証明。** 値型のcanonical formsを型導入から先に得る。閉じたF_Value値はValue閉包、対応するrecfun、operation(ℓ)、またはhole certificate付きcont(E)。F_Comp値はComp閉包または対応するrecfun。U_ε A値はthunkまたは宣言型のrequest carrier、Bool値は真偽のいずれかである。限定したweakeningはこれらの形を変えない。

次に有限なcomputation構文に帰納する。Returnは1。ForceとIfはcanonical formsからredexを持つ。Bindは左辺がreturnならredex、stepならそのstepを文脈へ持ち上げ、外向きrequestならBind文脈をsuffixに追加する。Callはcalleeだけに同じ帰納法を使い、calleeがreturnなら上記四種のcallable規則の一つを適用する。argumentを先に評価する場合はない。

Enterでは内側のreturnを除去し、stepは持ち上げ、requestにはEnterをsuffixとして残す。Catchではbodyがreturnならvalue arm、stepなら持ち上げる。bodyがrequest文脈なら、全域のχ_hによりhitかpassを判定する。hitならK5のℓ∈body effectとhandler typingのarm coverageからHit規則を適用でき、passならCatchをsuffixに追加する。Performそのものは3である。

有限な外側文脈にmatchがあれば最も近いmatchを選べる。matchがなければK5で3の型・effectを得る。recfunは適用時に有限な一βステップを持つので、この帰納法で評価の終了を仮定する必要はない。□

**系K7.1（有限実行と正しいresponseに対するeffect safety）。** 閉じた c:A!ε から始め、外部がrequestに対して宣言型 B_op の実値だけを返すとする。任意の有限回の内部stepと外部responseの後も状態は A!ε を持つ。外向きrequestのlabelは ε に含まれ、payloadは宣言型、正常returnは A の値である。

**証明。** 有限実行長に関する帰納法。内部stepはK6、外部responseはK5の E[return b] の結論を使う。各prefix末尾の分類はK7、外向きrequestの情報はK5で得る。□

handler armがeffectfulなresponse計算を cont(E) に渡すときには、その追加effect ζ もCall規則の ζ∪ε に数える。外部が既に得られたresponse値を渡す場合と、任意のeffectful computationを無償で注入する場合は区別する。

ε=∅ なら外向き unhandled request は起きない。無限に内部stepが続く再帰についても、すべての有限prefixが同じ性質を持つ。ここから終了性は主張しない。

### 2.11 tree表示と証明の依存順序

§2.2の Ret/Tau/Req 表示は、上記のsmall-step実行の観測として読める。内部stepはK6、外向きrequestと正しいresponseによる再開はK5、有限prefix全体はK7.1で型付けされる。したがって、strict Bindの安全性と浅いhandlerの安全性は、これらの定理を繰り返し適用した系である。

証明の順序は、構文・型規則、同時代入、文脈置換、request分解、preservation/progress、有限実行の安全性となる。handlerの安全性をpreservationの前提として循環させていない。高階の応答値も、その値自身の有限な型導出を保持することで扱う。

### 2.12 R252・raw resume・CBV let の具体的な導出

#### 2.12.1 開いた negative row は state callback を拒まない

callback の型を

$Cb(χ)={F}_{Value}(1,⌀;1,χ)$

とする。receiver の formal に書かれた [io] は、negative position では open row と local permission P={io} を与える。actual callback の effect χ を閉じた {io} へ制限しない。上界表現を使う場合も χ⊆{io}∪δ であり、actual χ と permission P を分けて保持する。

cb_state=λ().force(request(ℓ_state,())) なら χ={ℓ_state}。δ に state の contribution を入れれば境界適合は可能である。**permission は io のままであり、state の contribution を消す権限にはならない。**

receiver body が callback を使わず Unit を返すなら body effect は空。receiver body が call cb (return ()) なら Call rule より effect は χ。io handler を置いても ℓ_state∉D_h なので、定理K6のhandlerの場合の Pass 分岐から state は外へ残る。同じ derivation に受理・呼出し・残余が結び付く。

現行 R252 の candidate_formal_effect_port は fresh effect port と FormalPermission を作り、negative concrete row を closed upper bound にしていない。この source-level 方向は維持する。ただし FormalPermission から actual D_h を作る consumer は別の未完部分である。[S05]

#### 2.12.2 同じ family の後続 request も自動的には消えない

次の resumptive tree を考える。

Req(io, payload1, λanswer1.\
  Req(io, payload2, λanswer2.Ret(())))

最初の io を浅い handler が選び、その arm が raw k を一回 resume すると、二番目の io は **その選択済み handler の外側**で発生する。追加の handler がなければ外へ出る。{io}\{io}=∅ を raw continuation の型にまで適用する規則は、この二段の計算で反例を持つ。

これは明示した浅い意味論に対する反例であり、Oracle compiler がこの不正規則を実装しているという主張ではない。正しい型は k の latent effect に後続 io を保持し、arm の ε_op にそれが入るため、定理K6を満たす。

別 family state を二番目に置いても同じ証明になる。二番目の request がまだ実行されないまま arm が k を破棄した場合は、後続計算自体が実行されない。これを「発生済みの別 contribution が不正に消された」と表現してはならない。

#### 2.12.3 Function response の latent effect

ping:1⇒Cb({state}) とし、arm が response=λ().state() を k に渡す。定理K5は **B_ping=Cb({state})** を応答型として要求する。resume が即座に返す値が closure でも、現在の immediate effect は空になり得る。一方、その closure の型には latent state が残り、後で actual closure を Call すれば state が発生する。

この導出には、response を同じ型の別の closure へ交換する手順も、Closure tag だけで B_ping の型付けを済ませる手順もない。operation-v1 が保持しようとしている exact local definition→actual closure handle→later Apply→callback event の接続は、この導出を実装へ結ぶための情報である。[S06]

#### 2.12.4 厳格な initializer の効果を落とさない

$let x←force(request({ℓ}_{h},())) in return()$

の effect は {ℓ_h}∪∅={ℓ_h}。x が未使用であり、型が ground で、一般化すべき変数がゼロでも、initializer は実行される。定理K6のstrict Bindの場合と系K7.1の Req 分岐により、外へ出る最初の request は保存される。

これは旧 CBV I-Let 文書の反例に対する明示的な修正である。旧反例は let x=perform_h(()) in () を empty effect とした規則を否定していた。initializer effectを残すというこの修正自体には、value restrictionを要しない。一般化全体の安全性は次節で別に扱う。initializer effect と result value の一般化を別々に扱えばよい。[S07]

### 2.13 一般化について閉じた部分と閉じていない部分

#### 定理3：strict polymorphic let の正しい条件

この定理は、上の小核に任意のeffectful initializerの一般化規則を暗黙に追加するものではない。一般のscheme entryを許す場合の、明示した条件の下での拡張定理である。schemeに対する代入は、各occurrenceで元の導出が選んだinstanceを同じ値に適用するという、K4.1と同じ帰納法で扱う。

initializer c1 の実行が A!ε1 を満たし、**その同じ returned value** v が、外側の型・effect・runtime environment を固定したすべての許可 substitution θ に対して θA を満たすとする。body は scheme ∀a.A の各 use で、一つの整合した substitution により v を使用し、B!ε2 を満たすとする。

このとき strict let 全体は B!(ε1∪ε2) を満たす。

**証明。** initializer が request を出す間は定理K6のstrict Bindの場合と系K7.1が同じ request と suffix を保持する。return したら、その actual value v を一回だけ環境に保存する。body の各 scheme use は、それぞれの θ に対する v の premise と同時代入補題から型付けされる。runtime value を use ごとに別の値へ取り替える必要はない。body の安全性と定理K6のstrict Bindの場合と系K7.1により結論。□

これは一般化の semantic condition を明示した theorem であり、「各 use に適当な値が別々に存在する」で代用できない。

**構文的に閉じる十分条件。** 小核の λ/recfun/thunk などの inert value に対する導出で、一般化する型・effect 変数が外側の Γ、operation signature、shared anchor に自由出現しない場合、同じ導出へ任意の θ を同時代入できる。導出に関する帰納法から同じ runtime value がすべての θ に対応する。この場合には、一般化する変数を含む全制約も同じ置換で満たすという合法instanceの条件の下で、上の定理を適用できる。

**残る範囲。** 一般の effectful initializer、generic operation、mutable state、continuation に関連した polymorphic instantiation、scheme graph の Capture/FreshUse について、現行 compiler がこの uniformity condition を必ず作ることは本稿では証明していない。「安全な場合だけがYulangの言語仕様」と変更するのではなく、元の既存受理例を維持してこの条件を証明する責任が残る。runtime event、handler activation、shared provider を type-variable freshening と一緒に無差別に freshen してはならない。

### 2.14 現行 Rust 実装に対して閉じる局所定理

以下は 5596b159... の private machine を、その正規 constructor から開始した実行についての定理である。不正な arena handle を外部から注入した state は対象ではない。成功した遷移の safety を示し、必要な witness が欠けたときの Unavailable を source-level 型エラーや divergence と同一視しない。

#### 定理4：actual Call の三点の同一性

Frame::Callee から closure invocation が進む場合、次の三つは同じ Call に属する。

1. 実行した closure は、callee evaluation が返した ReceivedValue.value をキーに得た ExecutableValue::Closure。

1. 引数 Delay の code/environment は、その Frame::Callee が保存した actual argument と caller environment。

1. 実行 body と captured environment は、1で得た closure のもの。ValueEntry が束縛する値は、2の Delay の force が返した同じ handle。

**コードによる証明。** evaluate(Apply) は callee/argument/environment/site のうち後三者を Frame に保存して callee へ進む。return_value(Callee) はその actual frame の argument/environment から Delay を allocate し、self.executables.get(&received.value.0) を一度取得する。Closure 分岐の body/environment/parameter はこの record の pattern binding。新 invocation は actual call site と actual provider source を記録する。Value role は同じ body/environment の ValueEntry を積み、直前に作った Delay を execute する。ValueEntry はその return の received.value を bind して同じ body を Evaluate する。Comp role は同じ Delay を bind して同じ body を Evaluate する。途中に型から別の provider を選ぶ lookup はない。□ [S01][S03]

この定理は型の正しさをまだ言わないが、四ポートの theorem を適用するための actual-provider 相関を実コードについて閉じる。

#### 定理5：選択された handler の exact event と positive Grant

現行 propagate_request が operation arm を選択して State::Evaluate(arm.body) へ進む場合、次が成立する。

- declaration identity は request.declaration.id と exact equal。

- 選択の検査時点では handler installation はまだ stack 上にあり、その owner は current executable owner と一致し、live である。arm の Evaluate へ移る時点では、後述のとおり pop 済みである。

- closed_primitive certificate があるか、**同じ request.event** について local_grant が true を返している。

- payload は選択 declaration の argument 型に対する現行 primitive check を通過している。

- selected handler は arm を Evaluate する前に pop される。

さらに local_grant=true の場合には、単に family が等しいだけでなく、次の witness が存在する。

1. live な invocation owner r と、その r に固有の boundary。

1. 同じ source owner に属する formal annotation が対象 family を concrete permission に含む。

1. 同じ event を持つ authentic ExecutionView observation。

1. その exact view に対する candidate owner r の actual receipt。

1. その view の image parent chain から r の boundary への到達。

**コードによる証明。** handler の候補を frames.last().cloned() で読む段階ではまだ pop していない。validate_handler_installation が occurrence 範囲、owner 一致、activity を検査する。operation arm の loop は異なる declaration id を continue する。同じ id では closed certificate または local_grant を要求し、失敗は forwarding ではなく HandlerEvidence として止まる。payload・continuation response guard の後で初めて frames.pop() し、actual payload と actual captured continuation を bind する。

local_grant は ModuleRun を拒み、r の live membership を調べ、r 固有 boundary を binary search する。annotation owner と concrete family を確認する。各 observation で event equality と authentic execution を検査し、receipt の exact view を確認する。candidate receipt は (owner,view,formal) をキーに取得し、owner/view/formal を再検査する。その後の parent-chain loop が r に到達した場合だけ true を返す。visited set はこの認証後にのみ使うため、別の未認証 observation の family が一致しても Grant は作れない。□ [S08][S09]

この theorem は **Grant の sound positive witness** を証明する。必要なすべての source path に Grant が作られること、unknown なときに正しく forwarding できることは証明していない。現行 runtime は unknown と否定を混同しない代わりに Unavailable で停止し得る。

#### 定理6：raw suffix の順序と浅い除去

request propagation が frame F1,…,Fn を順に pop して suffix に保存し、その後に handler h を選択したとする。capture が成功し、そのtemplateへの再入がHoleまで成功した時点で、元のsuffixに対応するframeはstackの上から F1,…,Fn の順に復元される。selected h の delimiter はその template に含まれない。途中で forwarding した未選択 handler の delimiter は含まれる。

これは復元されたframeの相対順序の定理である。capture成功だけで、その後の資源確保、templateへの再入、suffix全体の正常終了まで保証しない。suffix自身の分岐、再request、abortによって後続frameへ到達しないことも許す。

**コードによる証明。** propagate_request は一回の forwarding につき actual top frame を一つ pop し、それを request.suffix.push(template) する。したがって保存順は「次に return を受けるものが先」。選択候補は pop する前に調べ、capture_template には選択 h を追加していない。

capture_template は Hole から始め、suffix を保存順に読み、各 node の inner を直前の root にする。したがって追加の containing-owner wrapper を除く root は Fn(…F2(F1(Hole)))。enter_template は outer node から frame を stack に積み、inner へ降りる。Hole 到達時の source suffix の先頭は F1、次が F2、…となる。containing-owner wrapper はその外側の制御括弧であり、この相対順序を変えない。これは n に関する単純な帰納法である。

SavedFrame::HandlerBoundary だけが ForwardHandler node を作り、再入時には fresh handler occurrence を allocate する。選択 h は suffix にないので復活しない。Owner node は live owner を借りるか新しい invocation occurrence を作り、borrowed delimiter は元の live invocation を pop しない。GlobalRead/Root cache-write frame があれば materialization は失敗するので、未対応の suffix を成功した continuation に変えない。□ [S10]

#### 定理7：actual response handle と event identity の保存

ResumeArgument の検査を通った actual ReceivedValue は EnterTemplate にそのまま渡され、Hole は同じ ReceivedValue を Return する。Bind/Owner/ForwardHandler/View node は response を別の値に置き換えない。

request carrier の execute は fresh event を一回 allocate し、同じ declaration/payload/source を PendingRequest に移す。forwarding はその request の event/payload を再生成しない。後の resume で同じ source operation を再実行した場合は、新しい execute による新 event となる。

**コードによる証明。** ResumeArgument は response:received を State::EnterTemplate に設定する。enter_template の各非Hole branch は response 引数をそのまま次の State に渡し、Hole は State::Return(response)。execute(Request) は next_request を checked increment して PendingRequest を一回作る。propagate_request は同じ request を mutable ownership で受け取り、suffix 以外の identity を変更せずに State::Request または UnhandledRequest へ渡す。□ [S11]

この定理は operation-v1 の particular closure が **同じ closure** として resume に渡されたことを支える。任意の closure が宣言の higher-order response type を満たすことを、runtime tag から導くものではない。

### 2.15 通常経路と operation-v1 への適用

#### 2.15.1 通常経路

execute は候補推論後に _candidate を保持するが、RuntimeProgram を RuntimeEvidence::default() で作る。[S12]

定理4〜7は、この通常経路の actual successful transitions にそのまま適用できる。closed_primitive の成立する有限 primitive universe では、Lambda や bound continuation がないことを全 code/dependency に対して分類しているため、callback protection を要するイベントがこの universe に存在しない、という限定された経路もある。[S13]

一方、型安全性の定理K6・K7を **全 candidate accepted source** へ適用するためには、同じ source の型付け導出、result/consumer role、static classification、scope transport が必要である。default evidence と構造的 solve 成功だけでは、この結合 premise は得られない。

#### 2.15.2 operation-v1

research entry は一つの HIR で candidate を solve し、observes_hir と conflict absence を確認し、同じ HIR/candidate から evidence を構築する。[S12] その後の実行は同じ Machine の Call/Request/Resume/Handler 規則を使うので、定理4〜7を再証明せず再利用できる。

current function-response guard は、particular request/catch/arm、particular response local read、particular lambda source、actual closure handle を確認する狭い分岐を持つ。このため「たまたま42が出た」だけより強い causal identity を確かめられる。**ただしこの exact-source guard は、一般の**** ****Γ⊢response:B_op**** ****の決定手続ではない。** operation-v1 の一つの response についても、静的にその body と四ポートの型付けを閉じ、実 code の body/environment に結び付けて初めて定理K6を適用できる。

つまり、現行 code の identity join は実証明で閉じられるが、自然な全 source Call と全 higher-order response の型安全性への拡張は残る。operation-v1 に合わせて他の正常 source を拒否する必要はない。

### 2.16 元の全体定理へ残る接続

| **残る接続** | **今回までに閉じたもの** | **次に証明すべき実装上の事実** |
| --- | --- | --- |
| source → typed core | role付きCall・厳格Bind・浅いresumeの型安全性 | 全LocalSource constructorについて、同じsourceの導出を生成すること |
| R252 → actual permission | open rowでstate callbackを受理しstate residualを保つ導出 | FormalPermissionからsame-use/view/arrival/providerのGrantを作ること |
| four ports → runtime | actual callee/argument/body/result identity | source四ポートと同じruntime view全体の型付け |
| shallow residual | raw kを含むhandler ruleのsoundness | actual suffix rowの生成、replay、Capture/FreshUse、公開結果との一致 |
| generalization | strict effect union、uniform same-value条件、inert値の十分条件 | 一般effectful initializerを含む候補schemeが条件を満たすこと |
| scope/receiving | 現行positive Grantのexact witness | 全合法pathの生成、absenceとunknownの扱い、escaped latent path |
| continuation response | exact response handle保持、suffix order | generic operationのrigid opening、全response型の導出とcontinuation environmentの型付け |
| runtime total coverage | successful transitionsの局所保存 | well-typed accepted sourceがUnavailableに落ちないこと、module initialization/storeの対応 |

特に、今回の「型安全性の定理」と「実コードのidentity不変条件」をただ並べて、接続が完成したことにはしない。その間にある型付け・effect label・scope/view の翻訳を、同じ source occurrence を保った一つの定理として閉じる必要がある。

### 2.17 固定ソースの根拠と確認方法

以下の candidate/runtime path はすべて研究branch固定 commit、Oracle path のみ anchor commit。新しい cargo test やビルドは実行していない。静的コード読解による有限の制御・データフロー証明であり、計測やテスト成功を報告していない。

- **S01** [tools/inference-playground/src/runtime/machine.rs:642–674,910–1042](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/tools/inference-playground/src/runtime/machine.rs#L642-L674) — closure/Apply/actual provider/Value・Comp entry。

- **S02** [notes/design/2026-10-02-ordinary-computation-semantics-package.md:91–278,280–445](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/design/2026-10-02-ordinary-computation-semantics-package.md#L91-L278) と notes/design/2026-10-02-typed-computation-core-elaboration.md:55–209 — whole argument delay、role、current configuration、shallow rule。これらは履歴上のDraftであり、ソースからの全構成定理が閉じたという根拠には使わない。

- **S03** [tools/inference-playground/src/runtime/machine.rs:1112–1175,1967–2002](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/tools/inference-playground/src/runtime/machine.rs#L1112-L1175) — ValueEntry、local cellへのactual value保存、厳格initializer。

- **S04** [tools/inference-playground/src/runtime/machine.rs:904–908,1043–1098,1858–1874,2003–2040](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/tools/inference-playground/src/runtime/machine.rs#L904-L908) — operation producer/result consumer/request emission。

- **S05** [crates/yu-solver/src/candidate_effect.rs:231–234,1385–1427](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_effect.rs#L231-L234)、notes/theory/2026-10-21-r252-open-effect-tail-correction.md — permissionとnegative open row。

- **S06** [tools/inference-playground/src/runtime/machine.rs:779–848,941–997,1676–1700](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/tools/inference-playground/src/runtime/machine.rs#L779-L848) — actual function responseとexact v1 guard。

- **S07** [notes/theory/oracle-inference-document-audit/typing-generalization.md:178–225](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/theory/oracle-inference-document-audit/typing-generalization.md#L178-L225) — CBV let initializer effectを落とした旧定理の反例。Oracle compiler bugを主張する資料ではない。

- **S08** [tools/inference-playground/src/runtime/machine.rs:1585–1784](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/tools/inference-playground/src/runtime/machine.rs#L1585-L1784) — live candidate、exact declaration、Grant、payload、selection-before-pop。

- **S09** [tools/inference-playground/src/runtime/receiving.rs:207–335](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/tools/inference-playground/src/runtime/receiving.rs#L207-L335) — observation、receipt、positive local Grantとimage path。

- **S10** [tools/inference-playground/src/runtime/machine.rs:1336–1550,1787–1829](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/tools/inference-playground/src/runtime/machine.rs#L1336-L1550) — owner、capture_template、enter_template、forwarded frame順序。

- **S11** [tools/inference-playground/src/runtime/machine.rs:779–848,1451–1550,2003–2040](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/tools/inference-playground/src/runtime/machine.rs#L779-L848) — response伝達とevent生成。

- **S12** [tools/inference-playground/src/lib.rs:168–268](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/tools/inference-playground/src/lib.rs#L168-L268)、tools/inference-playground/src/runtime/program.rs:216–275 — 通常実行と同じHIR/candidateを使うv1入口。

- **S13** [tools/inference-playground/src/runtime/primitive.rs:24–213](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/tools/inference-playground/src/runtime/primitive.rs#L24-L213) — 全programのclosed primitive分類。

- **S14 Oracle対応** [crates/infer/src/lowering/expr/tail.rs:535–628](https://github.com/momota1029/yulang/blob/a58eefc31e22141574b6f20c6a5748151c6d79f1/crates/infer/src/lowering/expr/tail.rs#L535-L628) はactual calleeとargumentのvalue/effectを一つのFun上界へ結び付け、callee effectとreturn effectをresult effectへ結ぶ。crates/infer/src/constraints/machine/propagate.rs:212–270 はAV/AE反変、RE/RV共変。これは本稿の四ポート配置の参照であり、Oracleから新型安全性定理を無証明で移植する根拠ではない。

## 3 Capture・FreshUse・scope変換の実装保存

### 3.1 実際の識別子と処理経路

固定版の実在する識別子は次のとおりである。ConstraintId という型名はない。

| **役割** | **現行の型・構造** | **所有箇所** |
| --- | --- | --- |
| source の制約位置 | ConstraintOccurrenceId = HirOccurrenceId + local_slot | lib.rs:422–443 |
| source の格納済み fact | FactId、AdmissionReceipt | lib.rs:3175–3210 |
| context 付きの関係 | RelationId、relation の pair/context/scoped payload | candidate_context.rs:30–31,3020–3030 |
| bound の admission と物理格納 | BoundAdmissionId、BoundEmissionId、PhysicalBoundSlot | candidate_context.rs:489–554 |
| owner と向き | BoundKey(owner, polarity, item) | candidate_effect.rs:34 |
| 捕捉した一つの fiber | Bound { relation, source_bound, kind, side, lower, upper, evidence } | candidate_scheme.rs:156–164 |

同じ BoundKey に複数の RelationId が付く場合がある。同じ source occurrence からも replay による異なる fiber ができる。したがって source occurrence 又は端点対だけを semantic 重複排除のキーにしてはならない。既存 Capture::bound は relation まで含めて区別している（candidate_scheme.rs:1242–1285）。

#### 3.1.1 物理 bound の向き

candidate_apply_effect(a,b) は canonical な effect row 同士について、

- level(b) <= level(a) なら a の negative/upper lane に b を格納する。

- そうでなければ b の positive/lower lane に a を格納する。

これは candidate_extrusion.rs:954–977 の場合分けである。同年齢の a <= b は a の upper に置かれ、b の lower に同じ辺を二重格納しない。

その直後、同じ owner の反対側の lane と replay する。candidate_opposite_count は direct row と exact atom の両方を数え、candidate_opposite_bound も両方を読む（同 684–743）。candidate_replay_bound は実際の lower/upper の順序を定め、両方の BoundKey を渡す（同 877–917）。この経路を落とした graph は、実際の飽和済み solver 状態ではない。

#### 3.1.2 現行 Capture が列挙するもの

local row の owner lane を両側とも読む。nonlocal row では直ちに止まり、同じ live identity を anchor として使う（candidate_scheme.rs:1289–1407）。effect の補助的な逆索引は、次の条件をすべて満たす場合にだけ使う。

- Capture boundary が正である。

- 対象 row が shape_effect_rows に入っている。

- 捕捉対象 upper row が local である。

- owner の upper bound が、保存済み completion receipt に対応する Lambda slot 4 relation を持つ。

索引**構築**自体は全 effect owner を走査する。shape 制限は索引の**利用側**にある（同 843–928,1340–1385）。R245 の「索引自体が shape だけを収録する」という説明は、この区別を修正する必要がある。

record_source_drain_completion が allocation failure で記録を省いても source drain は終了する（candidate_context.rs:2150–2161、lib.rs:12822–12832）。したがって reverse-owner から特定の元の辺を必ず捕捉する、という証明にはこの経路が障害になる。ただし、**同じ意味を持つ別の飽和済み bound が捕捉されないことまで示さなければ、root の意味保存への反例にはならない**。

### 3.2 定理3-A：older anchor からの有限 identity-chain は通常 replay で回収される

#### 3.2.1 定理の範囲

固定した Capture boundary を b とする。canonical な effect row を

$a,{x}_{1},…,{x}_{n}  (n≥1)$

とし、a は level(a) <= b、各 x_i は同じ level h > b で non-generic でないとする。この区間では row の同一化・level 変更は行わない。次の ordinary row 制約を、それぞれ identity context と default scoped flow で admission し、関連する typed work と replay が正常に完了しているとする。

$a≼{x}_{1}, {x}_{1}≼{x}_{2}, ⋯, {x}_{n−1}≼{x}_{n}.$

これは「結論の shortcut が admission 済み」という仮定ではない。入力は上記の隣接辺だけであり、shortcut の存在をコードから導く。

**結論。** 各 i に対して a <= x_i の physical bound が x_i の positive/lower lane に存在する。少なくとも一つの identity/default fiber がその bound に付く。Capture の型 shape が x_n を含めば、completion receipt と boundary > 0 の条件に依存せず、その shortcut を捕捉する。

#### 3.2.2 証明

i=1。level(a) < level(x_1) なので candidate_apply_effect の後半の場合に入り、owner は x_1、side は Positive、item は a となる。

帰納段階。a <= x_i は x_i の lower lane に存在するとする。x_i=x_{i+1} なら帰納仮定がそのまま結論になる。異なる場合、入力の隣接辺 x_i <= x_{i+1} は同年齢なので x_i の upper lane に置かれる。両辺を admission した順序にかかわらず、後から入った側の candidate_replay_bound が反対 lane にある先行辺を読む。replay の実際の task は a <= x_{i+1} である。

candidate_context_begin_replay は二つの bound のすべての新しい fiber の組を列挙する（candidate_context.rs:3869–3917）。identity 同士の場合は明示的に identity を使う（3900–3903）。default scoped flow の合成は default のままであり、effect の demand は存在しない。正常完了した child はこの effect task を通常 admission する。a は古いので、得られた bound の owner は x_{i+1} の positive/lower lane である。既に同じ fiber が処理済みの場合も、必要な child が存在することは変わらない。以上で帰納法が閉じる。

Capture は local な x_n を展開すると、その direct_lower_rows を無条件に列挙する（candidate_scheme.rs:1357–1364）。そこで a <= x_n を bound に渡し、付いている relation を列挙する。a を row として登録しても、local=false なのでそれより外側へ展開しない。この処理は restricted reverse-owner index を通らない。□

この証明は effect row の ordinary replay についてのものである。optional record 等の具体型 adaptation に推移性を導入していない。

#### 3.2.3 Capture と同じ使用への復元

FreshUse が作る同一使用の map を mu_j とする。a は nonlocal なので mu_j(a)=a、x_n は local なので fresh な mu_j(x_n) を作る（candidate_scheme.rs:1857–1888）。begin_candidate_fresh_bound は元の polarity と owner を保って、捕捉した shortcut を

$a≼{μ}_{j}({x}_{n})$

として復元する（同 2124–2170）。各 bound を復元し終えるまで root は使用先へ接続されない（同 2429–2447）。したがってこの使用の return effect を、古い a より小さい effect として自由に選ぶことはできない。

同じ議論を各使用 j に別々に適用できる。異なる使用の fresh local row を同一視する必要はない。共有するのは元から共有すべき a だけである。

#### 3.2.4 boundary 0 と root 自体が shared な場合

b=0 で level(a)=0、各 local row の level が正であれば、同じ証明がそのまま成立する。したがって reverse-owner index が boundary 0 で無効であることだけから、module Capture の意味保存失敗を結論してはならない。

x_n 自体が nonlocal の場合は、FreshUse が同じ x_n を使う。元の live session の bound は保持され、root コピーは作られない。この場合も incoming の元の辺を graph に複写することは、root の制約を保つための必要条件ではない。

#### 3.2.5 R187/R244/R245 への帰結

R187 が記述した relay の suffix を

${r}_{b}≼{c}_{u}≼{q}_{u}≼{r}_{u}$

とする。その記述どおり r_b が level 1 の shared anchor、c_u,q_u,r_u が level 2 の local row なら、上の定理は必ず r_b <= q_u と r_b <= r_u を作る。

この列の source との接続は次のとおりである。

| **辺** | **実際の生成経路** |
| --- | --- |
| r_b <= c_u | positive/negative Function の ResultEffect 比較。lib.rs:12687–12715、candidate_function_port_admit の Preserve 分岐 candidate_context.rs:3480–3514 |
| c_u <= q_u | source Apply slot 2。shadow_apply.rs:2780–2797 |
| q_u <= r_u | Lambda body-to-return slot 4。lib.rs:11377–11429 |

row-to-row source context は candidate_context_source により identity となる（candidate_context.rs:3323–3329）。元の R246 fixture は CandidateInference::solve を使い（local_source_observation.rs:230–247）、これは scoped experiment を有効にしない（shadow_apply.rs:812–822）。ResultEffect は identity の親を Preserve する。この普通経路に限れば、上記 identity/default の組を持つことはコード上の正の説明を持つ。

R245 の提案割当 r_b={signal}, mu_j(r_u)=empty は、捕捉・復元された r_b <= mu_j(r_u) を満たさない。**従って、その割当は通常飽和を含むこの slice の反例ではない。** これを source-level の solver bug として公開すべきではない。

ここで否定したのは旧候補の証明方法とその割当である。すべての source fiber、別経路、後続 level 変更、実 handler 選択までを列挙したとは述べない。R244 が問題にした元の slot-4 辺が omission され得ることと、その omission が root の意味を変えることを区別する必要がある。

### 3.3 定理3-B：上の chain では shortcut は root の全モデルを正確に表す

#### 3.3.1 identity-chain の正確な射影

任意の集合 E の冪集合を effect の領域とし、<= を包含とする。外側 anchor の値を A、公開する終点の値を R とする。中間 row に他の制約を加えない、この chain の局所的な意味について

$∃{X}_{1},…,{X}_{n−1}. A⊆{X}_{1}⊆⋯⊆{X}_{n−1}⊆R ⇔ A⊆R.$

**証明。** 左から右は包含の推移性。右から左はすべての中間集合を A と置けばよい。n=1 はそのまま同じ式である。□

したがって中間 row を全部 freshen しなくても、上の断片の root と anchor の観測には損失がない。この結果は「すべての内部割当がそのまま残る」ではなく、**中間を存在量化した正確な射影**である。中間 row 自体やそれに付いた独立の証拠も公開観測に含むなら、その観測を同じ式で捨ててはならない。

#### 3.3.2 nonidentity な closed zero-word filter への拡張

各段に、固定した許可集合 F_i を持つ closed filter があり、その段の条件が

${X}_{i−1}⊆{F}_{i} ∧ {X}_{i−1}⊆{X}_{i}$

であるとする。X_0=A, X_n=R と置く。この断片では

$∃{X}_{1},…,{X}_{n−1}. ⋀ni=1({X}_{i−1}⊆{F}_{i}∧{X}_{i−1}⊆{X}_{i}) ⇔ A⊆R∧A⊆⋂ni=1{F}_{i}.$

**証明。** 左辺から、各 A <= X_{i-1} <= F_i と A <= R が得られる。逆向きはすべての中間集合を A にする。□

この filter は架空の操作ではない。現行 candidate_zero_word_filters は closed weight の owner/position/空 word を検査し、受理した filter ごとに実際の lower <= Allowance(view) を登録する（candidate_context.rs:3530–3619,3704–3746）。closed Allowance への concrete contribution の検査は allowed.contains(effect) である（candidate_effect.rs:1214–1244）。replay の filter 合成は集合の共通部分に対応する（candidate_context.rs:1796–1800）。

旧 anchor a から各中間への shortcut ができれば、中間の Allowance upper と再度 replay し、必要な a <= Allowance(F_i) も生じる。これらは shared anchor の live 制約として残る。Capture が終点の shortcut を保存し、同じ外側 session を保つ限り、上式の二つの条件を保てる。

この定理は open tail、一般 PUSH/POP、provider ごとの grant、BothFromRight、又は一般の非推移的 concrete adaptation の証明ではない。意味を P_F(X,Y)=(X<=F and X<=Y) と明示した、現行実行可能な zero-word filter 断片の証明である。

### 3.4 定理3-C：現行 ScopeTransformer の合成は全初期状態について正しい

#### 3.4.1 実装と一致する denotation

ScopeTransformer は stamped と scopes を持つ（candidate_scope.rs:16–39）。集合として書き直す。

- S：新しく付ける InputRouteId の集合。

- 各 EffectScopeId s に対して k_s：元の protection を残す真偽値。

- A_s：Missing(tags) の tags 集合。条件は「少なくとも一つの tag が初期入力にない」である。

- 記録のない scope の既定値は k_s=true, A_s=empty。

初期状態を入力 tag 集合 I と protection 集合 P とする。M(A,I) を A の要素のうち I にないものがあるという命題と定義する。評価は

$T(I,P)=(I∪S, {s:({k}_{s}∧s∈P)∨M({A}_{s},I)}).$

これは evaluate の条件式 keep_initial && inherited || add.holds(initial_inputs) にそのまま対応する（同 180–209）。入力の並べ替えと重複除去は集合を変えない。

#### 3.4.2 合成式

先に T_1=(S_1,k_1,A_1)、次に T_2=(S_2,k_2,A_2) を実行する合成 T を、各 scope s について次で定める。

$S={S}_{1}∪{S}_{2},  {k}_{s}={k}_{1,s}∧{k}_{2,s},$

${A}_{s}=(if {k}_{2,s} then {A}_{1,s} else empty) ∪ {u∈{A}_{2,s}:u∉{S}_{1}}.$

**定理。** 任意の有限な I,P について

$eval({T}_{1}then{T}_{2},I,P)=eval({T}_{2},eval({T}_{1},I,P)).$

この等式の右辺は二段の逐次実行である。初期状態を空に限定しない。現在どの tag/protection が付いているか、同時に何個付いているかにも制約を置かない。

#### 3.4.3 証明

入力集合は (I union S_1) union S_2 = I union (S_1 union S_2) なので一致する。

任意の scope s について、二段目の protection の真偽を展開する。

$P{″}_{s}=({k}_{2,s}∧P{′}_{s})∨M({A}_{2,s},I∪{S}_{1}).$

$P{″}_{s}=({k}_{2,s}∧{k}_{1,s}∧{P}_{s})∨({k}_{2,s}∧M({A}_{1,s},I))∨M({A}_{2,s},I∪{S}_{1}).$

集合に関する二つの恒等式

$M(A,I∪S)=M({u∈A:u∉S},I),  M(A,I)∨M(B,I)=M(A∪B,I)$

を使うと、右辺はちょうど (k_s and P_s) or M(A_s,I) になる。すべての scope の membership が一致するので protection 集合も一致する。□

#### 3.4.4 コードへの完全な対応

ScopeTransformer::then（candidate_scope.rs:134–175）は、

- 行135で stamp 集合を union する。

- 行152–154で k_2 と k_1 の積を取り、k_2=false のとき一段目の add を捨てる。

- 行160–168で二段目の tags から S_1 を除き、一段目の残る tags と union する。

- 行169–170で、identity に等しい entry だけを省略する。release の keep_initial=false は、add が空でも tombstone として残す。

merge loop はソート済み二集合の最小の scope を一つずつ処理し、片方にない entry には上の既定値を使う。各 step で i+j が少なくとも一増え、有限に終わる。以上により、数式との対応に未列挙の entry の場合は残らない。

**系。** 任意長の有限 transformer 列は、その長さについて帰納的に then で合成でき、すべての初期状態に対して同じ結果となる。結合の括り方を変えても、評価結果は同じである。これは effect contribution の runtime 発生を仮定せず、有限 transformer の全状態意味論について成立する。

### 3.5 定理3-D：ScopeTransformer の remap は評価と可換

input identity の写像を mu_I、scope identity の写像を mu_S とする。各写像は transformer の support と初期状態の support の和集合上で単射とする。共有すべき anchor は固定する。freshening の場合は、既存 arena にない fresh identity を割り当てることで、この条件を満たす。

**定理。**

$eval(μT,{μ}_{I}I,{μ}_{S}P)=μeval(T,I,P).$

**証明。** 集合の像は union と可換である。単射性から u in I と mu_I(u) in mu_I(I) は同値で、従って M(mu_I A,mu_I I)=M(A,I)。scope 側も membership が同値である。k_s は名前変更で変わらない。§3.4の評価式に代入すれば、stamp と protection の各成分が一致する。□

実装 remap は stamp とすべての Missing(tags) から input support を収集し、各 distinct ID に一度 map を適用する。mapped support の衝突と scope の衝突を明示的に拒否する（candidate_scope.rs:214–264）。集合の並べ替えは順序番号の観測ではなく canonical set 表現を回復するためである。

**仮定の注意。** remap の内部チェックだけで、任意の外部状態に含まれる未登録 ID との衝突まで排除したとはいえない。全状態の上の定理には、上に明記した「transformer と初期状態を合わせた support 上の単射」が必要である。FreshUse の実 map が現在の全既存 ID から fresh な像を作り、外側 identity を固定することを適用側で使う。異なる level なら異なる scope とみなしてよい、という代替条件ではない。

#### 3.5.1 replay から FreshUse まで

candidate_context_begin_replay は lower flow の後に upper flow を実行する順序で compose_scopes を呼ぶ（candidate_context.rs:3904–3909）。compose_scopes は identity の場合を短絡し、それ以外は実際に first.then(second) を呼ぶ（同 2774–2782）。

prepare_candidate_fresh_use は一つの scope_remap からすべての captured relation の ScopedFlow を再構築する（candidate_scheme.rs:2036–2059）。したがって捕捉済み shortcut に含まれる composed transformer は、同じ use 内で正しい名前変更を受ける。§3.4・§3.5により、その **route tag/protection の変換** は元の逐次変換と一致する。

ここで state に effect member、実 provider、捕捉 grant、handler の正当性は含まれていない。candidate_scope.rs 自身もこれらを対象外と明記する。よって、この完全な代数証明を source の handler grant や残余 effect の健全性へ無条件に読み替えてはならない。必要な次の橋は、各 source event がこの transformer と同じ tag/protection 遷移を持つことである。

### 3.6 定理3-E：現行 context DAG と有限 graph の構文輸送

#### 3.6.1 現行 context の成功範囲

context_payloads が成功する grammar は次である。

K ::= I\
    | PrefixLeft(w, K)\
    | SuffixRightPops(K, w)\
    | Swap(K)\
    | Replay(K, K)\
    | WithoutLeftFilter(K)

各 child ContextId は parent より小さい。context_payloads は child をすべて辿り、weight を列挙する（candidate_context.rs:1669–1697）。BothFromRight は、authentic certificate の FreshUse owner がないため、この経路では明示的に失敗する（行1685–1686）。その場合を成功範囲へ黙って追加しない。

**定理。** finite な成功入力で、weight map が必要なすべての weight に定義されているとき、rename_fresh_contexts は各 original constructor を同じ constructor へ写し、child の順序と共有を保つ。

**証明。** ContextId の増加順について帰納法を用いる。Identity は Identity。単項 constructor では唯一の child が既に写され、その像と必要な weight の像を同じ tag に入れる。Replay では lower と upper を別々に既に写し、同じ順番で再構築する。rename_contexts_impl の match はこれら全場合を列挙している（candidate_context.rs:1592–1605）。同じ source ID の再出現は一つの remap を引くため共有が保たれる。caller が既存 map を渡した場合も再構築される constructor と等しいことを検査する（1615–1622）。child ID の不正な循環は先に拒否される。□

**評価に関する系。** 対応する weight に同じ意味値を割り当てる任意の constructor-compositional な解釈について、元と再構築後の評価が一致する。これは各 constructor の子について上の帰納法を適用することで従う。実際の detached evaluator の Replay は lower.left, upper.left の順、upper.right, lower.right の順で合成する（1760–1806）。上の構文輸送はこの順序を反転しない。

この系は、元の context evaluator が source の意味論を正しく表すという主張を仮定せず、同じ evaluator に対する再構築の保存だけを証明する。

#### 3.6.2 row map と term node

通常 Local/module 経路では Capture と prepare_candidate_fresh_use が連続して実行され、間に source constraint の solver 実行を挟まない（candidate_scheme.rs:2298–2303,1751–1753,1797–1816）。したがってこの区間の source canonical row と local/shared 分類は安定している。

row 再構築では canonical_rows が一つの source representative に一つの像を与える。local には fresh row、nonlocal には source row そのものを使う。Function node は AV・AE・RE・RV の四つの child を元の順番と polarity で再構築する。leaf は同じ atom、effect view は同じ source owner/position/allowed と map された tail を持つ（candidate_scheme.rs:1857–2034、candidate_effect.rs:1101–1124）。

**証明。** row loop について、処理済み representative の像が一意で、local な新規像は既存像と異なるという不変条件を維持する。term node は structural DAG で、循環は事前割当済み row を経由するため、Function child に関する構造帰納法が使える。行1978–1979の実装コメントと、finish 前後を分ける行2014–2030がこの順序に対応する。全 node constructor を上の三種類で尽くす。□

古い Graph を保存して、その後に canonical merge を行ってから単独で FreshUse する場合は、写像が単射にならず商になることがある。この場合は別の quotient 対応が必要であり、今回の連続 Capture/prepare の証明へ紛れ込ませない。

#### 3.6.3 一つの use での全 captured bound の復元

Graph が m 個の bounds を持つとする。Local use の loop 不変条件は次である。

- 0 <= next_bound <= m。

- index が next_bound 未満の bound は、その use の同じ row/context/evidence map によって復元済み。

- restoration=Some(id) の場合、id はちょうど next_bound の一つの未完了 owner operation を指す。

- next_bound<m 又は restoration=Some(id) の間、root を使用先へつなぐ最後の link はまだ開始されていない。正常な step の戻り点で complete=true なら、全 bounds の復元と root link の admission が終了している。

初期 cursor で成立する。restoration がないときは現在の bound だけを begin し、handle を保存する。handle があるときはその child が完了した場合だけ handle を外し cursor を一進める。next_bound=m になって初めて root を link する（candidate_scheme.rs:2429–2447）。root link の admission と complete=true の間には fallible な容量確保があるため、関数途中の全状態について complete=false なら未 link と主張することはしない。ここで対象とするのは成功した step と正常終了した route である。成功した route は同じ map と graph を一つの LocalFreshRoute に移す（758–788）。したがって正常終了した一つの route では、選択済みの各 graph entry に対応する復元を飛ばさず、他の使用の map へ取り替えない。□

これは **選択された m 個** の復元についての証明である。m が source に必要な全制約を表すという Capture 完全性は、定理3-Aのような source/solver からの別の接続を要する。

### 3.7 提案：全モデル輸送を選ぶ場合の semantic incidence 索引

現行 shortcut の意味的射影を全構文について証明する方法もある。ここでは、それに依存せず依存制約をそのまま捕捉する実装を選んだ場合の、具体的な代替を証明する。**この変更が現行 source のバグ修正に必須であると立証したわけではない。**

#### 3.7.1 追加する索引の単位

成功した BoundEmissionId が指す BoundAdmissionId とその RelationId を正本にする。pure な physical bound と、実行可能な context/scoped fiber を混同しない。BoundTransport { relation: None } の診断専用由来から、新しい identity fiber を捏造しない（candidate_effect.rs:532–543,708–716）。

各 semantic record e の依存先は、少なくとも次を含む。

1. canonical lower/upper の中の row。owner 側だけでなく両端。

1. Function の四ポート、effect view の tail。

1. relation の residual context DAG が参照する weight/view/tail。

1. scoped transformer の stamp、Missing 条件の input、scope。

1. deferred demand の Function root・output_scope・input・use instance。

1. 実行意味が参照する他の payload。純粋な source provenance の文字列や source位置は固定ラベルとして区別する。

列挙関数を deps(e) と書き、incidence[d] に e の既存 ID を登録する。型・effect row の local 判定は既存 level と non_generic、scope/input の local 判定は既存 source region の所有関係を使う。constructor に level を追加しない。

#### 3.7.2 admission の不変条件

公開可能な状態では次を満たす。

**I1（全登録）**：任意の保持中の semantic record e と任意の d in deps(e) について、incidence[d] から e を得られる。

**I2（正当性）**：索引中の ID は保持中の同じ record を指し、d が実際にその依存先である。canonical alias については class のいずれかの member の bucket にあることを許し、lookup は class 全体を読む。

**I3（fiber の区別）**：異なる relation/payload の record を端点対だけでまとめない。exact duplicate の省略には、その意味と必要な provenance の等価性を使う。

candidate_insert_bound_with_evidence の physical emission 完了点で、record と全 incidence をひとまとまりとして commit する。予約失敗で I1 を破る場合、その private result を公開しない。任意に省略できる completion observation と semantic 登録を分ける。完全 rollback はこの定理の前提ではない。

canonical merge では二つの class の member/bucket 列を結合し、既存 ID を失わない。raw record の source identity は書き換えず、端点の current representative を解決する。これは「同一化してよい」という source 証明ではなく、同一化後にも incidence を欠落させないデータ構造上の保存である。

#### 3.7.3 具体的な Capture 手順

1. root と公開する付帯証拠の local support を queue に入れる。

1. 未処理の local coordinate d を一つ取り、current class の全 incidence を読む。

1. 初見の semantic record e を bounds/payload table に記録し、deps(e) を列挙する。

1. local な依存先は queue に入れる。nonlocal な依存先は同じ anchor として登録し、それを経由して別の record へは進まない。

1. queue が空になるまで繰り返す。context や demand の latent payload から得た新しい local coordinate も同じ queue へ戻す。

seen のキーは record と canonical coordinate の双方に持つ。shape から来たかどうか、source slot が4かどうか、boundary が0かどうかを採否条件にしない。

#### 3.7.4 定理3-F：上の実装手順の列挙完全性

有限な成功 snapshot で I1–I3 が成立するとする。root の local support から、local coordinate を介した有限 incidence path で到達できる record は、すべてこの手順で捕捉される。また到達しない record を追加しない。

**証明。** record へ至る最短 path の長さについて帰納法を使う。最初の local coordinate は seed として queue に入る。帰納的に直前の local coordinate が処理されれば、I1 によって当該 record が列挙される。初見ならその全依存先が追加され、既出なら前回すでに追加済みである。このため path の次の local coordinate も必ず処理される。逆向きには、queue に入る coordinate は seed 又は既に到達した record の依存先であり、索引が返す record は I2 により実 incidence を持つので、各追加に実 path がある。有限 snapshot で各 coordinate/record を一度だけ追加するため停止する。□

I1 は結論の Capture 完全性を仮定していない。admission の各 constructor が、その有限 payload の全 field を索引に登録するという局所的で実装可能な不変条件である。capture の全 path を先に知る必要はない。

計算量は、訪れた coordinate/record と列挙した semantic incidence の総数に比例する。union-find で canonical class を引くなら、その lookup の償却費用を別に加える。全 session の全辺を使用ごとに走査する必要はない。

#### 3.7.5 定理3-G：この方式による snapshot 全モデル輸送

この snapshot の言語は、上の明示した row/leaf/Function/view と§3.6.1の context grammar、§3.4の scoped transformer、同じ binder tree に属する demand payload からなるものとする。自由な local name を参照する anchor 値は shared 側へ戻し、outer anchor の固定条件を満たす。rigid/binder の合法な写像条件は別途検査する。

各 local coordinate に一つの fresh image を事前割当し、同じ写像をすべての record と payload に適用する。anchor は固定する。

**結論。** 元の captured graph の全モデルと fresh graph の全モデルは、名前変更によって一対一に対応する。個々の ground model だけを後から別の map で説明する主張ではない。一つの use の構文的 map を先に固定し、その map ですべてのモデルを輸送する。

**証明。** row は対応する割当、leaf は同じ解釈、Function は四 child の解釈の組、view は固定 allowed member と map された tail であるため、term の構造帰納法で解釈が対応する。context は§3.6.1の同じ constructor による帰納法、scope は§3.5の評価可換性を使う。demand は同じ root と binder/input/scope の像を一つの map で持つ。よって各 semantic record の充足は元と像で同値である。すべての record の連言を取れば graph 全体で同値となる。fresh image 集合への全単射の逆写像を適用すれば逆方向も得られる。□

全 snapshot との境界接続では、捕捉されなかった record は捕捉した local coordinate に依存しないことを定理3-Fから使う。残りの session を満たす固定 anchor と外側の割当を保てば、捕捉部分の任意のモデルと結合できる。外側 session の矛盾を消したり、共有 store を勝手に local 化したりする操作ではない。

この全モデル輸送は、§3.3の中間を消去する射影定理より保存対象が強い。全内部モデル・joint payload を保持する契約を選ぶなら、shortcut だけでその契約を自動的に閉じてはならない。

### 3.8 公開後・使用後の更新

#### 3.8.1 現行コードについて確定すること

install_candidate_local_term は LocalScheme { capture_region, id, root, boundary } を保存するだけである（candidate_scheme.rs:2232–2247）。各 Local use 開始時に live root から Capture する（同 2275–2303）。module use も stored graph の live_root と boundary を取り、再 Capture する（同 1735–1753）。

したがって「最初の使用後に source bound が増えても、次の使用が必ず古い graph をコピーする」は誤りである。**次の使用前に増えた bound** については、新しい Capture の完全性が問題となる。

一方、すでに commit 済みの LocalFreshRoute はその時点の graph/maps を保持する。step_candidate_local_use が復元するのは、その graph の有限 bounds だけである。使用済み route の未捕捉 template-local row へ新たに bound が来たとき、そのすべての既存 image に自動配送されることは、このコードからは証明できない。

shared anchor の変化は別である。各使用が同じ live identity を保持し、通常の later admission が同じ row に入るため、局所コピーの更新を必要としない。shared anchor と generic template local を混同してはならない。

#### 3.8.2 後続制約のための具体的な更新プロトコル

全-model Capture を選ぶ場合、次の追加で stable な local/shared 分類の epoch 内の更新を扱える。

- 各 template は semantic record の append-only 集合 C_t と現在の捕捉集合 B_t を持つ。

- 各 use j は同じ template を指し、mu_j、配送済み record ID 集合 D_j、未配送 queue を持つ。

- 新しい use を生成した場合は、その時点の閉包 B_t 全体を初期配送し、以後の差分配送へ参加させる。

- caller がその use に追加する制約 U_j は、その use の所有物とする。**caller の特殊化を template 全体へ逆伝播して、兄弟 use を特殊化してはならない。**

- template に新しい record を追加したら I1–I3 を満たす incidence へ同時登録し、既存の捕捉 local support に触れる場合に閉包 queue を再開する。新しい record が新しい local coordinate を発見したら、その coordinate に接続する過去の record も同じ手順で読む。

- 増えた B_t の差分を既存の全 use へ配送する。各 mu_j を fresh に一意に延長し、同じ record/payload を写して復元する。

- 現在版の必要 record がすべて配送済みとなるまで、依存する結果を使用可能・公開可能としない。資源失敗時はその private result を止める。別の型候補を試すことや rollback を要求しない。

#### 3.8.3 定理3-H：有限の append-only 更新列に対する完全配送

更新期間中は local/shared 分類と binder 所有関係を固定し、template-local を外側 anchor が自由参照しないとする。更新は新しい semantic record/coordinate の追加のみとし、alias 変化は次節で別に扱う。

参照仕様を、その時点の template 全体に定理3-Fの Capture を最初から適用し、各使用に同じ map の延長で fresh graph を作ったものとする。これは古い成功結果の保存を仮定した仕様ではなく、更新された制約集合から一意に定まる再計算仕様である。

**結論。** 各有限の更新列を drain した後、増分法の捕捉 record 集合と、各 use が受け取る mapped record 集合は参照仕様と等しい。従って両者の全モデルは等しい。既存 caller 制約 U_j を連言しても等しい。

**証明。** 更新数について帰納法を使う。初期は定理3-F/G。新 record の追加で到達可能性が変わらなければ両方式とも以前の集合を保つ。変わる場合、新しい到達 path のうち最初に以前の捕捉集合から外へ出る辺は新 record 又はその後の flood に含まれる。両端 incidence と新 coordinate の展開によって、その path の全てを定理3-Fの最短 path 帰納法で列挙する。反対に、追加する record には実 path があるから余分なものは入らない。捕捉集合は追加のみなので、過去の差分を削除する必要はない。

各 use では D_j により一つの record ID を一度だけ配送し、map の既存定義を変えずに新しい coordinate だけを fresh に追加する。そのため最終的な mapped syntax は参照再計算と同じである。任意の有限 prefix における use 数・record 数が有限で、各差分の局所処理が有限なら queue は有限に処理できる。語彙の無限生成を排除する全 solver 停止性までは、この有限 prefix の定理で主張しない。構文が同じなのでモデル集合も同じであり、同じ U_j を連言しても等しさは保たれる。□

**時間に関する重要な区別。** 更新後のモデル集合が更新前と同じとは述べない。新しい source 制約はモデルを合法に減らし得る。示した等式は「同じ更新後仕様に対する増分計算と再計算」である。

#### 3.8.4 alias、level 変更、公開境界

同一化が起きる場合は、canonical incidence の bucket を結合するだけでなく、各 use の該当 image の等式も同じ source-qualified 操作として伝播する。a=b が template に正当に追加されたなら、各 use に mu_j(a)=mu_j(b) を追加する。この等式を満たす割当は商の同値類で一定となり、商の割当と一対一に対応する。これは商の通常の pullback/descend の証明であり、intrusion の source 正当性そのものとは別である。

local が shared へ分類変更される場合は、以前のコピーが新 anchor と同じものを表すべきかを source/generalization 規則が決める必要がある。決まっていないのに map だけを置き換えて、過去の使用が直ったとみなしてはならない。真に同じ anchor を表すべき変更なら、既存 image との等式を明示して全 consumer へ replay する。別の意味なら、その境界の合法な凍結時点を source schedule から証明する必要がある。

module SCC では全 member の source schedule を完了してから graph を staged/public にすることが実装されている（candidate_scheme.rs:1622–1705）。これは有用な境界だが、局所 let、外側の later bound、alias による更新が一切ないことの全証明ではない。定理3-Hをそのまま現行全 source に適用したとは述べない。

### 3.9 実装判断へ返す、具体的な残りの仕事

1. **R245 の旧候補割当を反例として扱わない。** 完全な same-use inventory には、元の辺だけでなく replay が生成した shortcut とその relation/context/scoped payload を必ず含める。既存 observer は四つの target bound と slot-4 bound を確認するが、全 bound inventory は print のみである（local_source_observation.rs:260–265,383–404,417–438）。

1. **identity chain と closed filter chain の証明を再利用する。** これらを receipt 必須の特別規則で修正しない。boundary 0 も含めて、ordinary positive/lower lane からの Capture を検査する。

1. **nonidentity payload の代数は§3.4–3.6で閉じる。** 次に必要なのは source Call/entry/return と実 provider の対応であり、同じ scope 合成を再び小補題へ分割することではない。

1. **必要な保存対象を固定する。** root への意味的射影で足りる箇所は§3.3型の存在量化の等価性を証明する。元の joint body/context/evidence の全モデルが契約なら、shortcut だけの議論では足りず§3.7の incidence 方式が明快である。

1. **lifecycle を route 作成時点と作成後で分ける。** 次の使用は再 Capture される。過去の使用への template 更新は、source が起こさないことの証明又は§3.8のような配送規律が必要である。現在の graph/map 保持がそれだけで通知機構になるわけではない。

本稿の新しい中心結果は、「Capture の不足を疑う」から一歩進み、**実装がすでに正しく回収する finite chain を証明し、旧候補反例の不足を特定し、nonidentity な scope transformer の全状態意味論を証明したこと**である。source/runtime の残る橋を、この完了した代数や再構築の証明と混同しない。

### 3.10 主要な固定コード参照

すべての行番号は冒頭の固定 commit のもの。

- [Capture の物理所有・逆索引・展開](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_scheme.rs#L821-L1412)

- [Capture の payload 閉包と source SCC 境界](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_scheme.rs#L1469-L1705)

- [FreshUse の row・term・context・scope 再構築](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_scheme.rs#L1818-L2170)

- [Local の毎使用 Capture と復元 cursor](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_scheme.rs#L2228-L2478)

- [片側所有と反対 lane replay](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_extrusion.rs#L684-L977)

- [Context の完全な ordered replay 生成](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_context.rs#L3853-L3935)

- [ScopeTransformer の then/evaluate/remap](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_scope.rs#L95-L265)

- [Context DAG の構文 rename](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_context.rs#L1523-L1697)

- [実際の R187 source fixture と assertions](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/shadow_apply/local_source_observation.rs#L205-L438)

- [R244](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/theory/2026-10-21-r244-forwarding-capture-cuts.md)、[R245](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/theory/2026-10-21-r245-receipt-loss-admission.md)、[R246](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/theory/2026-10-21-r246-r187-source-qualification.md)

## 4 任意の同時利用文脈に対するCapture置換

### 4.1 対象と前提

有限な制約領域を、内部の行変数集合 $Q$、外側と共有する固定アンカー集合 $R$、制約の有限な多重集合 $C(Q,R)$、公開する観測タプル $T(Q,R)$ で表す。制約は単なる端点対ではなく、occurrence、admission/emission、relation context、source input、scope、およびそのpayloadを含む。異なるcontextを持つ同じ端点対を同じ制約として潰さない。

外部領域の変数を $X$、外部制約を $D(R,X)$ とする。観測は公開タプル**全体**の同時α同値類で取る。ここで変えてよいのは内部の型・証明用の名前だけであり、外部アンカー、実行上のprovider、event、および観測可能な値は固定する。各座標を独立にα変換して共有を消す商ではない。rawな内部IDそのものを比較する場合は、後述するようにclient側の述語も対応写像で輸送する必要がある。次の四条件を置く。

1. **境界の完全性。** 外部制約・外部観測から内部変数を直接参照しない。外部への接続は公開タプルと $R$ を通る。$C$ 内の全payloadの自由な依存先は $Q$ または $R$ に含まれる。内部変数に制約を課す元の制約はすべて $C$ に含まれるか、$C$ と $D$ から同じ作用域のまま同値に再現できる。

1. **同一写像。** 一回のfresheningは、根、すべてのbounds、relation contextのDAG、scope、source input、公開タプルに一つの対応写像を一貫して使う。固定アンカーはそのまま保つ。

1. **作用域の保存。** fresh名の宣言位置と、依存してよい外側のbinderを保存する。名前の置換だけで元の量化順序を移動しない。

1. **名前に対する同変性。** 許された名前の全単射によって制約の充足、項の観測、binderの許容履歴が保存される。これは名前を識別子として扱う意味論の性質であり、任意の書換えの健全性ではない。

第一条件の「同値に再現」は、以降の証明で自由に利用できる包括仮定ではない。実装に適用するとき、当該の省略に対する独立した保存証明が必要である。単に根からboundsを辿ったことだけでは第一条件を満たしたことにならない。

### 4.2 定理4-A1：Captureの文脈的置換

任意の有限な使用回数 $n$ を取る。各使用 $i$ に対し、独立な元領域のコピー ${C}_{i}({Q}_{i},R)$ と、Captureからfreshenした領域 ${C}_{i}({Q}_{i},R)$ を用意する。${Q}_{i}$ 同士、${Q}_{i}$ 同士は互いに素である。使用ごとに、対応する局所binderも含めた作用域保存全単射

${μ}_{i}:{Q}_{i}→{Q}_{i}$

があり、${μ}_{i}$ は $R$ 上で恒等、${C}_{i}={μ}_{i}{C}_{i}$、${T}_{i}={μ}_{i}{T}_{i}$ とする。

さらに任意の外部変数 $Z$、任意の外部制約・観測述語

$K(R,X,Z,{[{T}_{1},…,{T}_{n}]}_{α})$

を取る。$K$ はこの観測域上で任意であり、複数回の使用結果を同時に比較してよい。現在のソースコードから生成できる述語に限定しない。元のbinder木を同じ位置で評価する限り、次の二つの系は、外部変数と公開観測の**同時の関係**を同じにする。

$D∧⋀ni=1{C}_{i}∧K,  D∧⋀ni=1{C}_{i}∧K.$

**証明。** 各 ${μ}_{i}$ の定義域・値域は互いに素で、固定集合 $R$ では一致する。したがって和を取り、外部名上の恒等写像を足して、一つの名前の全単射 $μ$ を作れる。元の充足割当て $v$ から新しい割当て $v$ を、各内部名 $q$ について $v(μq)=v(q)$、外部名について $v=v$ と定める。局所binderが名を含む値を生成する場合は、その値にも同じ名前の全単射を作用させる。

前提4より $v⊨{C}_{i}$ と $v⊨μ{C}_{i}$ は同値である。公開タプルは同じ一つのα変換で対応するため、タプル全体の同値類が一致する。$D$ は内部名を参照しないため保存される。$K$ の引数が同じなので、複数使用間の相関を含めて真偽が一致する。逆写像 ${μ}^{−1}$ で新しい充足割当てから元の割当てを戻せる。ゆえに充足解の間に全単射があり、外部への射影が一致する。これは使用ごとの周辺関係の一致より強い。□

rawな名前を含む観測空間では、同じ証明から関係の同型を得る。任意のraw述語 $K$ に対し、対応するclientを $K=K∘{μ}^{−1}$ として輸送すれば真偽が一致する。輸送せずに内部IDの文字列や番号を比較する任意の述語まで不変だという主張はしない。元のYulangの公開観測と独立したproduction viewが、この境界と名前の同一性をどう与えるかは、ソースとの接続で確かめる。

### 4.3 元の量化依存を保った証明

前節の割当てに対する議論を、依存する存在証人の選択に持ち上げる。元のbinder木の各位置 $b$ で、それ以前に見えてよい履歴を ${H}_{b}$ とする。履歴 $h$ の下で型・scopeが許す値域を ${V}_{b}(h)$ とする。存在binderの戦略は、各 $h∈{H}_{b}$ に対して ${s}_{b}(h)∈{V}_{b}(h)$ を選ぶ関数であり、未来の普遍binderの値を引数に取れない。

作用域保存写像は、履歴の全単射 ${μ}_{H}$ と、各履歴でのfiberの全単射 ${μ}_{b,h}:{V}_{b}(h)→{V}_{b}({μ}_{H}h)$ を誘導する。新しい戦略を

${s}_{b}({μ}_{H}h)={μ}_{b,h}({s}_{b}(h))$

と定める。これは元と同じ深さの履歴だけを読む。普遍binderの各挑戦も同じ全単射で対応する。葉の制約では定理4-A1の同変性が成り立つので、binder木の葉から根への帰納法で、勝つ戦略の存在が双方向に保存される。

したがって証明は、たとえば $∀a ∃b(a)$ を $∃b ∀a$ に変換しない。$μ$ は制約生成時に一度選ぶ構文上の写像であり、各挑戦を見てから都合よく選び直す写像でもない。□

この結果は任意の $K$ に対する置換を許すため、将来の独立したclientを現在のsource imageに制限しない。ただし独立したproduction viewの全てがそもそも $C$ で表現されるか、観測がソース意味論と一致するかは別定理である。置換定理だけから、その表現完全性やprincipal typeを結論しない。

### 4.4 定理4-A2：fresh copyの一様な因子分解

一つのfresh copy $μ:Q→Q$ を固定する。元の領域の任意の**合法な構文的instance**を与える置換 $θ$ を取る。$θ$ が項へ置換するのはflexibleな座標だけであり、束縛名・剛体名には合法なα改名だけを許す。共有アンカー、source occurrence、実際のprovider/eventは固定する。sortと作用域を守り、束縛名のcaptureを起こさない。

$η(μq)=θ(q),  η(r)=r (r∈R)$

と定義する。このとき

$η(μC)=θC,  η(μT)=θT.$

**証明。** 変数では定義そのものである。head、ordered port、bound、contextの各構文形成子では、全ての子に帰納法を適用して同じ形成子を再構成すればよい。束縛形成子では、作用域保存条件から共通のfreshな束縛名へα変換して帰納法を適用できる。同じ変数が複数のpayloadに現れる場合も一つの $η$ を使うため、その共有が保たれる。したがって有限な構文全体に構造帰納法が適用できる。□

これはfresh copyが合法な構文的instanceを一様に生成する普遍性である。任意のsemantic viewが合法な構文的instanceである、という完全性の証明ではない。型の表示を最小化する定理でもない。

### 4.5 実装への適用時に残る具体的な項目

この定理で必要なのは、rootだけをコピーすることではなく、境界を跨ぐ相関を一回の写像で保つことだ。ConstraintOccurrenceIdだけをキーに異なるRelationIdのfiberを潰した場合、前提2を満たさない。FactId、BoundAdmissionId、BoundEmissionIdのどれを同一視するかも、実際に保持する関係を基準に決める。

また、この定理は一時点の領域と各使用時点のcopyを比較する。live rootの再Captureは、将来作る使用へ新しい制約を反映する。既に作った使用へ後続制約が必要か、必要な場合にどのように届けるかは時間方向の別の不変条件であり、名前の全単射だけからは従わない。

## 5 Extrusion・Value SCC intrusion・一般化

本章の原命題は、元のsource、合法なjoint use、元のbinder/provider/event/effectを保ち、実Value参照SCCで選ばれたextrusion occurrenceの親子を等置したときの保存である。以下では、ordinary copyの構文的消去、現コードの共有、scope下降の条件、元source frameを保つ提案構成を分けて証明する。最後の提案構成が現コードで実現済みだという結論は出さない。

### 5.1 実装と source occurrence の対応

#### 5.1.1 SCC の対象を確定する

candidate_value_graph.rs:5–8 の vertex は Module / Local / Parameter / CatchBinder / Expression という source Value であり、solver row とは別の型である。retain_source は各 source-owned initializer/body の Name をその owner から解決済み binder への辺として追加する（同ファイル 84–100,145–158）。nested initializer を外側 owner に混ぜない。

Apply occurrence の origin は owners[index]、receiver は callee を Group / Ascription 越しに解決した Value である（77–82,204–219）。qualifies は二つの source Value の component equality を検査する（254–255）。型の <: 辺はこの検査の入力ではない。

**補題1：fragment helper の導入は source Value 間の到達可能性を変えない。**

比較する二つのグラフを次のように具体的に定義する。

- 展開グラフ：実装どおりの helper vertex と辺を持つ。

- 圧縮グラフ：helper-only path v → h₁ → … → hₖ → w を semantic Value 間の辺 v → w に置換する。direct owner-to-Name edge も保持する。

前者の source Value 間の path を、途中に現れる semantic Value で分割する。各区間は helper-only path か direct edge なので、後者の一辺へ縮められる。逆に後者の各辺を、その定義に用いた前者の path へ展開すればよい。双方の到達可能性が一致し、従って source Value 上の SCC も一致する。実装は Name helper を resolved Value へ結び、Apply / If / Sequence helper を選択された child helper へ結ぶ（162–219）ので、この圧縮定義そのものである。これは有限グラフに関する完全な証明であって、型の健全性を前提にしない。

この補題は、どの source fragment を対象とするかという source 規則自体の正しさまで証明しない。特に Lambda / Block を経由する Apply fragment membership を、存在しない辺で補わない。

#### 5.1.2 実際の extrusion occurrence

candidate_extrusion.rs:20–35 は呼出しごとに occurrence と局所 memo を作る。row の level が target 以下なら元 row を返す（90–103）。若い row は target level の copy を作り、親・極性・target・occurrence を記録し、memo を登録してから bounds をたどる（104–174）。

正極性では parent ≤ copy を入れ、親の lower bounds をコピーする。負極性では copy ≤ parent を入れ、親の upper bounds をコピーする。Function の port 順序は (argument, argument_effect, result_effect, result) であり、先頭二つだけ極性を反転する（235–264）。Work::Function はこの四つの順序を保って再構築する（candidate_extrusion.rs:356–386 付近）。

candidate_intrusion.rs:324–364 は現在処理中の関係の source set に qualifying event があれば、この occurrence の実際の親子を pending に登録する。568–595 は pending pair 全部を merge する。通常 drain の空 queue で settlement が呼ばれる（lib.rs:12134–12138,12401–12404）。従って「あとで常に local use の後へ equality を遅らせる」という別のアルゴリズムを現実装の説明として使えない。

source seed の直接対応は candidate_context.rs:3331–3351 にある。checking occurrence から source event を引き、singleton source set を作る。一方、派生関係では union_sources が source set を合併する（3066–3072）。any(qualifies) が後の extrusion を正しく occurrence-qualified に扱うことを全派生経路について示すには、**複数の source に由来する関係のどの demand を今コピーしているか**の証明がなお必要である。単に set に qualifying ancestor が一つ入っていることは、完全な source-demand 対応の証明にならない。この文書のコピー構造の定理は、この provenance 問題と独立に成立する。

### 5.2 定理5-A：実際の extrusion を全対 intrusion したときの構文的消去

#### 5.2.1 定義と対象

typed row の集合を V = V_value ⊎ V_effect とし、term を row、固定 atom、四引数 Function から作る。Function の四引数の sort は (value,effect,effect,value) である。ここで扱う「ordinary bound」は、この term 間の関係の occurrence である。relation の source label は保持するが、別途生成される context transformer や effect permission の意味は本定理へ混ぜない。

一回の完了した extrusion Ext(t,p,l) を考える。コピー前の ordinary bound occurrence 群を S、実際に作られた copy 集合を N、戻り term を t′、直接追加された bound occurrence 群を D とする。これらはraw termを含んでよい。開始時の古いrowのcanonical mapを κ とし、構造IDをordered constructor syntaxへ展開した全termの、**全ての子row**へ再帰的に作用させる。κ はこのinvocation中に固定される。Work::Functionのchanged=false経路がraw aliasを含む元構造termをそのまま返す場合も、結果側をこのreadbackの対象から除かない。既に同一化されていた別のsource declarationがこのnormalizationで無条件に合法になるとは主張しない。

実装と同じく、構造 node を終えてから pending bound を処理し、copy の memo は selected bound をたどる前に登録する。ordinary skeletonのinvocation内に別のmergeやsource mutationは挟まない。extrusion本体が終わった後にpending intrusionをsettleする現行の通常drainとの対応である。

消去写像 π は次で定義する。

- 古いraw row a ∈ V について π(a)=κ(a)。canonical representativeでは κ(a)=a。

- この invocation の実際の copy c について、記録済み parent が a なら π(c)=π(a)。

- atom はそのまま、Function は**四つの子すべて**へ同じ π を適用する。

新しい copy の親がこの invocation 内で既に作られた row でも、allocation order が小さい親へ進むので π は有限に定義できる。bounds が循環していても、親の allocation order と構造 term の有限性は変わらない。bound cycle を無限展開する定義ではない。

#### 5.2.2 命題

**定理5-A。** 上記の actual extrusion の ordinary skeleton について、

$π(t′)=κ(t)$

が構文上成立する。さらに D の各 occurrence を π で写すと、κ(S) の元の occurrence と同じ typed relation、または反射的 row link a ≤ a になる。従って、この invocation の**全ての retained parent/copy pair**を等置し、新copyを消去したrelation programは、再帰的canonical readback後の元 κ(S) と同じdemandに、元clauseの重複と反射的linkを加えたものである。すべてを初めからcanonical syntaxで記した場合には κ(t)=t、κ(S)=S である。

元のdemandが K[t] で、extrusion後に K[t′] が保持された場合も、π(K[t′])=κ(K[t]) である。K は input / result / effect / provider / scope 等を持つ任意の固定された typed tuple context でよい。π が作用しない実行上の provider や source identity は変化しない。

この定理は、具体的 adaptation の推移性を要求しない。等しい whole tuple に同じ局所述語を適用するだけである。使用する論理法則は、同じ clause の重複を消せることと、row の identity link が真であることだけである。

#### 5.2.3 証明

実際の work item の処理に対し、次の二つの不変条件を同時に示す。

1. memo に入った (u,p,l) ↦ v は π(v)=π(u) を満たす。uが古いcanonical termだけなら右辺はuである。

1. これまでに挿入されたboundは、πの下で元の κ(S) のclauseまたは反射的linkになる。

**古いlevelのrowとatom。** rowはcanonical representativeを返すので、κの冪等性から π(κ(a))=κ(a)=π(a)。atomは同じtermを返す。boundの追加はない。

**若い row**** ****a**** ****の最初の訪問。** c を作った時点で π(c)=π(a) と定義する。新 link は正なら a≤c、負なら c≤a であり、いずれも π(a)≤π(a) になる。memo はこの時点で登録されるので、その後 cycle から戻って来ても同じ c を使う。

**selected bound。** 正なら親の lower occurrence b≤a、負なら upper occurrence a≤b が選ばれる。子 traversal が返す b′ は1によって π(b′)=π(b)。コピーされる関係はそれぞれ b′≤c または c≤b′ なので、消去後は選ばれた元の関係そのものである。

selected boundがinvocation開始前から存在した場合は、消去後に κ(S) のclauseになる。途中で追加されたboundが選ばれた場合には、不変条件2により、既にその消去は κ(S) のclauseまたは反射的linkである。これは親子linkだけでなく先に複製されたordinary boundにも同じく適用できる。実装はselected listの長さを親linkの挿入前にsnapshotするが（105–119）、別極性の処理が先に作ったboundを後の訪問が見る場合も、この二分に含まれる。よって「選ばれたboundsは全て開始前のもの」という偽の前提は不要である。

**Function。** 四つの子に1を適用する。argumentとargument-effectで極性が反転するのはコピー対象を決めるためであり、消去後には各子が元の同じcanonical readbackへ戻る。changed=trueなら再構成した四子に帰納仮定を使う。changed=falseならraw aliasを含む元構造が返っても、πが全ての子にκを適用するので同じ結果になる。どちらも元Functionのcanonical readbackと構文上同一である。

**memo hit。** 既に成立している1を利用する。bound cycle に対する追加の帰納法は要らない。

以上でwork itemの全ケースが成立し、最後のroot memoから π(t′)=π(t)=κ(t) を得る。全親子の等式で new copy を消去すると、1・2により主張した relation program になる。□

#### 5.2.4 実装への適用範囲

この定理は candidate_extrusion.rs の通常 row / Function / ordinary copied bound の構成に適用できる。IncomingAllowance、effect view の identity、context、attachment、source-fiber の輸送は別の payload を持つため、**ordinary skeleton の消去から全意味の消去を推論しない**。

effect view は candidate_effect.rs:1127–1142 で tail に従いコピーされ、candidate_extrusion.rs:269–302 で新 view の ID を返す。この view の固定 declaration・permission・attachment と context 上の現れる場所を、同じ source view の capture-avoiding copy として解釈できる証明が必要である。tail だけを親に戻したという事実では足りない。

また、この定理は level を含まない relation program の定理である。intrusion が parent の level を下げることは、次節（§5.3）で別に扱う。ここを省略すると、local equality の証明をそのまま Generalize 保存へ誤用してしまう。

### 5.3 定理5-B：現実装の商クラスと FreshUse の正確な共有関係

#### 5.3.1 merge が持つ metadata

開始時点のcanonical classを一つのseed v とし、その代表に保存されたlevelを ℓ₀(v)、non-generic flagを n₀(v) とする。raw aliasの古いmetadataを別seedとして数えない。以下のB1は、独立したlevel変更やnon-generic更新を挟まない、正常に完了した有限merge列について述べる。別更新を挟む場合は、その更新後を新しいseed状態として読む必要がある。境界 b での現コードの判定は

${local}_{b}(v)⇔ℓ(v)>b∧¬n(v).$

これは candidate_scheme.rs:969–994 にそのまま実装される。merge は同じ sort の row だけを結び（candidate_intrusion.rs:619–623）、代表の level を min、non-generic を OR にする（666–691）。

**定理5-B1：metadata の商。** 有限回の正常に完了した merge 後、商クラス [v] の代表は

$ℓ([v])=minu∈[v]{ℓ}_{0}(u),  n([v])=⋁u∈[v]{n}_{0}(u).$

従って

${local}_{b}([v])⇔⋀u∈[v]{local}_{b,0}(u).  (B1)$

**証明。** singleton class では定義そのもの。二つの既存 class を merge する一歩では min の結合則と OR の結合則によって union class の式になる。既に同じ representative なら操作はなく、式も変わらない。path compression は equivalence class も metadata も変えない。有限 merge 数に関する帰納法で成立する。最後に min ℓ > b は全 ℓ>b と同値、¬∨n は全 ¬n と同値なので B1 が従う。□

ここで「古い level は source で本当に固定すべきである」とは仮定していない。証明したのは、現コードがどの row を共有するかという正確な性質である。

#### 5.3.2 複数 use の可換図式

境界 b で local な original row の集合を Q、fixed な集合を R とする。use i の通常 freshening f_i は v∈Q を別 row (i,v) に写し、r∈R は共有のままにする。distinct use の fresh images は disjoint とする。これは fresh allocation の identity 不変条件である。

intrusion の equivalence relation を E とする。全 use の raw incidence graph を作り、各 pair uEv を各 use へ同じ f_i で輸送する。この transported equality の推移閉包を E^I と書く。**この閉包は等式の推移閉包であって、具体的 adaptation の推移閉包ではない。**

**定理5-B2：freshen と quotient の可換性。**

- [v]⊆Q なら、use ごとに一つずつ異なる class (i,[v]) ができる。

- [v]∩R≠∅ なら、全 use の [v] の image は同じ class に属する。

この分類は、先に E で quotient し、B1 によって class の一般化可否を決めてから FreshUse する結果と同型である。

**証明。** E の一本の path を f_i で写すと、同一 use 内の等式 path になる。[v] が Q のみからなる場合、use をまたぐ vertex はなく、equality の edge も同じ use 内だけなので二つの use は接続されない。一つでも fixed r∈[v] があれば、各 f_i(v) から同じ r への path がある。従って全 image が connected になる。ほかの class との edge は存在せず、これが全ての equivalence class を尽くす。B1 は、ちょうど前者だけを freshen すると述べているため同型が得られる。□

同型は term、bound、Function の全 port、任意の joint predicate の**全ての出現**へ同じ写像を作用させれば保存される。四つの port を別々の fresh map で処理する結論ではない。

#### 5.3.3 現 FreshUse との対応と stale snapshot

prepare_candidate_fresh_use は現在の representative を取り直し（candidate_scheme.rs:1860–1861）、同一 representative に対して canonical_rows で一つの image を共有する（1862–1871）。新規割当ての条件は

row.local && current_level > graph.boundary && !current_non_generic

である。normal local useは capture_candidate_graph_owned の直後に prepare_candidate_fresh_use を呼ぶ（2298–2305）。**captured rowsのimageを割り当てる部分に関して**、この経路はB1・B2の分類を実現する。必要な全row・全incoming relationをCaptureが漏れなく取得したという別の証明まで、この局所対応からは出ない。

以前の snapshot を利用する場合も、capture 以後に level が下がる・non-generic が立つ・class が合併するだけなら、local から fixed への変更を current metadata が検出する。fixed が local に戻らないので、同じ canonical class の複数 snapshot row の順序によって fresh/fixed が分かれることはない。rollback をまたいで失効した snapshot を再利用してよいという定理ではない。

#### 5.3.4 何が新しく確定したか

正極性コピー a≤c が target b にあり、a が originally level >b である場合、a=c の merge 後は a も境界 b で fixed になる。これは heuristic ではなくB1の直接の系である。各 local use はB2によりこの同じ fixed class を使う。

従って「本当は independent use で親の type description が変わり得るが、コピーの低 level は保存したまま equality だけ追加する」という構成は、その独立性を保存しない。source scope がもともと共有を要求している場合には正しい。source scope が独立性を許す場合には、それを正当化する別の証明が必要になる。

### 5.4 定理5-C：古い source scope への戦略因子分解

#### 5.4.1 定義

source declaration a が読める環境の集合を Ω_a、古い copy scope が読める環境の集合を Ω_c とする。環境は単なる型代入だけでなく、そこまでに導入された description parameter、shared binder、合法に先行する universal challenge 等を含む。元の telescope が許していない将来の event や continuation は含めない。

忘却写像 r:Ω_a→Ω_c は、古い scope から見えない情報を落とす。到達可能な environment に限定し、Ω_c=r(Ω_a) とする。親の strategy は A:Ω_a→D。ここで D は同じ sort の semantic description を比較できる共通の台集合であり、その全要素が古い scope で合法だとは仮定しない。各 z∈Ω_c について、古い telescope の environment z で well-scoped な description の集合を D_c(z)⊆D とする。これは sort の一致だけでなく、自由な rigid / nominal identity、固定 binder、provider 等の support がその telescope で許されることも含む。binder の内側で封じられた identity と自由な identity は区別する。

ここでいう**古い scope で許される semantic strategy**は、関数 C:Ω_c→D で、各 z について C(z)∈D_c(z) を満たすものをいう。copy がこの意味で古い scope に置かれたまま a=c を満たすには、さらに

$A=C∘r  (C0)$

となるものが必要である。

#### 5.4.2 必要十分条件と証明

**定理5-C。** C0 を満たし、すべての z∈Ω_c で C(z)∈D_c(z) となる semantic strategy C が存在することと、次の二条件の両方が成立することは同値である。この C は到達可能な古い environment 上で一意である。

$r(ω)=r(ω′)⇒A(ω)=A(ω′)  (C1)$

$A(ω)∈{D}_{c}(r(ω))  (ω∈{Ω}_{a}).  (C2)$

**必要性。** C0 なら、同じ r(ω) に同じ関数 C を適用するため、二つの A は等しくC1が成立する。C(r(ω))∈D_c(r(ω)) とC0からC2も成立する。

**十分性。** 各 z∈Ω_c について、r(ω)=z を満たす任意の ω の値を用い C(z)=A(ω) と定義する。C1 により値は代表の選択に依存しない。C2 によりその値は D_c(z) に属する。C の入力依存性は z だけであり、出力の自由 support も古い telescope に収まる。定義からC0が成立する。C0を満たす別の C′ があれば、各 z=r(ω) で C′(z)=A(ω)=C(z) なので一意である。□

この証明は「合法な下降がある」を仮定していない。**関数の入力依存性と出力の scope support**を保つ因子分解の条件を、元 strategy から導出した。ただし、得られた C を特定の source constructor の項として表現できることや、追加の局所 constructor law を満たすことは、この集合論的な因子分解だけでは証明されない。それらを source の typing 導出へ適用するときは別に示す必要がある。

特にC1だけでは不十分である。新しい private rigid κ が古い telescope に存在しないとき、全履歴で A(ω)=κ とする定数関数はC1を満たす。しかし自由な κ は D_c(z) に入らずC2に失敗する。κ を正しい binder の内側に封じた description が古い scope で合法な場合とは区別する。固定した値域 D を初めから全 environment で古い scope に合法な値だけに限定した特殊な場合に限り、C2は自動的になる。

#### 5.4.3 finite-use discriminator

古い環境が一つだけで、Ω_a が二つの独立 use i=0,1 を区別できるとする。A(0)=int、A(1)=unit と置けば、r(0)=r(1) だが A(0)≠A(1) なので下降できない。一方、親が source 上も本当に shared で A(i)=T、かつ T∈D_c(*) なら C(*)=T でよい。

**SCC equality はC1もC2も導かない。** SCC は resolved Name reference の path の存在で決まり、independent use index、binder telescope、description の自由 support を検査しない。§5.1.1の actual graph でも、この違いは明示されている。

ただしC1またはC2の失敗だけで、必要な主型被覆が失われたとは断定しない。被覆は内部 strategy の変更を許すことがある。**同じ公開観測を保つ別の source strategy が存在しない**ことまで示す必要がある。次節の two-use 条件は、その変更の余地をなくす具体的な observation を与える。

### 5.5 two-use 障害を現在の source 機構へ接続する

#### 5.5.1 対象 source と Name owner

過去の研究で得られた小さい source discriminator を、現在のコードへ接続する。

my answer = {\
  my f x = {\
    my g y = { my drop z = y; drop (f y) };\
    my first: int = g 0;\
    g ()\
  };\
  f\
}

これは新規に実行した parser / compiler 結果ではない。既存の notes/progress/2026-10-12-intrusion-admitted-two-use-witness.md にある候補と同じ source である。元の研究の「source event endpoint が未保持」という当時の障害は、固定版にはそのまま適用できない。

現在の Graph::retain_source を構文どおり追うと、F は最後の g () により F→G を持ち、G は drop (f y) により G→F を持つ。first の initializer は別 owner なので、その g 0 は First→G である。drop の initializer の y は Drop→Y であり、Gのown source bodyをFの参照へ置き換えない。従ってFとGの同一SCCは、実コードのsource-Name辺から導ける。

f y の Apply event は§5.1.1の construction により origin=G, receiver=F となる。型行B/CのSCCは計算しない。

#### 5.5.2 現在確定できる generalization incidence

source traversal は local initializer だけで level を増やし（candidate_source.rs:1057–1064）、lambda 本体は同じ level を使う（1015–1055）。f の initializer level を k とすれば、g の正式引数 y の row B は k+1、g publication boundary は k である。

active initializer 中の f の Name は fresh scheme を開かず、同じ initializer endpoint へ Link される（1343–1349）。g publication 後の二つの Name はそれぞれ Action::Local となり、local scheme は root と boundary を保存する（candidate_scheme.rs:2232–2247）。各 use は現在 graph を capture し、一つの coherent map を作る（2298–2305）。

実際にその f y demand を level k へ negative extrusion した occurrence が作られたなら、argument B の positive copy C は level k、link は B≤C になる。qualifying source event が保持されたこの occurrence の merge は B=C を入れる。**B1・B2により、その後のgの二つのuseでBは必ず同じfixed representativeへ写る。** 当時のノートで条件だった native level/classification の部分について、現コード上の帰結を確定できる。

ここで「candidate のどの dispatch path でも必ず同じ実際の demand occurrence を作る」まで無検証で主張しない。source seed、Link/replay、extrusion の全関係履歴が同じ occurrence を運ぶことは、§5.1.2で区別した別の対応義務である。

#### 5.5.3 障害の代数的な核心

g が戻すのは y である。drop は Value parameter なので、呼出し元が先に f y を評価するのではなく、**calleeを先に評価し、whole delayed argument**** ****f y**** ****をdropへ渡し、Value entry がそれをforceしてからyを返す**。この説明を普通の caller-side CBV に置き換えない。force が返らず発散する可能性は型推論の反例を自動で無効にしないが、発散を理由に各source typing premiseが証明済みになるわけでもない。

g の同じ source result correlation を保持する ordinary value projection は、各 use i で

${argument}_{i}≤{B}_{i}≤{S}_{i}≤{result}_{i}.$

firstのannotationは result₀≤int、第二のargumentは unit≤B₁ を要求する。B2のsharingを加えると

$unit≤{B}_{1}={B}_{0}≤{S}_{0}≤resul{t}_{0}≤int.$

これは ground compatibility に unit と int の適合を要求する。ground compatibility がこのpairを拒否することだけで矛盾となる。**optional adaptationを推移的な具体型順序として合成する必要はない。** row flowをたどって伝播した一つの ground pair (unit,int) が検査される、という通常のSimple-sub bound semanticsである。

一方、共有anchor Cへ B_i≤C と流すだけなら、C=int|unit、B₀=S₀=result₀=int、B₁=S₁=result₁=unit は整合する。固定されたFの引数型も int|unit にできる。同じgのproviderを保持しながら別のsource descriptionを選ぶという区別が必要である。

**この節で証明したもの**は、現在の canonical merge と FreshUse の実装機構が、上記の correlation を受け取ったとき independent-use discrimination を必ず失う、という命題である。完全Yulangの元のCall・recursive-world・publicationの独立した source judgment がこの候補を合法と認めることまで、既存の未閉鎖のsource lawを使ったふりをして断定しない。従ってここでは新たなsource-level compiler-unsoundnessやOracle回帰の成立を宣言しない。

#### 5.5.4 旧Yulang2との区別

旧Yulang2の固定checkout a58eefc31e22141574b6f20c6a5748151c6d79f1 では、crates/infer/src/constraints/machine/bounds.rs:4523–4544 の extrude_pos/neg は元IDを返し、4701–4727 の extrude_type_var が元variableのlevelを下げ、lowerとupperの**両側**を再帰的にたどる。

新方式は別IDのpolar copyを作り、選んだ片側のboundsだけをコピーする。後にqualified pairをmergeすると、その訪れた親のlevelは下がる。しかし旧方式の両側closureを、新方式の片側closureと同一だとみなせない。

従ってtwo-use discriminatorが純粋Simple-subのより広い多相性を示しても、それだけで旧Yulang2の受理を失ったとは言えない。旧方式が同じBを先に低位化するなら、そちらもgをmonomorphicにする可能性がある。Oracleの実測または元のscope規則の決着なしに「Oracle compatibility違反」と書かない。

### 5.6 定理5-D：source scope を保つ extrusion消去と Generalize の修正構成

#### 5.6.1 何を変える必要があるか

型上のコピーはsourceの新しいbinderや実行上の新providerを作らない。そこで、solverのcanonical代表だけで元のsource declaration/scopeを消さず、次の情報を同じ意味的graphのnode/edgeに残す。

1. ordinary source inference declaration のidentity、sort、元のscope/telescope、現在のpublicationでのeligible/fixed区分。

1. actual extrusion occurrence、元のwhole demand、親子のsort付き対応。whole demandにはFunction四port、同じprovider、source argument、scope、effect許可やcontinuationを含む実際の全payloadを保持する。

1. 各source frameに一つのrenaming。source-owned eligible declarationだけをfreshにし、outerのmonomorphic receiver/provider/実行eventは同じものを参照する。

この構成は、runtime計算をuseごとに複製するものではない。type/evidence descriptionのsource-allowed frameだけを開く。古いfのproviderや現在のworldをgの各useで別々に選び直すことは認めない。

現コードへの差分は、canonical row のmin levelだけをsource generalizationの唯一の根拠にすることをやめ、**synthetic polar copyが元のsource declarationを誤ってfixedにしないようにする**ことである。どのsource declarationが本来eligibleかは元のsource ruleの責任であり、SCCが同じという理由で恣意的にeligibleへ変更しない。

この変更は設計案であり、既存のAuthoritative決定に実装上そのまま適合すると宣言していない。等置するpairの選択は変えず、backtrackingも追加せず、program受理範囲を狭めない方向の修正である。

#### 5.6.2 構成

元source rule programを P とする。Pは特定のsource ruleによるtyped atom、全tupleのconjunction、元binder、registered recursive referenceからなる。単一のopaque Safe(P) という述語は置かない。各atomの解釈は元から定まっているものを用い、全rowについてidentity link a≤a が真であることを要求する。それ以外の具体的adaptationの推移性は要求しない。

コピー後のprogramを D(P)、定理5-Aのparent erasureを π とする。対象occurrenceについては全retained pairをquotientし、π(D(P)) はPの同じclausesと反射的link・重複だけになるとする。**ordinary skeletonについては、この性質は定理5-Aで証明済みである。** full contextual payloadへ拡張する部分は、何を全体として輸送するかを定めて同じ構文帰納法を追加する義務であり、現実装全体に対して仮定したまま結論を宣言しない。

source publicationが独立に選んだeligible declaration集合をQ、fixed outer fieldsをRとする。use iのsource mapを ηᵢ とし、Qを同じsort・同じtranslated telescopeのfresh declarationへ写し、Rは固定する。元sourceのbinder順序を保ち、複数useのShared binderや実行上のeventは共有する。

**この区分に必要な、構成的に検査できる条件。** Qを「元sourceに由来するrow全部」としてはならない。次のcertificateをsource-owned graphから作る。

1. source constructorが導入したdeclarationごとにsort、binder、許されたfree dependencyの列を残す。written rigid、non-generic、実行上のidentityをQへ入れない。

1. 実際に共有されるouter contract、non-generic capture、Shared witness、provider/world fieldをfixed rootとし、**そのfieldの意味が自由に読む全declaration**をたどって固定する。boundsやpayloadがそのfixed descriptorの一部として解釈されるなら、その内部のfree readも含む。field内部の本来のbinderで束縛されたparameterとfree occurrenceは区別する。

1. Qは、元source introductionが一般化を許し、かつ上記のfixed-read closureに入らないdeclarationだけから作る。scope/telescopeを古い場所へ移動しない。元のsource ruleでown-componentのInternal relationとして保持するfieldと、既に固定されたEstablished contractとして読むfieldの区別も、そのowning constructorが与えるものを使う。

1. fixed row Rとlocal Qを同時に含む**関係clause**は削除しない。たとえば O≤Function(B,Ea,Er,Rv) をコピーするならOは同じouter rowのまま、Bなどのeligible operandsだけを一つのmapで写し、その全clauseを各frameの関係として追加する。Oの固定contract本体をその場で別のcontractへ差し替えることはしない。fixed descriptorがBを自由に読む場合を、都合よく単なる関係clauseだと呼び替えて3の固定を回避してはならない。

1. 親へ戻すπの一つのfiberが、元から別々のsource declarationを新たに同一化してはならない。別source declarationsが同一classに入っている場合、元source programにその等式とscopeが明記されているときだけ、その元等式を含むPを比較対象にできる。sourceにない同一化は定理5-Aのfresh-copy消去ではなく、別の保存証明が要る。

2は、列挙されたtyped record graph上の有限なfree-dependency closureであり、「全viewが保存される」という判定を隠していない。ただし、そのfree-dependency列挙が実際の全consumerの読取り（bounds・payloadを含む）を網羅することは、現実装への独立したbridge義務である。consumerが読む辺を落としたgraphのclosureでは足りない。完全な列挙を持つ構成では、ηᵢがfixedなfieldを内側から書き換えず、same-frameの全共有を保つことを構成段階で保証する。どのfieldがfixed contractか、どのclauseが各source descriptionで再形成される関係かが未確定なら、そのnative/source seamにはD2をまだ適用できない。**特に§5.5のgが元Yulangのsource ruleでこのQに入るという意味論選択は、ここでは行わない。**

本節のsource-owned πは元source declarationを固定する消去である。開始時にsourceが許した等式があるなら、それを含むPをその等式で正規化してから使う。定理5-Aのnative κがこのsource正規化に対応することは、上の条件5を満たす範囲でのみ利用する。sourceにないnative aliasをπで消しただけでsource意味が保存されたとはしない。

copy graph側のmap η̃ᵢ は、source parent a のコピーcを、そのuseの ηᵢ(a) のactual type-copy cᵢへ写す。消去 πᵢ(cᵢ)=ηᵢ(a) と定義する。copyのnumeric target levelを根拠に、そのcᵢだけを全useで同じglobal anchorへ写してはならない。親がsource上fixedであれば、この定義でも全useで固定される。

#### 5.6.3 自然性の証明

**定理5-D1：構文置換の可換性。**

${π}_{i}∘{η}_{i}={η}_{i}∘π.  (D1)$

**証明。** 元source declaration aでは両辺は ηᵢ(a)。copy cでは両辺は ηᵢ(π(c))。fixed operational identityでは両辺ともidentity。Functionでは四子について帰納仮定を使い同じconstructorを組み立てる。その他のtyped predicateも、その**引数tuple全部**へ同じ結果を代入するので一致する。binderでは元位置を保存し、bound identityを両側で同じcapture-avoiding renamingに写すので一致する。recursive referenceは同じ登録equation nodeとその同じoperand tupleを指すため、無限unfoldingを必要としない。□

**定理5-D2：商・消去後のsource-scope frameにおける任意個joint useの全関係保存。** 任意の有限use集合Iと、sourceが合法に置ける任意のjoint client formula Wを取る。Wは結果型だけでなく、複数useのpublic field、shared outer contract、同じprovider、scope内のevent/effect/continuationを相関させてよい。Wのbinder位置と共有関係は変更しない。このとき

$(⋀i∈I{π}_{i}({η}_{i}(D(P))))∧W と (⋀i∈I{η}_{i}(P))∧W  (D2)$

は、反射的linkと同じclauseの重複を除き構文上同じである。従って、rowのidentity linkを真とする、独立に定められた各local atomの解釈に対し、同じpublic assignmentと同じscoped strategyを解とする。

**証明。** 各iにD1を適用し、定理5-Aの消去結果を代入する。各frameでPと同じclausesになる。§5.6.2のfixed-read closureにより、固定fieldが自由に読むsource declarationはηᵢで変更されない。frame間でR・Shared・実行eventを同じものへ写しているため、conjunctionを取っても勝手な別worldや別providerは現れない。fixed rowとeligible rowを結ぶclauseは全体を保持しているので、cross-frameで同じouter contractにかかる複数の要求も同時に残る。Wは同じincident fieldsを参照し、両側で変更されない。binderの順番も同じなので、点ごとのassignmentだけでなく、各telescope上のstrategyがそのまま一対一に対応する。□

**D2が比較するのはπ適用後の二つのsource-scope programである。** 古いcopy scopeを維持したpre-erasure D(P) の全strategyが合法に存在し、元Pの全strategyを覆うという結論ではない。その主張にはC1・C2や追加のconstructor lawが要る。ここでは修正構成が元source frameを保持して消去・fresheningする範囲を証明しており、現在のmin-level方式の全intrusion保存に読み替えない。

D2の写像はsource/frameのidentityとretained parent mapだけで先に定まる。解・ground substitution・実行履歴を見てから都合のよい写像を選ぶことはない。これが主型・all-viewに必要なquantifier orderである。

#### 5.6.4 source typingとの合成

特定のsource fragmentについて、元source ruleからPを生成する対応が独立に証明されたなら、D2はそのfragmentの任意のlawful finite joint useを保存する。sourceが与えた同じprovider、同じargument entry、同じinvocation result/future/effect tupleをそのまま使うため、別のsource typingを探す必要はない。

この最後の合成は、source adequacyを新しく公理化するための口実ではない。実際に証明済みのruleだけに適用する。たとえばpure Value-parameter Lambda / Name / Applyのsource生成保存を独立に証明した場合、そのrule programのordinary typed部分にD2を接続できる。本書の実行小核の安全性だけでは、この生成保存を代用しない。generic handler、annotation由来のcontext、existential package、method/optional adaptation等の未証明ruleへ自動で拡張しない。

**D2が示す強い点**は、原sourceの任意の全関係を保持する変換の条件を、成功predicateや保存定理そのものではなく、構文上の同一性・同じbinder placement・同じrenamingとして構成できることである。**残る難点**は、そのsource-owned declarationとwhole clauseを現native graphに保持し、capture・replay・freshenが実際に同じmapを使うことにある。

### 5.7 現行方式へ適用する場合に閉じるもの、閉じないもの

| **項目** | **この文書での結果** | **残る実装・source義務** |
| --- | --- | --- |
| Value SCCの意味 | actual Name graphとhelper圧縮の到達可能性を証明 | 各fragmentのmembershipが承認されたsource規則と一致すること |
| ordinary extrusionの全対intrusion | 元demand/元boundsへの構文的消去を証明 | full effect/context/evidence payloadの同じ消去 |
| merge後の一般化判定 | min/orからclass-localの全称条件を証明 | native level判定とsource eligibilityの対応 |
| FreshUseでのequality | 全finite useの可換図式を証明 | sourceが許す独立性とnative共有が一致すること |
| scope下降 | 環境射影fiberでの一定性と古いscopeで合法な出力rangeへの所属を合わせた、semantic strategy因子分解の必要十分条件 | source ruleが両条件とconstructor law・表現可能性を与えるか、元scopeを保つ構成に変えること |
| 修正構成のall-view | 商・消去後のsource-scope frameで任意のjoint Wを含む全関係の同型を証明 | 元source declaration mapと全consumer輸送の実装 |
| 型安全性 | この変換で既存source proofを保存する合成方法 | complete Call、runtime simulation、recursive world、effect/handlerの本体証明 |
| 主型 | mapをmodel/history前に固定する全finite-use保存 | 各source fragmentの生成完全性と公開projection |
| 停止性 | 一回の有限コピー/有限mergeについてのみ扱った | contextual state universe、再起動/replay全体の停止 |

現在のsource theoremを閉じるには、mixed local/fixed classを「問題ない」と仮定するのではなく、元scopeの共有を示すか、§5.6のようにsource declarationに沿うframe輸送を実現する必要がある。根拠なく全local helperをmonomorphicへ限定する、旧Oracleが受理する自然なprogramを落とす、intrusionの対象pairを都合よく外す、といった回避はこの証明の結論に含めない。

### 5.8 固定コードと既存研究

- [実Value参照グラフ](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_value_graph.rs)

- [極性付きコピーの全work item](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_extrusion.rs#L20-L386)

- [親子pairの選択とmerge](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_intrusion.rs#L324-L721)

- [local判定とFreshUse](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_scheme.rs#L969-L994)

- [sourceのlevelとName生成](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/crates/yu-solver/src/candidate_source.rs#L1015-L1064)

- [旧Oracleのextrusion](https://github.com/momota1029/yulang/blob/a58eefc31e22141574b6f20c6a5748151c6d79f1/crates/infer/src/constraints/machine/bounds.rs#L4523-L4727)

- [既存のoccurrence intrusion研究](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/theory/2026-10-12-extrusion-occurrence-intrusion-proof.md)

- [既存のsource保存研究](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/theory/2026-10-13-intrusion-source-preservation-proof.md)

既存研究のpointwiseな商の議論やtwo-use判別例を参照した。今回の追加は、actual copyの消去、merge/Capture/FreshUseまで通した共有の定理、well-scopedな値域を含むscope下降条件、元frameに従うjoint-use自然性である。既存研究の未完のsource対応を完成済みと読み替えていない。

## 6 局所guardから再帰readbackのnonescapeを導く

### 6.1 証明用の依存グラフ

存在開封で得られる剛体名の有限集合を $R$ とする。各flexible変数 $a$ に、作用域から決まる許可集合 ${A}_{a}⊆R$ を対応させる。これは証明用の記号であり、constructorにlevelを追加する実装提案ではない。level $ℓ$ で開いた名前 $κ$ は、適切なlexical scope内のlevelが $ℓ$ より大きい変数だけが自由に保持できる。scopeの包含関係を同時に使うので、数値levelだけで別の枝のscopeを同一視しない。

現在の有限な型グラフに対し、変数 $a$ の保持するbounds・型payloadを構造的に読む。そこで直接自由に現れる剛体名の集合を ${D}_{a}$ とする。内部のbinderに束縛された出現は ${D}_{a}$ に入れない。$a$ のpayload中の変数 $b$ の各出現を依存辺 $e:a→b$ とする。出現に到達する途中のbinderが束縛する剛体名の集合を ${B}_{e}$ とする。全ての束縛名はα変換で区別済みとする。

このグラフはpositive/negative boundsの両方、argument/result/effectの全port、contextが保持する型payloadを含む。どのconstructorを通ったかで変数の参照が消えることはない。存在packageで名前が束縛される場合だけ、${B}_{e}$ によって自由名から除く。

### 6.2 局所的な二つの条件

全変数と全依存辺に対し、次を要求する。

${D}_{a}⊆{A}_{a}.  (G1)$

$remove({A}_{b},{B}_{e})⊆{A}_{a}  (e:a→b).  (G2)$

G1は直接の剛体比較の条件である。G2は、外側の変数のboundに内側の変数をそのまま埋め込み、後から内側の剛体名が流出する経路を防ぐ条件である。Simple-subのextrusionはこの種のscope境界を処理する位置にある。ただしG2はここで定めた局所disciplineの十分条件であり、現実装の全型形成子について既に証明済みの同値条件とは主張しない。

### 6.3 再帰型を含む自由名の定義

readbackを有限な木に展開できるとは仮定しない。自由名があるとは、その名前へ到達する有限の展開経路があることと定める。具体的に、${F}_{a}^{(0)}=⌀$ から始め、

${F}_{a}^{(m+1)}={D}_{a}∪⋃e:a→bremove({F}_{b}^{(m)},{B}_{e})$

と置く。$remove(U,B)$ は $U$ から $B$ に属する名前を除いた集合である。自由名の全体を

${F}_{a}=⋃m≥0{F}_{a}^{(m)}$

で定める。有限経路での出現という定義と、上の最小不動点は一致する。前者から後者へは経路長に関する帰納法、後者から前者へは反復段階に関する帰納法で従う。ここにはsubtypingの循環仮説のguardednessやsolver停止性の仮定を置いていない。

### 6.4 定理6-B1：局所guardによるnonescape

G1とG2が成り立つなら、全変数 $a$ について

${F}_{a}⊆{A}_{a}.$

特に公開root $o$ の許可集合に含まれない内部剛体名 $κ$ は、再帰readbackの自由名として外へ出ない。

**証明。** 全変数を同時に扱う反復段階 $m$ の帰納法を使う。$m=0$ は空集合なので成立する。全ての $b$ について ${F}_{b}^{(m)}⊆{A}_{b}$ と仮定する。直接出現 ${D}_{a}$ はG1によって ${A}_{a}$ に含まれる。辺 $e:a→b$ から来る名前は、帰納法の仮定から ${A}_{b}$ に属し、かつ ${B}_{e}$ には属さない。G2によってその名前は ${A}_{a}$ に属する。全辺の和を取っても ${F}_{a}^{(m+1)}⊆{A}_{a}$ である。最後に全 $m$ の和を取る。□

この証明は、望ましい大域不変条件を最初から仮定していない。各辺と各直接出現の局所条件から、任意に長い循環展開を含む大域不変条件を導いている。

### 6.5 系6-B2：全更新経路でguardを実行すればexit時の検査を要しない

初期グラフがG1、G2を満たし、各mutationが、直接出現、依存辺、そのbinder集合、許可集合の変更によって影響を受けるG1、G2を、公開前にすべて保つとする。このとき任意の有限回のmutation後にB1が成立する。

**証明。** mutation回数に関する帰納法でG1、G2が常に成立する。各時点にB1を適用する。最後のscope出口で初めて全readbackを走査する必要はない。□

この十分条件を実装の各操作に対応させると次になる。

| **操作** | **必要な保存条件** |
| --- | --- |
| bound追加・構造分解 | 全portの新しい直接出現と変数参照を同じguardへ送る。 |
| 反対側boundとのreplay・alias経由の比較 | 導出した比較も同じguardへ再投入する。起点が検査済みでも省略しない。 |
| extrusion | 境界外の参照をそのまま保存しない。境界に適合するcopyと、そのcopyへ移す全payloadについてG1、G2を保つ。 |
| 同一化・intrusion | 作用域の共通部分へ許可集合を狭める場合、新ownerの全既存payloadを再検証する。levelの最小値を代入するだけでは証明にならない。 |
| freshening | 一つのscope保存写像を全payloadと束縛名へ使う。外側アンカーを固定する。 |

同一化でincoming辺の参照先の許可集合が狭まり、辺のbinder集合が不変なら、その辺のG2は弱くなるので保存される。一方、新owner自身のoutgoing辺と直接出現は許可集合が狭まるため再確認が必要である。複数ownerを同時に同一化するときは、変更された全ownerについて同じ議論をする。許可集合を拡大する更新なら既存incoming辺も検査対象になり、binder集合が変わる場合も変更された辺として検査する。全体への合法なα改名は同変性により保存できる。

これは別の量化solver、constructor上のlevel、必須のexit-time checkerを要求しない。必要なのは選択済みの比較時guardが、派生比較と既存payloadのowner変更まで漏れなく届くことだ。ただし不適合な更新を拒否できるという安全性から、Oracleに適合する全てのプログラムを受理できるという完全性は従わない。extrusionの存在と意味保存は別に証明する必要がある。

### 6.6 packageとrigidityを取り違えない

exists kappa. T の内部出現はbinderが束縛するため、外へ運べるpackageに剛体名の自由な流出はない。B1はpackageの使用自体を禁止しない。開封した $κ$ を単独で外側の変数へ流すことを禁じる。

またB1はnonescapeの定理であり、抽象的な $κ$ を具体的な Int へ特殊化してはならないというrigidityの全てを証明しない。後者には、構造分解後の剛体比較を許す条件と、任意の型に対して一様であるarmの証明が別途必要である。保存する命題の違いを区別することで、level guardの局所性から型健全性全体を飛躍して結論しない。

本章の実装方針との対応は、[charter §§22–23](https://github.com/momota1029/yulang/blob/5596b1598388f629f95a44ef203e4f760b615803/notes/design/2026-09-29-scc-intrusion-redesign-charter.md#L603-L645)に固定した。局所条件を全経路で満たすことは、現実装について残る義務である。

## 7 証明の接続と実装の次の手順

### 7.1 本書で完了した証明をどう合成するか

第2章の型安全性は、型付き導出を持つ計算に対する定理である。第3〜6章は、その導出の材料となる制約・scope・名前・共有を保持する変換の定理である。必要なのは、この二群の間に、**同じソースの導出を生成し、同じ実行を説明する接続**を一つ作ることだ。

現在の全体命題を、ソース $s$、生成された制約グラフ ${C}_{s}$、公開scheme ${Σ}_{s}$、elaboration ${e}_{s}$、実行機械 ${M}_{s}$ について次のように固定する。

1. ${C}_{s}$ の合法な解から、同じ $s$ の宣言的な型付けと、対応する ${e}_{s}$ の型付き導出を構成できる。

1. solver・extrusion・intrusion・Capture・FreshUseは、公開する型、effect、同じ使用のprovider、scope、必要な証拠を保って、この解を元の導出へ戻せる。

1. ${Σ}_{s}$ の任意の許可instanceが、同じ共有アンカーを使ってその導出へ対応する。

1. ${M}_{s}$ のステップと ${e}_{s}$ のステップ・request・returnが、同じpayload、response、continuationを使って対応する。型付きの対象範囲では、未対応による Unavailable に落ちないことも、この接続に含める。

この四項目が満たされた場合、型安全性は次の短い合成で得られる。任意の公開instanceを取る。3から対応する解を得て、2で元のグラフへ戻し、1で同じソースとelaborationの型付けを得る。第2章の保存・進行・effect safetyを適用し、4の実行対応を各有限prefixに反復すれば、実機械も型に合わない値操作や許可外の外向きrequestを起こさない。

この合成論法は全体の最後の一段である。四項目そのものを未証明のまま置いて、全体定理が完成したとは扱わない。本書が実際に完成させた部分と残りは、次表のとおりである。

| **接続** | **すでに再利用できる証明** | **残る具体的な構成** |
| --- | --- | --- |
| Callのsource導出 | role付きCallの保存、actual provider/argument/bodyの同一性 | 一つのsource Applyから四portとreceiver roleを同じ導出へ結ぶ |
| effectとhandler | raw resumeを含む小核の安全性、scope transformerの合成 | FormalPermission・view・arrivalからactual classifier/Grantを構成する |
| generalization | fresh mapの全joint関係輸送、same-returned-value条件 | native Captureの全構文での境界完全性とsource一般化条件 |
| intrusion | ordinary copy消去、class共有、scope下降の条件 | sourceが許す依存と現行min-levelの共有が一致すること |
| rigid opening | 局所guardからのrecursive nonescape | 全constructor・派生比較・owner変更で局所条件を保持する実装 |
| 実行 | Call/Grant/suffix/response/eventの局所不変条件 | source型付けから全runtime stateへ対応を保ち、未対応停止を排除する |

### 7.2 最初に閉じる実装単位

最初のまとまりは、**LocalSourceのName、Lambda、Apply、厳格なlocal bindingと、そのeffectの公開まで**とする。これは最終的な言語範囲の縮小ではなく、一つの実際の経路について既存の証明を最後まで接続する順序である。Tupleやmethodを回避するsource rewriteで、元の受理要件を済ませない。

各source constructorは、同じsource occurrence、元のscope、使用した型・effect行、receiver role、公開resultと残余effectを一つの導出記録へ結ぶ。実在の ConstraintOccurrenceId、FactId、RelationId、BoundAdmissionId、BoundEmissionId の役割を保ち、source occurrenceだけをキーに異なるcontextのfiberを統合しない。

必要なのは汎用的な「証明済み」フラグではない。たとえばApplyなら、calleeの導出、whole argumentのDelay、Value/Compのentry規則、同じ四port、同じinvocationのresultという、そのCall規則の実際のpremiseを保持する。consumerはその同じpremiseを使う。既存の10月7日architectureが求めた証拠保持を、具体的なconstructorと利用先で完結させる。[P03]

### 7.3 Captureは、まず既存の正しい経路を証明へ取り込む

identity-chainとclosed zero-word filterの経路には、第3章の証明をそのまま適用する。これらをcompletion receiptが欠けるという理由だけで別の特例へ作り替えない。

次に、open tail、一般context、scope付きdemand、latent payloadを含む各場合について、公開する**jointな観測**を定める。中間座標の存在消去で足りる場合は、元の関係とshortcutの射影が同値であることを示す。中間のprovider、continuation、evidenceも観測に必要なら、その座標を消した射影だけでは足りない。

全モデルを同じ写像で運ぶ契約を選ぶ部分には、第3章のsemantic incidence方式と第4章の文脈的置換を適用できる。登録の局所不変条件、閉包の停止・列挙完全性、freshening、任意のjoint clientまでが一つの証明になる。必要なsemantic登録をoptionalな観測記録に依存させない。

後続制約については、次の二つのどちらをsource scheduleが実現するかを決める。

- 既存useが作られる前に、対応するtemplateの必要制約が確定する。その確定時点をlocal/module SCCのscheduleから証明する。

- 後から増えることを許し、第3章の差分配送の不変条件を実装する。新しいtemplate制約だけを各useへ写し、caller固有の特殊化は兄弟useへ逆流させない。

後者の定理は増分結果と**同じ更新後仕様の再計算**の一致であり、更新前と更新後で型の候補が変わらないという約束ではない。

### 7.4 intrusionを一般化と別々に変更しない

現行のmin-level/OR mergeがどのclassを固定するかは、第5章で決着した。次に証明すべき命題は、その固定が元のsourceの共有要件と一致することである。

sourceの値が古いscopeへ降りる必要がある場合、環境射影のfiber上で一定であり、しかも古いscopeでwell-scopedな値域に入ることを示す。Value SCCの同一性だけでは、この二条件は出ない。元のsource declarationに従ってframeを保持する修正構成を選ぶ場合も、固定fieldが自由に読む依存、non-generic capture、provider/worldの共有を全て保持する。

ordinary copyを元の親へ消せることは証明済みだが、scopeの違うcopy binderを無条件に消せることまでは含まない。別々のsource declarationを新たに同一化する場合も、fresh-copy消去の定理では扱えない。その等式が元のsource規則に属することを別途示す。

two-useの int / unit 障害は、共有の影響を確かめる代数的な判別例として使える。ただし旧Yulang2も元変数のlevelを下げるため、その例の候補版での失敗を直ちにOracle回帰と呼ばない。元の受理仕様またはOracleの実行結果を確定してから、必要な一般性の命題へ接続する。

### 7.5 effect・existentialを同じ型安全性へ接続する

R252のnegative open rowでは、callbackを受理することと、callbackが実際に出したeffectを処理できることを分ける。[io] のpermissionを持つreceiverがstate callbackを実行した場合、stateは残る。この導出を、sourceの四port、scope transformer、actual requestのGrant、公開残余effectの全てで同じものとして保持する。

浅いhandlerでは、選択されたhandlerをraw resumeへ再設置しない。実際のsuffixが後に起こすeffectと、resumeに渡す応答引数のeffectを保持する。第2章のhandler規則は安全な上界であり、その保守的な上界をそのまま主型規則にして正常なOracle例を拒否しない。精密なsuffix導出から狭いrowを構成し、同じ保存証明へ差し替える。

generic operationの開封では、payloadとresponseを同じfreshな剛体名のもとで型付けし、armをその名前に対して一様に検査する。第6章のnonescapeを使うには、構造分解、alias、bound replay、intrusionによるowner変更、FreshUseの全経路が同じ局所条件を保つことを確かめる。nonescapeだけでrigidityやparametricなarmの一様性を証明したことにはしない。

### 7.6 主型性と停止性の残りを混ぜない

本書は、fresh copyの合法な構文的instanceに対する一様な因子分解を証明した。これをprincipal typeへ進めるには、**独立に合法な全source/production viewが、そのinstanceとして表現される**という生成完全性が要る。現在のsolverが受理したviewだけを合法と定義する循環は使わない。元のbinder順序、任意の有限個の将来のclient、Option2の独立したproduction側の対象を保つ。[P03][P04]

停止性については、有限snapshotのCaptureとcontext合成・renameの局所的な停止は証明できる。一方、solver全体には、新規context・scope・copy・派生relationの生成と再起動がある。全体の停止には、それらの到達可能な状態の有限性またはwell-foundedな尺度が必要である。seen setの存在、配列への追記、局所loopの終了だけで全体の停止を結論しない。

### 7.7 この証明編の到達点

今回の成果は、型安全性の証明を単なる条件付きの合成論法から一段進め、実際の評価順序とraw continuationを含む小核について完結させたこと、そして現行Rustの複数の機構を、その証明へ接続できる具体的な保存命題まで整理したことである。

残っている中心は、**同じsource constructorの導出を、伝播、scope付きコピー、一般化、公開、実行まで保つこと**である。既に完成したscope代数や名前変更の補題を繰り返し増やすより、この接続をconstructor単位で最後まで通す。全体の健全性を宣言するのは、その接続を含む元の命題が完成した時点とする。
