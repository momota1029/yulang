# 有限 let 推論履歴全体の canonical model

CANONICAL-LET-HISTORY-20261024/r2。著者 `/root`。独立査読前。

本稿は [SU1–SU5](2026-10-24-signed-update-extrusion-corridor.md) の signed invariant を用い、元 f の全 descendants を一度に修復する。対象は任意有限 Let/LetRec client の**実際の元推論履歴全体**である。各公開時点で別の valuation を選ばない。実行途中から quotient した別推論履歴との対応は §8 に区別する。

## 1. 対象、モデル、履歴

[LF](2026-10-24-let-free-client-reverse-coverage.md) の元 prepublication store と [P1](2026-10-24-publication-reverse-coverage.md) の guarded regular-tree preorder を固定する。Record の node 内 label は一意。Primitive は元 object identity を使う。source client は任意の有限 Var/Lit/Lam/App/Rcd/Sel/**Let/LetRec**。f の既存再帰 store は入力であり、新しい client LetRec の signed invariant は下の CH0 で追加証明する。全 caller levels は1以上、H,C,D,T は元の level1 anchors である。

外部 context は LF と同じ、変更対象の f rows を別の入口から露出しない固定 monotype と独立 builtin schemes である。通常の client Let と f の publication boundary は1以上。builtin `if` の元 scheme は実コードでは boundary0なので、別に扱う。その元 Z-row v は empty bounds から始まり、各 lookup は v の独立 clone を返す。freshenAbove は元 v に link を加えず、client に元 v を返さない。よって v は常に empty のまま、boundary0 の lookup は H,C,D,T や f-role row へ到達しない。この例外を「全 freshening boundary は1以上」と読み替えない。他の任意の boundary0 scheme を追加する主張ではない。

履歴 h は、元 store から始まる有限の実 native inference history とする。`extrude`/`freshenAbove` の最外 call が返り、未完の copy-list assignment がない点、および同じ条件を満たす source subexpression の返却点と scheme publication/use の点を completed points と呼ぶ。再帰 child call の返却だけではこの条件を満たさない。新しい copy の list assignment が未完の途中点で production witness が既に存在するとは要求しない。whole inference の停止性を仮定・結論しない。完成した有限履歴または完成点までの有限 prefix が対象となる。

Γ_h は、全 completed points の実 stored bounds、全発行 source seeds、固定出力上界を集めた有限制約族である。bounds の出現は list entry ごとに区別する。native は完成済み row の旧 entry を消さないので、最後の全 allocated store は過去の stored clauses を保持する。ただし source seed と出力契約は明示的に Γ_h に残す。cache の存在からこれらの意味論的成立を推測しない。

元 scheme は root と boundary を保存し、参照先 row は mutable である。ここで「公開時点」はその時点の実 store を指し、後の lookup は**その lookup 時点の**両 bound lists を使う。保存時に immutable graph を capture したとは仮定しない。Γ_h はこの実際の全 freshening の結果を含む。

ρ は Γ_h の任意の一つの P1 model とする。したがって可解性は結論の前提であり、native success だけから model が存在するという未証明の完全性は使わない。固定する値を

```text
c = ρ(C),   τ = ρ(T),   δ = ρ(D)
G* = μg.Function(τ,Record(first:δ,next:g))
F* = Function(c,G*)
```

と置く。G* は一つの新しい guarded node を既存の閉じた regular values τ,δ に接続する有限 graph である。ρ(D) 等の内部 graph を破壊的に書き換えない。

## 2. recursive Let の実 constructor と clauses の由来

**CH0（新しい LetRec の signed extension）。** SU1–SU4 の store invariant S、全 completed source results の Pos 性、全 client requests の Pos≤Neg 性は、同じ domain に新しい native recursive Let を加えても、任意の有限実 inference derivation について成り立つ。

**証明。** SU1–SU3 の operation lemmas は source syntax に依存しない。SU4 の構文/event 同時帰納に、pinned `typeLetRhs(true,nme,rhs)` の分岐を一つ加える。caller level l に対し、実コードは fresh `e_ty` を l+1 に作り、ctx の nme をこの同じ SimpleType へ束縛する。e_ty は空 lists の **Z** であり、P-role へ変更しない。Z は Pos/Neg 両方の variable case に入る。

RHS は拡張 context と level l+1 で推論される。active recursive name の `instantiate` は SimpleType の実装を使い、同じ e_ty を返す。ここでは `freshenAbove` を呼ばない。syntax 上で真に shadow された名前はその新しい binding に従う。RHS 内の recursive reference も Pos result を返すため、有限 RHS derivation に構文帰納を適用できる。recursive source execution を展開する必要はない。

RHS の返却型 t は Pos。実 closing request `constrain(t,e_ty)` は Pos≤Z、従って Pos≤Neg である。SU2 はその全 replay/cache/level-mismatch events に適用され、S を保つ。実コードはこの request の返却後に e_ty を結果とし、`PolymorphicType(l,e_ty)` を作る。その root は Pos、後の uses は SU3 の両 list freshening である。RHS 内に nested LetRec があれば同じ syntax induction を適用する。self-application を特別に除外しない。finite error prefix にも signed invariant は成立するが、完成 scheme や model の存在を失敗から主張しない。よって SU4 の残りの constructor cases と合わせて全主張を得る。□

CH1 以下では、nonrecursive 部分に既存 SU4、recursive 分岐に CH0 を使う。新しい recursive placeholder とその descendants は全て Z であり、I schema を追加しない。

### 2.1 実 clauses の由来

元 o,J,R の descendants をそれぞれ o-role,J-role,R-role、元 B,Y の descendants を B-role,Y-role とする。コピーは actual parent の role を継承する。SU の P は最初の三 role、N は後の二 role、Z は全通常 client rows、外部 rows、anchors である。level や今回の publication boundary が変わっても role は変わらない。

各 entry に証明用 origin tag I/E を付ける。これは native implementation に新しい欄を要求するものではなく、有限生成導出に付ける annotation である。

* 元 f store の九種類の非空 clauses は I。
* client が発行する seed と、それを根とする実 `constrain` の全再帰 requests、およびそこから保存される entry は E。internal bound を replay しても、その実 request はこの E derivation の子である。
* f-role の extrusion parent link は I、Z-row の extrusion parent link は E。
* selected-bound copying と both-list freshening は、各元 entry の tag をその写像先 entry に継承する。

同じ payload が複数回挿入されても、それぞれの entry に由来を付けられる。identity/cache return は entry を作らない。

**CH1（由来と signed form）。** 全 completed points において、各 I entry は下表の role instance または同一 role の parent inequality である。各 E entry と各 E request は Pos≤Neg である。全 old entries を含む。

| 元 I schema | role instance の条件 |
| --- | --- |
| H≤Function(C,D) | H,C,D は同じ元 anchors |
| Function(B,Function(Y,Record(first:J,next:R)))≤o | 各文字はその role の任意の row |
| o≤Function(Record(a:Y),R) | 同上 |
| Record(a:Y)≤B | 同上 |
| B≤C | C は同じ元 anchor |
| Y≤T | T は同じ元 anchor |
| D≤J | D は同じ元 anchor |
| Function(Y,Record(first:J,next:R))≤R | 各文字はその role の任意の row |
| Record(a:T)≤C | T,C は同じ元 anchors |

「同じ role の任意の row」は、五つの occurrences が同じ freshening family に属することを要求しない。selected copying や低い row での early return が family を横切ってもこの条件は保たれる。

**証明。** 初期 store で表を直接検査する。SU2/SU4/CH0 は全 source seeds と実再帰 requests が Pos≤Neg であることを、Function の反変 branch、Record branch、lhs-variable 優先、opposite-list replay、wrong-level rewrite を含めて与える。よって `constrain` に由来する各 E entry は正しい form を持つ。I/E を単に endpoint の見た目で判定しているのではない。

SU1 により f-role の P は positive にだけ、N は negative にだけ extrude される。parent link はそれぞれ P-parent≤P-copy、N-copy≤N-parent であり、同一 role の I。Z parent link は Z≤Z なので Pos≤Neg の E。コピーする各 finite payload は constructor と leaf role を保持する。元 anchors は level1 で early return し、§1 の builtin 例外も anchor へ到達しない。従って I schema のコピーは同じ schema、E のコピーは同じ signed form である。

freshenAbove も各 row の role/color を保ち、元 anchors で停止し、両 lists をそのまま写す。I/E のそれぞれの条件が保存される。memo-before-recursion で同じ row/key に別の role を与えない。通常 allocation は空の Z-row なので追加の I schema を作らない。これで全 write constructors を尽くす。□

特に internal payload を replay した結果を、根拠なく「internal だから安全」とはしていない。実 replay は SU2 による E request であり、その derived entry は後で signed weakening によって検査する。

## 3. 完成済みコピーに残る production witnesses

**CH2。** 任意の completed point で存在する全 f-role rows について、次の実 list entries が存在する。

| role | 必ず残る entry |
| --- | --- |
| B | upper に元 C（実際には上界 list は [C]） |
| Y | upper に元 T（実際には上界 list は [T]） |
| J | lower に元 D |
| R | lower に Function(y,Record(first:j,next:r))。y,j,r は Y,J,R roles |
| o | lower に Function(b,Function(y,Record(first:j,next:r)))。b,y,j,r は B,Y,J,R roles |

これらは witness の存在であって、R の lower 内の r が R 自身という等式ではない。

**証明。** 元 store では表示した entry が存在する。既存 row の client insertion と extrusion parent-link insertion は旧 entries を消さない。新しい P-copy は positive extrusion でだけ作られ、親の lower list 全体をコピーする。そのため親 J/R/o の表示した witness は、新 copy の完成した lower list に役割を保って現れる。新しい N-copy は negative extrusion でだけ作られ、親の upper anchor をそのままコピーする。C/T は target 以下である。

freshening は両 lists をコピーするので、どの role でも表示した entry を保つ。copy 中に recursive memo hit が起きても、有限 call の返却時には miss で割り当てた全 row の list assignment が終了している。freshening は元 lists を変更せず、extrusion が途中に加える links は既存 witness を削除しない。従って完成した新 copy の witness は**その copy が返った時点**で存在する。後の client constraint を待たない。通常 allocation は f-role を作らない。有限完成 operation 列への帰納で従う。B/Y の exact singleton は SU5 と同じ write enumeration でも得られる。□

各 publication は RHS の同期返却後なので、その実 saved root の全既存 role rows に CH2 が成立する。lookup 時には、その時点の actual lists から作った全 clones に CH2 が成立する。publication のための全 latest-bound saturation や、呼ばれていない comparison の処理を要求しない。

## 4. 全 descendants に同時に成り立つ regular-tree refinement

**CH3。** ρ が Γ_h の model なら、履歴中に完成した全 role rows について

```text
ρ(B-row) ≤ c                 ρ(Y-row) ≤ τ
δ ≤ ρ(J-row)                G* ≤ ρ(R-row)
G* ≤ ⟦Function(y,Record(first:j,next:r))⟧ρ
F* ≤ ρ(o-row)
```

が同時に成立する。中央の Function は CH2 の任意の role witness を指す。

**証明。** B/Y/J の三つは CH2 の実 anchor inequality そのものである。残りを既に完成した再帰 membership の仮定から導かず、P1 の finite-depth simulation で示す。

≤₀ を全対、≤ₙ₊₁ を P1 の head 検査と depth n の child comparisons とする。Top の右最大、Primitive identity、Function contra/covariance、Record の width/depth という同じ規則である。各 ≤ₙ は反射的・推移的で、n に関する帰納で証明できる。真の P1 inequality は全 ≤ₙ に含まれ、全 n の成立は greatest simulation の成立に等しい。

一つの n について**全 R-role rows と全 K witnesses を一緒に**扱う。depth0 は自明。K=Function(y,Record(first:j,next:r)) との比較では、domain は既に得た ρ(y)≤τ、first は δ≤ρ(j)、next は一段以上小さい depth での G*≤ρ(r) を使う。Function と Record の二つの guards を越えてから next に戻るため、同じ depth の結論を使わない。これで G*≤ₙK を得る。CH2 の stored K≤R と ≤ₙ の推移性から G*≤ₙρ(R)。小さい n で Record の child 検査にまだ到達しない場合は ≤₀ が充足する。

全 n について同じ G*、同じ ρ の値を使っているので、depth ごとに異なる valuation や witness value を選んでいない。有限 family の相互参照が自己参照でなくても、同時帰納の r は常にその family 内にある。従って G*≤全 K/R を得る。

o の witness について、ρ(b)≤c と G*≤K から Function の反変/共変性により F*=Function(c,G*)≤Function(ρ(b),K)。その stored lower inequality と推移性から F*≤ρ(o)。全 inequalities は一つの ρ の下で成立する。□

## 5. 一つの canonical action と全 clauses

全 allocated rows に対して一度だけ定義する。

```text
ρ*(z) = ρ(z)                       (全 Z rows)
ρ*(b) = c                          (全 B-role rows)
ρ*(y) = τ                          (全 Y-role rows)
ρ*(j) = δ                          (全 J-role rows)
ρ*(r) = G*                         (全 R-role rows)
ρ*(o) = F*                         (全 o-role rows)
```

extrusion の polar copies、後の freshening clones、内側では low で外側では high となる rows を全て含む。元 base row だけに action を限定しない。全 client lambda-formal/App/Sel rows、これらの polar copies と freshening descendants、builtin rows は Z で、各々の旧値をそのまま保つ。

**CH4（signed action）。** 任意の Pos term p と Neg term n について、`⟦p⟧ρ*≤⟦p⟧ρ` および `⟦n⟧ρ≤⟦n⟧ρ*`。全 E clauses と source seeds が保存される。

**証明。** P-row の値は CH3 により小さく、N-row の値は大きく、Z/Primitive は同じ。Pos/Neg 相互文法への同時構造帰納で、Function domain の文法反転と preorder の反変性が一致し、result/Record は両方共変なので主張を得る。したがって任意の E clause p≤n に対し

`⟦p⟧ρ* ≤ ⟦p⟧ρ ≤ ⟦n⟧ρ ≤ ⟦n⟧ρ*`。

freshening で異なる use の Z clones が異なる旧値を持っていても、それぞれの同じ row を固定しているためこの式は同時に成立する。□

**CH5（全 I clauses）。** ρ* は全 I clauses を満たす。

**証明。** CH1 の全種類を調べる。元 ρ は Record(a:T)≤C を満たすので A(τ)≤c がある。H≤Function(C,D) と A(T)≤C は元の同じ anchor 値で成立する。J の clause は δ≤δ、R の clause は G*≤G*、o の lower は F*≤F*、B≤C と Y≤T は反射性。A(Y)≤B は A(τ)≤c。o の upper は

`Function(c,G*) ≤ Function(A(τ),G*)`

であり、A(τ)≤c と Function 反変性から従う。同一 role の親子 inequality は両端を同じ値へ送るので反射性。I の role instances は全て同じ検査になる。anchor-containing I clause を根拠なく全て反射性としたわけではない。表で全 I clauses を尽くしているので結論する。□

**CH6（finite-history joint repair）。** ρ* は Γ_h の全 stored bounds と source seeds を満たす。各 completed subexpression の Pos result は旧 result 以下であり、固定出力契約 result≤E を全て保つ。全 Z assignments は元のまま。一つの同じ ρ* の restriction が、履歴中の全 actual publication/use states の model となる。

**証明。** CH1 の partition に CH4/CH5 を適用する。source result の Pos 性は SU4/CH0。E は閉じた regular descriptor または保持する Z coordinates から作った固定 descriptor なので、その解釈は不変である。従って result*≤result≤E。App/Sel の result row は Z だから値の等式も成立する。Lambda/Record の full result は refinement を主張し、等式に強めない。

全 actual stored clauses と source seeds を含む Γ_h の model を既に構成したので、各時点の rows/clauses への restriction も model である。CH2 の witness はその時点で存在し、後着 constraint に依存しない。完成 prefix だけを独立の h とした場合も、その prefix の任意の model に同じ構成を適用できる。全履歴 h の場合には prefix ごとに別の model を選ばず、最後まで固定した c,τ,δ,G*,F* と一つの ρ* を使う。これで相反する use や異なる publication boundaries の共有 anchors が一つに保たれる。□

本定理は external Z relation を無視していない。Z-owner の lower/upper entry も全て CH1 の E または表の I に入り、同じ検査を受ける。P.upper/N.lower の元 internal correlations と全 client-added bounds も削除しない。

## 6. 等式追加の全 Z projection

Eq_h を、全 Y-role y について y=T とする有限 equality family とする。より強く、全 B-role b に b=C、全 J-role j に j=D、全 R-role 同士、全 o-role 同士の等式を加えてもよい。C と T を等置したり、別々の Z rows を等置したりはしない。

**CH7（equality projection）。** 同じ固定 output contracts の下で、全 Z coordinates 上の solution projection は

```text
π_Z Mod(Γ_h) = π_Z Mod(Γ_h ∪ Eq_h)
```

である。強い方の等式 family でも同じ。

**証明。** 右から左は制約を忘れるだけ。左の各 model ρ から CH6 の ρ* を取れば、全 Z 値は同じで Eq_h を満たす。G*,F* も explicit regular values であるから存在を別途仮定しない。□

有限式の semantic quotient として扱う場合、Eq_h の class を一つの coordinate に送り、ρ* の class-constant value を割り当てる。構造代入の帰納から全 quotient clauses が成立する。逆に quotient model は class map に沿って pull back できる。これは**同じ有限制約族に等式を加える**定理であり、quotient 後に native inference を再実行した履歴の theorem ではない。元 levels を quotient して NL invariant を満たすとは述べない。

## 7. 既存の未証明前提への適用

LP の nested Let では各 use の polar y が独立に freshen される。本定理ではそれらを全て τ にし、対応する B/J/R/o descendants も canonical values に修復する。各 use の client k/result/Z copies は旧値を保つ。旧 LP の個別 valuation を全 clients の証明として流用せず、その実 history を CH1–CH6 の一般帰納の一 instance として扱う。

SU5 で除いた later-upper の障害に加え、本稿は **全 finite original histories に対する joint stored-model repair** を閉じる。任意の source-added lower/upper、both-list freshening、全 actual snapshots を一つの action で保つ。永久 low 分類、全 f copies の旧値の等式、全最新 bounds の replay 完了を要求しない。

## 8. 実 early-intrusion 履歴への残る接続

CH7 を元 general LET-POLAR-PUB の完了と同一視しない。Y descendants の高い lower payload を level1 の T に直接集約すると、NL の leaf-level≤owner-level が破れる場合がある。実 earlier quotient はそれ以前に別の extrusion を発生させ、Z copies の生成・共有・freshening 到達を変え得る。CH6 は**元履歴の** Z rows を全て保つが、存在がまだ対応していない別履歴の Z rows に値を与えたわけではない。

この残項を解く入力は、任意 valuation の存在という形ではなく、CH6 の明示した canonical model で固定できる。必要な event transport は、(a) 実 before/after request と variable-first/cache actions、(b) 新 after Z-copy に割り当てるこの model 内の値または構成値、(c) 全 selected-bound inequalities と shared-low の一貫性、(d) 全 actual freshening snapshots の root/出力対応、を同時に与える必要がある。[EC1/EC2](2026-10-24-signed-update-extrusion-corridor.md) は uninterrupted extrusion と固定 snapshot の場合にこの値の取り方を既に与える。interposed writes と altered reachability について無条件にその map が存在するとはしない。

source receiving/SCC 資格、元全 source の effects/provider/owner 対応、独立 result target checking、original A/B の全量化、principality、combined termination はそれぞれ元の親として残る。本稿の domain へ親定理を縮小しない。

## 9. CH8: Y.lower の低い boundary factor とその複写

本節では h の各 top-level `constrain` call が正常に返った完成点を使う。途中で失敗した call の insertion から、残りの replay が実行済みとは言わない。一般停止性は引き続き主張しない。

**定義（低い正方向 factor）。** finite term L の low factor は、同じ Function/Record/Primitive skeleton を持つ level≤1 の項 Q と、その leaf comparisons、および保存された Q≤T からなる。ただし L が variable の場合は Q=T を許す。net-positive の variable leaf a と対応する low leaf b に対して a≤b、net-negative では b≤a が実 bound entry として保存されている。leaf を変更しない場合は反射性でよい。Q=T のとき最後の Q≤T も反射性でよい。この有限証拠から、構造帰納と Function の反変性により L≤Q≤T が従う。

**CH8。** 上記の正常返却 history の任意の完成点で、各実 Y-role row y の lower entry L には低い正方向 factor が存在する。各 actual freshening がその entry をコピーした場合、写された L' にも**同じ Q**を使う factor が存在する。全 finite uses で Q の全 leaf とその値は共有される。これは各 copied pair(L',T) が新しく実行されたという主張ではない。

**証明。** entry の実 origin で帰納する。元 Y.lower は空である。CH1 の分類から、Y.lower を新規に増やす constructor は (a) negative extrusion の同-role parent link、(b) `constrain` の rhs-variable insertion、(c) freshening の lower-list copy だけである。negative extrusion が新 Y-copy に設定するのは upper list であり、選択 lower copy を紛れ込ませない。

(a) entry は別の Y-role row y' である。CH2/SU5 により y'.upper に同じ T がある。Q=T、正 leaf inequality y'≤T を取る。

(b) cache miss した実 `constrain(L,y)` が rhs-variable branch で L を挿入した場合、SU5 の y.upper=[T] を同じ stack で走査し、実 `constrain(L,T)` を呼ぶ。lhs-variable 優先が成立した場合は y.lower に新 entry を作らないので、この case に含めない。正常に戻る top-level call 内で、この boundary request の証拠を次の通り取る。

* L が variable なら、L.level≥1=T.level なので、L=T の identity return または lhs-variable branch で保存する L.upper の T を使い、Q=T とする。反対 list をも挿入したとはしない。
* L が structural または Primitive で level≤1 なら、rhs-variable branch が T.lower に L を保存する。Q=L、leaf comparisons は反射性。
* L が structural で level>1 なら、実 positive `extrude(L,1)` が Q を返す。各 wrong-level variable leaf a に対し、net-positive では parent.upper に copy b、net-negative では parent.lower に copy b を保存するので、上で要求した各 leaf inequality がある。返却 Q は level≤1。同じ call の rewritten request `constrain(Q,T)` は rhs-variable branch で Q を T.lower に保存する。Q は Function/Record root のままなので lhs-variable branch に変わらない。

boundary pair の cache hit は、その cache への最初の miss を参照する。実 cache は top-level constrain call ごとに作られ、whole call が正常に返った時点ではその first-miss frame も正常に返っている。その first miss は上の同じ L,T に対するいずれかの case であり、そこで保存した entries を使う。level が可変だとは仮定しない。fresh positive extrusion の rewritten Q は新 copy identities を含み、同じ call のその生成以前の cache entry ではない。低い structural case/variable case では直接の保存 entry がある。cache hit を最新 bounds の再処理に置き換える必要はない。

(c) y.lower の L を actual `freshenAbove(b,root)` が L' へコピーしたとする。y が freshen される通常 boundary は b≥1。Y-role が builtin if の boundary0 lookup から reachable でないことは §1 で示した。既存 factor Q の全 rows は level≤1≤b なので、Q と Q≤T の保存 clause は変わらない。

L の leaf a が boundary 以下ならそのまま、boundary より高ければ、実 both-list freshening は a を clone a' にし、その全 upper/lower entries をコピーする。factor の entry a≤b_low または b_low≤a はそれぞれ a'≤b_low、b_low≤a' になる。b_low は level≤1 なので共有される。L から a は直接 reachable であるため、その clone と list entry は実 traversal に存在する。ここで別の freshening memo を後付けしていない。variable L の Q=T も同じ議論である。全 skeleton と polarity は保たれるので L' の factor を得る。

既存 entry への後着 writes は factor の保存 entries を削除しない。従って全 origins と有限 history を尽くす。複数 use でも各々の高い a' に対する bound は別にコピーされ、Q の低い rows だけが同じものとして残る。これで同じ Q の共有が示される。□

CH8 は、単なる transitive path L≤y≤T より具体的な、実低 boundary と各 leaf の保存証拠を与える。特に Y.lower からしか見えない高い payload が publication でコピーされても、その T-boundary factor が失われない。旧 §7 の variable-first/cache 留保は、任意の L.upper に保存された y や、任意の未処理 path に対しては依然として必要である。

CH8 だけでは、新 after extrusion が読む**全 selected bounds**の factor を同じ polar memo で選ぶところまで示していない。新しい payload を跨いだ repeated keys、異なる demands の共有、別履歴の全 Z copies を、CH6 の model と EC1/EC2 に整合させる合成が残る。input term の leaf inequalities を全 copy-list obligations の証明へ置換しない。

## 10. Freeze / handoff

契約 [CANONICAL-LET-HISTORY](../../tasks/agent-loop/sprints/canonical-let-history-20261024.md)、r3、SHA-256 `8b43b5d0ef521daf765ebad86bf0d8ff90a0015cd1aefb40a211440647f7a73f`。Primary 単著。直接根拠は pinned Typer.scala の constrain/extrude/freshenAbove/typeLetRhs と、固定済み SU/P1/LF/NL。コード・tests・probe は変更／実行していない。査読対象は CH0 の recursive placeholder と closing request、CH1 の全 entry origins、CH2 の completion 時の witness、CH3 の同時 depth 帰納、CH4–CH6 の全 clauses と時点、CH7 の equality fiber、§8 の actual-history 境界である。


## 11. 初回独立査読と差分

初回査読対象 SHA-256 `79fd826da939ad73b76711f2928a56e6cb2aeade1161a9c53bde100a8a54a97d` の CH0–CH7 は `/root/astra_semantics_review`110sec の独立査読で受理された。BLOCKING/MAJOR なし。MINOR 指摘に従い、completed copy-operation points を「最外 call の返却かつ未完 list assignment なし」と明確化した。source publication/use は元からこの条件を満たす。追加 CH8 とこの差分は別途独立査読待ちである。


## 12. 最終差分査読

`/root/astra_semantics_review`100sec の独立差分査読は、CH8 の正常返却履歴での全 Y.lower origins、first-miss/cache、同じ低い Q を保つ実 freshening、および先の MINOR 修正を受理した。BLOCKING/MAJOR なし。査読対象 SHA-256 `d2fe0701f4f9d5ca5070fe56b28e93fe82c04742dee635fe625e054b7c076745`。本節追記以外の本文は同じ。CH0–CH7 の初回受理と合わせ、記載した範囲の共同モデル・等式 projection・boundary factor が確立した。全 selected bounds/memo と別 early-intrusion 履歴への合成は未完。[固定版と査読範囲](../../tasks/agent-loop/sprints/canonical-let-history-20261024-outcome.md)に記録する。
