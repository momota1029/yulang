# 生成された source core から有限観測 interface を構成する

Assignment: **CORE-INTERFACE-VALUE-20261024/r1**。著者 `/root/astra_corrected_machine`、子・共同執筆者なし。分類は未査読の構成的候補証明。要求 Astra/medium、観測 model/effort/active duration は UNKNOWN。基準は primary 指定の `59057b660a5a46f448d4c6feda041cb3df3bb38f`。

契約 `tasks/agent-loop/sprints/core-interface-value-20261024.md` の SHA-256 は `25a86d63132654cfa1ef32074ac54f66f5be1f0ead5e0cdd4b0ec9d379056477`。本稿だけが書込み lease であり、旧証明・primary の値保存稿は変更しない。

## 1. 親命題と今回除く前提

親は source action coverage 稿の G5、すなわち有限導出から生成した `Gen(d)` の TABLE が修正候補 core の全有限実行 prefix の `Alpha*` を含むという命題である。G5 の「適切な有限 interface」を、以下の機械的な構成 `Interface(d)` に置き換える。入力は G1 が実際に生成する有限の命令・宣言・template graph であり、実行の到達集合、健全性判定、完成済みの有限抽象状態集合を入力にしない。

結論はその具体的候補 core に関する片方向 inclusion である。任意の source から承認済みの意味に一致する recipe/code が生成されること、自然な小さい annotation が受理されること、推論停止性・主型性・元の A/B はこの結論ではない。特に R の共起 recipe 定理の有限 signed graph という前提を、非正則な全型の有限性へ拡張しない。後述の §8 で、観測 interface の有限性と recipe の正しさを別々に親へ戻す。

## 2. 凍結入力

すべて現 bytes の SHA-256 を契約と照合し一致した。

| 略号 / input | SHA-256 |
|---|---|
| G: `notes/theory/2026-10-24-source-core-action-coverage.md` | `36672ef591f42a281a04f14fb7ddc4c5283c119de20fee15168e37cbbf13201a` |
| CM: `notes/theory/2026-10-24-corrected-machine-simulation.md` | `fffb4f1540739020a0702d4f7b07d41cd9b68a9063f36d24292914b84e6b606d` |
| H: `notes/theory/2026-10-24-correlated-handler-observation.md` | `fd3a901a738f24b18d8c21acdb2dc451fe192da0b54a4aa5b674c3aaea8789f0` |
| R: `notes/theory/2026-10-24-cooccurrence-source-recipes.md` | `ee99b45dbc49c3563220335b350814ed422bf0fbe7edfcb4cfaef476da986cdb` |
| O: `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| S: `docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| D: `docs/yulang-dot-selection-safety-ja.tex` | `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b` |
| `notes/design/2026-10-24-cooccurrence-release-clarification.md` | `c9eb9b8d274172f02bc82088896c30dd92e219a02adf6ba22418b2cc34207d12` |

G の r1 は本 worker、G の failure abstraction・result-boundary repair は primary。CM の Extend/Fork/Rejoin 修正も primary。各独立査読 receipt の範囲だけを利用する。H は `/root/astra_scoped_join`、R は primary、原稿は各凍結入力の帰属を保持する。

直接の source 根拠は O:1194–1215 の有限宣言 template/型引数環境、O:1294–1342 の cell、O:1546–1576 の共同 formal seed と全 latent inclusion、O:1631–1678 の frame grammar、S:1690–1705 の有限語 path interpreter、S:1943–1958 の unknown correlation、D:153–221 の eapp、G §§3–7 の全命令/失敗 channel である。

## 3. Interface を作る有限走査

### 3.1 位置と register

`Lab(d)` を G1 が登録した命令・body・phase・arm index の有限集合とする。各位置 l で次を構文から列挙する。

1. その命令の operand、結果、型引数 environment、dictionary/direct evidence、closure environment の参照 slot。環境を再帰展開せず、一つの closure body の自由 binder はその有限な構文上の集合だけを slot にする。
2. 正常/発行 event/latent 使用/reentry の port **schema**。schema は code label と usage kind と静的に指定された component/template 位置である。runtime の全 path を列挙しない。一般の潜在位置には「現在この使用で選択された path」を格納する opaque cursor slot を一つ設ける。
3. 当該 frame の保存 operands、戻り先 label、mode、pending q,p,K。wait の新しい attempt event と元 pending event は異なる slot。再帰的な K 全体は一つの opaque continuation descriptor 参照であり、その全 frame を現在の interface へ展開しない。
4. 現在 action が読む owner/control/handler/view/event/family/resource/scope/target/receipt/型・operation instance の有限個の name slot。origin lookup が必要ならその戻り値を別の slot にする。evidence owner と control owner は役割 tag が異なるが、同じ owner-name sort 内で実 equality を比較できる。

各 slot の値は無限集合を走ってよい。有限なのは slot の数である。kind 色は有限の既知宣言・constructor/site と OTHER を区別するだけであり、OTHER 同士または同色同士を同じ動的 identity としない。

命令の出力を次の命令へ接続する edge e には、入力側と出力側の slot のタグ付き union `U_e` を作る。return/resume/No には保存 immutable 側、現在 world/operand 側、接続後側の三つの有限 interface の union を作る。同じ名前を意味することが構文的代入で指定された slot だけに equality equation を課す。三側の hidden witness が互いに素だとは仮定しない。

これは一回の有限 edge 走査で終わる。次々に union を作って世界全体の register を永久に増やす操作ではない。edge の出口で次の位置の interface へ射影する。必要な過去情報は frame が保存する有限 immutable projection として扱い、未知になった関係は再露出時の全候補に戻す。

### 3.2 命令から得る query 欄

命令 template の式を走査して以下の有限欄を生成する。反復変数の具体要素数だけ欄を増やしてはならない。

| template | finite observations |
|---|---|
| constructor/primitive/match | 指定された tag/arity/field presence、比較結果、Yes/No/failure tag、選んだ component の親対応 |
| call/entry/eapp | entry kind、receipt site、現在 control と evidence receiver の equality、source profile kind、型/dictionary instance の比較、実使用 port |
| search/attempt | Base、GC、GW、各 query candidate の witness D/P0/A/F/Z、operation identity と paired instance の一致 |
| release/target | named L(s,t)、Match(t,s)、From、actual inventory membership、scope の元 receiver、各 route の H membership、current Z |
| scope/View | own/borrow、activity、executing View membership、保存外側 ambient と今回の内側 contribution、route transport |
| wait/resume/read | 元 pending packet の immutable columns、current query columns、共有 identity equality、次 candidate の比較結果 |
| mapop | 同じ w の payload/response instance pairing、元 event identity、adapter body の入出力 usage |

scope/target 候補を任意個走査する R-Cross では、`selected(s)` と「その witness に新たに対応する解除対がある」という CM の discriminator を **row の述語欄**として一つずつ持つ。対象要素ごとに name register を作らない。From/Match の連言は同じ実 tuple に対する欄であり、別行の marginal を合成しない。

全 predicate は具体機械が既に読む有限 query の結果、またはその定義式の部分式である。`この状態が安全`、`将来 effect が起こらない`、`source 到達可能` のような述語は欄に加えない。保護解除の承認済み動作原理を新しい「同じ表示変数なら同じ scope」という判定に置き換えない。

### 3.3 cell の具体的な有限集合

各 interface I に、defined bits、同 sort register の equality partition、有限 scalar tags、named binary L/Match の欄を置く。現在比較するすべての packet port/candidate slot の欄を **一つの** witness vector に入れる。vector は scope/receiver equality、P0、A、D、F、Z、packet membership、named-target H membership、必要な上記 discriminator を含む。named witness は個別 row、その他は完全 vector β ごとの occupancy `e_β` 一つで表す。owner population についても現在必要な unary diagram を別に持つ。

欄数を b、name slot 数を n、有限 tag の組合せ数を k とすれば、粗い上界として `k · 2^n · Bell(n) · 2^(O(n²)+b n+2^b)` 個以下の syntactic cell で足りる。正確な個数は不要であり、明示された有限 Boolean/equality 制約だけで列挙する。実現不能 cell を除く oracle は使わない。Fail channel は G4 の有限な failure reason cell であり world 欄を持たない。

**定義 I1。** `α_I(x)` は実状態の上述の述語を評価した cell。latent cursor を持つ schema では、現在の具体使用 path を slot に与えて評価する。未知の将来使用を表す formal input では、全 concrete cursor/instance assignments の像を含む全 syntactic input cell を seed にする。未来 event を発生させる seed ではなく、使用時に接続する latent/reentry input の集合である。

## 4. 非正則な型と無限に多い instance

### 4.1 有限個の slot と無限に大きい slot 値

型を `template-node × type-argument-environment` の具体 descriptor として扱う。型引数環境は深く、大きく、実行ごとに異なってよい。cell はその全内容を保存せず、現在命令が実際に比較する instance の equality と、現在選択された structural query の結果だけを持つ。従って polymorphic recursion の `T<A>`, `T<F<A>>`, `T<F<F<A>>>`, … を code label や cell 色へ列挙しない。

`EqInst(i,j)` は具体機械の同じ resolved family/型引数 instance の等号である。有限色の一致とは異なる。明記された同時代入は必要な equality を保ち、別の利用時の比較は新しい EqInst 欄を作る。同じ入力を型・family・payload・response に使う pairing は一つの union interface の式として保持する。型の不一致を Boolean の不確定さによって実行時に許可する規則ではない。具体値の型安全性は独立の値定理であり、抽象側に余分な cell があることはその型規則を変更しない。

### 4.2 実 structural query の有限解釈

型の inspection をすべて「不明」と呼んで停止性を仮定するのではなく、O/S が定める query の種類を分ける。

- **静的 constructor operation**: split、field、switch、Function の四ポート、eapp の formal は現在の命令の有限 constructor/label を一つ検査する。variable-sized record/list は現在の field/index とその成功/不成功・選択された component だけを返す。未知の全 field を静的列挙しない。
- **typed path query**: 入力は既に存在する有限語 p と `(node,θ)`。次の child label を消費し、現在 node の宣言 template の該当子へ進み、その一段の型引数代入を行う。nominal representation を開くときも S:1699–1704 のとおり constructor label を消費する。型変数は現在の具体 environment を参照し、同じ有限語をその descriptor で解釈する。無進展 alias cycle は宣言形成が除く。従って、消費語長と有限な alias 解決の組による帰納で停止する。無限個の θ の集合を先に計算しない。
- **actual route query**: 有限 prefix の immutable occurrence DAG を後ろへ辿り、上の path interpreter で各 finite route の照合を行う。実行前の潜在経路・将来 read を辺として追加しない。DAG と実 route の有限性から全探索は有限。
- **Match/From/Z**: 現 target の実 B_t と actual witness の Origin/H、現在 L を同じ tuple で照合する。各有限 prefix の有限表・有限 route の query なので、上記の手順を有限回使う。Z は binary L の existential を正確に具体評価するが、その結果の一 bit を有限表示する。

この手順は一般の型等価判定器や任意の無限 path-language equality 判定器を構成していない。既に具体候補が定義している operation-instance equality を cell に観測することと、その判定を別の意味へ置換することを区別する。非正則な全 `I⁺(a)=I⁺(b)` を R の有限 graph 算法で判定できるという結論は出ない。

**補題 I2（structural observation の有限性）。** 固定した生成 template に現れる上記 query 群は有限個の schema と欄で表され、任意の具体有限 path/型引数環境についてその実結果を持つ cell が存在する。

**証明。** query schema の数は template 構文の有限性による。具体値の大きさでは増えない。各実 query は前記の有限解釈で結果を返し、それを各欄へ代入すれば α が得られる。alias/equality と共同 tuple の式は実同一性から満たされる。型の nesting が深くても増えるのは具体 query の作業量であり欄数ではない。□

### 4.3 潜在 port と上界の区別

動的に深い結果型の全 latent port を、固定深さまで切り捨てない。opaque cursor による一つの usage schema は、任意の実有限 path の使用を量化する。新しい使用ではその concrete path と現在 instance に応じた欄を Expose/Refresh する。同じ色の path が同じ結果を持つとは主張しない。失った相関は全候補となるので、その schema の TABLE は異なる path の挙動を混ぜて過大になりうる。

本稿が直接証明するのは実 successor の包含である。個々の Φ/annotation が path ごとに要求する上界については、その **同じ** cursor/instance の contract interpretation に対する mandatory inclusion を使わなければならない。cursor を忘れた後の最も寛容な別 path の許可を使ってはならない。必要なら現在の `Allowed_Φ(event,cursor,instance)` の実 query 欄を追加し、未知なら両候補を残し、出力 cell 全てで true を要求する保守的検査は有限である。ただしこれは既存 certificate の精度・構成可能性の証明ではない。Φ の解釈自体を任意に選ぶ規則は加えない。

## 5. Interface adapter と局所包含

edge `I→J` は有限 union interface U で次の順序に構成する。

1. input の完全 row/partition を U に持ち上げる。新しい欄は CM Refine、必要な旧名の露出は Expose。新たな name と単なる露出を区別する。
2. concrete instruction が保証する式だけを課す。保存 operand の alias/代入、実 receipt introduction、fresh scope/target、current named L の更新、paired payload/response の instance、constructor alternative を含む。
3. 旧 row の純粋な写像は Map、新しい protection/event は Extend、新しい view/route は Fork。旧 route を新 route へ置換しない。動的に何個 row が追加されても、占有する有限 vector 集合を列挙する。
4. 新しい型引数環境、candidate、path、world に依存する欄は、式を証明できる場合だけ更新し、残りは Refresh。未知の column を0や都合のよい grant に固定しない。
5. J へ Forget する。保存が必要な frame は先にその Imm projection を取る。future return ではその projection と **現在** world を Rejoin してから同じ手順を行う。

**補題 I3（adapter の構成と包含）。** 全 generated edge の adapter は有限に列挙でき、その edge の任意の具体 step `x→y` について `α_J(y)∈R_e[{α_I(x)}]`。保存 frame の復帰では入力を `(Imm(saved),α(current))` の joint tuple とする。

**証明。** I/J/U は §3 の有限構成。未知欄の選択では実 y の各値を選ぶ。hidden region を分けるときは実部分領域の occupied subset、Extend では実新 row の vector 集合、Fork では実 parent row と実 child row を選ぶ。これらが列挙内にあることは CM 2/2a/2b。新旧 route の H の違いも同じ union diagram にある。current restoration は CM 2c により実 joint tuple が Rejoin にある。I2 は非正則な path/instance についても必要な実欄値が定義されることを保証する。コピーした equation は concrete instruction の同じ式なので破れない。最後の Forget は実出力の射影である。したがって実 successor が残る。□

**補題 I4（query 欄の充足）。** generated search の実 α では H の `P,PF,Base,GC,GW` と `e=Base∧(¬P∨GC∨(GW∧¬PF))` が現在の具体 query に等しい。

**証明。** D/P0/A/F/Z と membership を同じ witness vector に入れたので、H1 の named singleton/hidden-region 分割をそのまま適用できる。未知 instance equality を色で代用していない。真偽両 filter はその実 cell を正しい側に残す。抽象集合全体には両真偽があってよい。□

## 6. 七 frame と有限 summary domain

各 frame は下表の有限保存 slot を持ち、内部の任意長の stack は grammar word として残す。

| frame | 保存する有限 schema / 復帰の接続 |
|---|---|
| bind | suffix label、自由 operand 環境参照、child result formal。current result を suffix に代入。 |
| scope | 旧 evidence owner、control slot、own/borrow、前 slot。復帰時に current control を処理。 |
| View | immutable packet/port cursor、saved outer ambient contribution。現在内側/外側の witness を共同に表示し、集合差で除去しない。 |
| handle | source descriptor、現在 activation/owner slot、arm index。selected K には追加せず、forwarded H_hK に追加。 |
| mapop | w と paired instance、payload/response adapter labels。response を同じ pair で接続。 |
| wait | Imm(q,p,K)、残り arm index、attempt child location。元 q と新 q' を別 slot にし、No は現在 world と Rejoin。 |
| release | immutable target/recipe reference、現在実 scope/From/Match query の row schema。Ret/Req/Fail を分離。 |

レシピ表・closure environment・K は runtime に無限種類ありうるが、現在 frame の operand として一つの参照 slot を占める。必要な一行/一変数の read をした時に、その結果を有限 query schema へ露出する。stack 全体を同時に正確な有限 diagram へ圧縮する主張ではない。

有限個の local/frame/adapter interface の cell universe の直和を B とし、failure cells も含める。`D=P(B)` または port を保つ有限積 lattice を取る。frame 関数は `Mon(D,D)`、grammar 非終端添字は code/template label と static hole/result scheme slot と mode である。具体的な instantiated type は添字にしない。同じ template の異なる instance は引数 environment slot と instance-observation 欄の入力が異なる関数適用として表す。

接続で concrete 型が一致することは独立の型導出が保証する。抽象 grammar は型一致を証明できない組を残してもよいが、色の一致から concrete 型一致を結論してはならない。この余分な grammar production は精度を悪化させうるだけで、実 word を落とさない。

**補題 I5（任意長の capture/resume に対する有限 domain）。** 全七 frame の local transfer と interface adapter が有限単調関数になり、実際の任意の有限 frame word と現在の適合 input は有限 code/cut 閉包に含まれる。

**証明。** relation image、cell 固定 filter、有限 union、Forget/Rejoin は入力集合に単調。I3 が各実 frame の interface 接続を与える。grammar word の長さ0は response hole の input cell。帰納 step では最外の実 frame の有限関数を適用し、その実現在 world/保存 Imm の joint 入力を選ぶ。I3 によって実 successor が関数像に含まれる。frame の保存データは帰納の各 step の局所 tuple であり、すべての pending data を一枚の固定 cell に同時展開しない。有限 `Mon(D,D)` の合成と union による同時閉包がこの有限合成を含むことは CM §6 の lattice 帰納で従う。再帰が frame 列を長くしても同じ有限 grammar production が繰り返されるだけである。□

## 7. 多相使用・外部応答・再開による反証の検査

同じ polymorphic body を二つの instance θ1,θ2 で呼んだとする。body label は同じだが、同時に存在する operand slots の EqInst は実比較に従う。θ1≠θ2 を「同じ template 色だから等しい」とする equation は生成しない。input graph で関連が失われた場合、両 equality alternative を列挙するので、少なくとも実 alternative は残る。

外部 response が内部型として今まで現れなかった深い descriptor または新しい nominal/family identity を持つ場合、既知の有限色以外は OTHER になる。しかし旧名との equality、実 operation response instance との一致、現在 path query は独立欄である。有限 opaque slots により α は存在する。これは response が型に合うことの証明ではなく、元の typed external protocol が与えた response の **表示**である。不正な host response をこの overapproximation で正当化しない。外部 code が実行される場合には、その introduction/reentry 契約が別に必要である。

pending q が保存された後、別 instance の callback が effect を出し L を変え、再開後に No となる場合、保存 q の instance/Origin/H は Imm に残る。callback の current L/owner は current 側、次 candidate の instance 比較は Prep の新しい欄である。I3 の Rejoin はこの三者の実 joint tuple を含む。保存時 Z や旧 candidate の EqInst をコピーしないため、callback による深い型 instance や新しい target が旧有限欄数を増やす必要はない。

この議論が保証するのは実 successor の存在であって、同じ抽象 cell の全 concrete 実現で query が同じ将来値になることではない。binary scope-target の完全な未来相関を unary quotient が回復するという CM で棄却された主張は再利用しない。

## 8. G5 への適用と正確な残項

**定理 I6（生成 core に対する有限 interface 前提の構成）。** G1 が有限の syntactic code/template graph `Gen(d)` を構成する任意の入力 d について、§3–6 の `Interface(d)` は有限に構成できる。この interface で generated metadata relations と both-filter/current-world connections を具体化すると、G5 の有限-interface/現在-query/pending-data 表示前提は I1–I5 から従う。任意の非正則な runtime type instantiation を個別の static graph node として列挙する前提は不要である。

**証明。** G1 の有限 label/edge 集合を §3 の走査に入力すれば有限 slots/columns/union interfaces を得る。I2 が各 runtime structural query の解釈を与え、I1 が全現在 cell と formal seed の存在を与える。I3/I4 が全 local edge と query の representation、I5 が capture/resume の接続を与える。G4 の failure channel は有限 failure reason のみであり追加 world interface を要求しない。これで G5 が独立に仮定していた interface 条件の各成分を構成したので、G5 の prefix 帰納を適用できる。Bad 排除・値保存および foreign introduction 契約は元の別前提のままである。□

この適用は、既存の小 certificate をそのまま認証しない。Interface(d) の Refresh や OTHER のため TABLE が大きくなった場合には mandatory inclusion を改めて満たす必要がある。有限の安全な overapproximation があることから、ordinary inference の受理能力や主型を縮小してよいとは導かない。

**残る生成境界を明記する。** G1 は recipe を R の有限 signed signature graph から生成する箇所を持つ。R §§1,5,7 は非正則な全 instance、任意型代入、compaction/recursive center の correspondence を明示的に未解決としている。本稿の path interpreter は **既に存在する recipe の有限語 membership**を扱うもので、任意非正則 instance に対する共変位置集合の equality や、その商 recipe 自体の生成を証明していない。したがって I6 を「全 original source について Gen(d) と正しい recipe を構成した」と読み替えてはならない。元の親 domain は狭めず、この生成・対応義務を別の owner にそのまま残す。

| TODO / owner | 必要な最初の証拠と exact falsifier |
|---|---|
| INTERFACE-REVIEW / primary が指定する独立 reviewer | finite slot/row schema と全 edge adapter、特に動的 latent cursor と seven-frame joint input の包含を査読。実 action がこれらのどの欄/Refine にも入らない例が反証。 |
| RECIPE-ALL-SUBSTITUTION / source recipe・co-occurrence owner | R の有限 graph 前提を満たさない非正則型/任意代入における正しい元成分 recipe の構成と承認済み原理との対応。有限語 membership の停止だけでは解けない。別 receipt の origin が Match に混ざる生成例が反証。 |
| VALUE-FOREIGN / primary 値保存 lane | 具体 instance に一致する typed response、internal closure/continuation の導入契約。Interface の OTHER/equality で型不一致を正当化した case が反証。 |
| SMALL-CERTIFICATE / annotation・inference owner | 各所定 Φ の同一 cursor/instance inclusion と ordinary source の精度。別 path の許可を流用する出力 cell が反証。 |
| SOURCE-NATIVE / 実 constructor owners | 実 compiler がこの candidate Gen/interface を生成する対応。本稿は symbol inspection/実装を行っていない。 |

## 9. 資源と停止

三段階を使用した: interface の構文走査、nonregular query と adapter/frame 帰納、G5 への適用と recipe 境界の切り分け。上限190秒・三段階。観測時間 UNKNOWN、未観測予算の返却なし。検査は pinned bytes の hash と source 式の読解、有限集合/構文/word/prefix に関する紙上証明のみ。tests/build/probe/network/Git/実装変更なし。

新規・scratch path は本稿 `notes/theory/2026-10-24-source-core-finite-interface.md` 一つのみ。既存 CM/G/H、central state、primary の値保存稿を変更していない。元の generation/accumulation/propagation/levels/extrusion/qualifying intrusion/generalization、residual/provider/witness の独立量化を維持する。

r1 は最終 hash receipt で凍結し書込み停止。子なし、未解決 descendant lease なし。この worker の停止は全体目標の完了ではない。次は primary の独立査読と、残る recipe/値・foreign/source-policy 義務への適用である。
