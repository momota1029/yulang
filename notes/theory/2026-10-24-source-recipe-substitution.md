# 任意型代入から経路 provenance と入力 recipe を構成する

Assignment: SOURCE-SUBSTITUTION-SURFACE-20261024/r1。
Author: `/root/astra_cooccurrence_proof`。共同著者・子なし。
Status: 未査読の enriched-source 構成的定理。既存 compiler の消去済み表からの復元定理でも、全言語の閉包でもない。
Contract SHA-256: `08ca430426512015db0c825dca0728be269ad59b79a818fd4a27e51bb0898d12`。
Baseline: `59057b660a5a46f448d4c6feda041cb3df3bb38f`。
Requested model/effort: Astra/medium。Observed model/effort/duration: UNKNOWN。

## 1. 親、入力、今回の結論

親は元の source 領域の全有限型導出と全有限実行 prefix に対する値・効果・衛生性の健全性である。全称除去、非正則な型 instance、繰返し再開、外部 continuation の独立した条件を削らない。直接の対象は R=`cooccurrence-source-recipes` の S5 が単射改名だけを扱っていた任意型代入の不足である。

入力は名前解決済みの有限な型導出 d、有限宣言/template 表 Δ、well-formed な capture-avoiding 同時型代入 σ である。σ の右辺は有限型構文または既登録 template と型引数環境であり、全 ground instance の有限列挙を要求しない。S の形成条件に従い、child label を消費しない alias cycle はない。正則性を仮定しない。source の formal/component root K は d の有限構文から列挙する。

出力は代入後の型導出、構成時 provenance を持つ有限 descriptor、任意の具体有限 path の signed occurrence を列挙する interpreter、およびその interpreter を参照する入力 recipe schema である。完成済みの正しい origin 表や安全な実行集合を入力にしない。さらに全称除去/template-use の両翻訳順序が同じ provenance trace を生成することを示す。

結論を分ける。任意有限 path の対応と元成分別 recipe の生成は構成的に得る。全ての非正則 instance の occurrence-language equality の決定算法、およびその等価 class を全て生成する算法は得ない。従って RECIPE-ALL-SUBSTITUTION の provenance/path 部分を本稿で具体化するが、無制限の商生成と native compaction の対応は残る。

## 2. 元座標を構文から付ける

### 2.1 型の意味と由来の sort を分ける

型変数の静的 identity β は binder identity である。由来座標 o は `(導出/template label, formal/root key, 元 binder identity, 元の構文 occurrence)` から作る。異なる type use は AllE 規則 node の identity u を持つ。この u は有限導出の位置であり、動的 receipt ではない。宣言の再帰使用では label を再登録せず、現在の型引数環境と有限な traversal trace に use を記録する。

各型構文 node と各 atomic contribution に、上の有限座標を付ける。型構造は変更しない。tuple/record/variant/nominal の child label、Function の四 port、interval の lower/upper、binder の body をそのまま用いる。Function arg/arg_eff と interval upper は符号 −、その他の既定の構造辺は +。opaque nominal の未定義な variance を推測せず、与えられた宣言 template の型付き辺だけを辿る。

row/union の複数寄与が同じ公開位置にある場合、寄与を区別する内部 trace tag を残し、公開 path に架空の child label を加えない。従って一つの公開位置は複数の occurrence trace を持ちうる。以下の定理は公開 path の一意分解を要求せず、**構築された trace ごとの分解**を使う。type denotation や family の一致で trace を同一視しない。

### 2.2 代入 constructor

`Sub_u(T,σ)` は有限 syntax/descriptor に対する次の再帰構成である。

1. 代入対象外の atom は identity と元座標を保存する。
2. 自由 atom a の occurrence o に遭遇し a∈dom σ なら、σ(a) の descriptor を参照する `Hole(u,o,a,σ(a))` を置く。展開時に右辺の各 contribution はその右辺自身の元座標と Hole の親座標をともに持つ。右辺を単に a へ改名したり、親座標を捨てたりしない。
3. 構造 node は同じ child label/符号を保ち、各子へ同じ σ を適用する。row の各寄与にも同じ処理をし、寄与 trace を残す。
4. 内側 `∀b` は必要に応じて先に alpha-renaming し、σ の自由変数を捕捉せず、body では b を domain から除く。元の binder の provenance は alpha-renaming 対応を通じて保持する。
5. `N<T̄>`/template 参照は同じ宣言 label と `Sub_u(T̄,σ)` の環境を保存する。body を再帰展開しない。型パラメータへの lookup 時は、宣言 formal から actual argument への接続も Hole trace として記録する。

同時代入なので σ の右辺に σ を無条件にもう一度適用しない。後続の τ は別の Sub node とし、合成は §4 の flattening で比較する。この区別は `σ(a)=b, σ(b)=C` で a を勝手に C にしないために必要である。

構成は有限な入力構文を訪問し、再帰参照では descriptor を作って止まるので有限時間・有限サイズである。これは新たな runtime データ構造の採用ではなく、source 導出上の証拠構成である。

## 3. 有限 path の factorization と極性

`Walk(T,θ,k,w)` は root k から有限語 w を解釈する。結果の各要素は

`(公開位置 (k,w), sign, 静的 endpoint β, provenance trace π)`

である。環境 θ は現在の template formal を有限 descriptor へ結ぶ。構造辺を一つ辿るたび w の label を一つ消費し、その符号を累積する。Hole/型変数 lookup は語を消費せず参照先へ進み、trace にその接続を積む。nominal を開く辺は既定の constructor label を消費する。row の同位置寄与では各寄与の trace を列挙する。

未束縛 atom はその位置で停止する。bound variable は binder 環境により解決し、別 binder の同名 atom と混同しない。query は無限 subtree を先に開かず、w に必要な spine と終点の有限寄与だけを読む。

**定理 T1（有限 query と trace factorization）。** 上の形成条件の下で各 Walk は終了する。`Walk(Sub_u(T,σ),θ,k,w)` の各 trace は、元の T の有限 traversal と、そこで遭遇した Hole の右辺 traversal を交互に接続した有限 trace と一対一に対応する。公開 path は各部分で消費した語の連結、符号は root 符号と全ての実際の child 符号の積である。逆にそのように型と環境の接続が一致する trace を接合すると、代入後 Walk の trace になる。

証明。有限 query の実行 derivation に帰納する。構造辺の場合は先頭 label を同じ辺で消費し、残り語の帰納仮説へ辺符号を掛ける。Hole の場合は同じ未消費語で右辺 descriptor へ入り、親 occurrence と use u を trace に記録する。これが接続位置を一意に決め、右辺の内部 trace に対して帰納仮説を適用する。binder は capture-avoiding な環境制限、nominal は同じ宣言と actual parameter 接続であり、同じ二場合に帰着する。row の場合は寄与 tag を選び、各 trace に帰納仮説を適用する。元の多重 trace は保持される。

終了は消費語長と、各位置での有限 alias/parameter 解決の整礎性による。後者は有限 well-formed 代入と既存の無進展 cycle 禁止による。recursive/nonregular nominal は constructor label を消費してから body へ入るため、instance の大きさが増えても語の長さを減らす。終点の寄与列挙も同じ無進展条件に従う有限構造だけを読む。逆構成は trace 中の明示 Hole 接続を再生し、各場合の規則を逆向きに適用する。□

単一の非再帰 occurrence の場合はよく知られた `w=vz`、`sign(w)=sign(v)·sign(z)` になる。一般の場合は複数の template/Hole 接続があるので、全体を一回の prefix/suffix に無理に縮めない。

**系 T2（符号付き occurrence の exactness）。** provenance を忘れる射影は、capture-avoiding 代入後の型の各構造 traversal とちょうど対応する。trace を忘れて同じ endpoint/位置を set 化した occurrence 集合も一致する。ただし type normalization/compaction による別の構造同一視はこの射影に含めない。

証明。T1 の接合は通常の構造的代入と同じ lookup/child 規則である。両向きの trace 対応を射影する。符号は同じ child 積であり、内部の反変位置を落とさない。□

## 4. 型導出、AllE、template-use と同時代入

**定理 T3（導出からの annotated substitution）。** 任意の上記 d,σ について、型代入後の導出 dσ と §2 の annotations を有限に構成できる。source elaboration を先に行い同じ全 packet 代入を行う場合と、先に annotated substitution を行い elaboration する場合は、alpha-renaming と明示した Hole trace の接合の下で一致する。

証明。値・式・pattern・evidence の有限規則木に同時帰納する。各 constructor/field/case では同じ宣言 label、同じ型引数、同じ子への σ を使う。tuple、record、variant、delay、Function 四 port は子の帰納仮説を符号付き辺で接合する。qualified telescope、handler の payload/response、adapter の両端、scope template にも一つの同時 σ を使うので、端点ごとに別 instance が入らない。

AllI は環境と自由変数条件を含めて binder を fresh にし、body の帰納仮説を使う。共有 graph/captured environment に自由な binder を一般化することは元規則が認めていない。AllE node `u=AllE(d₀,A)` の elaboration は `El(d₀)[A]` である。`d₀σ` の結果型に Aσ を適用する導出と、元の全称除去結果へ σ を施す導出は capture-avoiding substitution の合成則で alpha 同値となる。annotations については u の Hole と σ の Hole を順序どおり連結する。同じ消費 path を T1 で分解すれば、両側の trace は同じ元 occurrence と右辺 contribution を持つ。これは単なる endpoint 型 equality ではない。

nested AllE の合成で生成される二つの Hole 列と、合成代入にその履歴を付けた Hole は、連結列を標準表示とすれば一致する。合成時に履歴を消す定義は使わない。右辺に同名だが別 binder がある場合は alpha-renaming の対応を先に適用する。

template-use は宣言 label を保持し、formal 型・項引数への同時代入を行う一規則である。型引数の Hole 接続と body 内の formal lookup は同じ環境を読むため T1 が適用できる。再帰参照では signature に対するこの一規則で止まり、body 実行安全性を帰納前提にしない。各 body は有限表内で別途同じ構築を受ける。項 binder の置換では各 use に付いた AllE 列を同じ順序で残す。型代入は source Call、実際の receiver 確保、receipt 生成を発火させない。以上は S-AllI/S-AllE、source 使用共有補題、D の有限 template 閉包の構文的規則そのものであり、V1 の値型代入に provenance の構成を追加した。□

これにより inserted occurrence の由来は、元 binder、実際の AllE node、代入右辺 node、template formal/actual 接続から導出される。「代入後の正しい provenance が既にある」という前提を除いた。

## 5. 代入後 recipe を構成する

### 5.1 元成分別の有限 schema

K の各 root k と代入後 descriptor Tσ を登録する。静的 endpoint β をパラメータにする recipe schema は

`Rσ(k,β) = (k, Tσ, θσ, predicate endpoint=β)`

である。その membership query は有限語 w に Walk を行い、β に達する **全 trace** π を返す。各返却行は元座標 o と全 Hole 接続を含む。空の言語を持つ schema も登録してよい。空か否かの無限言語判定を recipe 生成の前提にしない。β の型 identity を query する場合も、元座標や receipt を β に置換しない。

K は有限、descriptor は有限なので、この parameterized recipe は有限に構成できる。非正則な全 endpoint instance を先に列挙する必要はない。具体的な出力 path p に対しては Walk が有限個の endpoint/trace を返し、それぞれの endpoint に対応する schema を参照する。

**定理 T4（recipe の置換対応）。** Rσ(k,β) の各成功行は、元 source の k から出発し、T1 の typed Hole/template 接続を通って代入後 endpoint β に至るものにちょうど対応する。符号、元 component、接続履歴は全て保存される。

証明。schema は Walk の結果の endpoint predicate による選択として構成した。T1 の両向き対応へ同じ選択を施す。predicate は endpoint の静的意味だけを選び、provenance を捨てないので、違う a,b が同じ β に至っても二つの元成分行が残る。□

これは完成した Match 表を入力にしていない。source 型導出と σ から interpreter と選択 predicate を構成した点が R の S1–S3 に対する進展である。

### 5.2 class は置換後に定義し直す

代入後の公開正位置集合を

`Iσ⁺(β)={p | Walk(Tσ,p) が sign=+、endpoint=β の trace を持つ}`

とする。非空の同じ集合を持つ endpoint の semantic class を qσ とする。これは旧 q の像と定義しない。

各**正の出力位置** p（sign(p)=+）の endpoint 集合 Aσ,p は qσ について飽和している：

`qσ⁻¹(qσ(Aσ,p))=Aσ,p`。

証明は Iσ⁺ の等号の定義による両包含である。従ってその位置に現れる class の recipe は、class の endpoint ごとの Rσ のタグ付き和として正確に表せる。元座標、Hole trace、entry k は union の中に残る。これが R-S2 と前稿の商保存へ与える正しい代入後の入力である。

**計算可能性の境界。** regular な有限 signed graph が構成できる場合は、R-S1 の到達可能性算法で qσ を計算し、R-S2 の有限 recipe を実際に生成できる。一般の非正則 descriptor では本稿は qσ の判定器を与えない。Rσ の有限 schema と pointwise query は無条件に構成できるが、「この二 endpoint の全無限位置集合が等しい」という判定とは異なる。ある有限出力 p で同時に現れることだけで class を作らない。semantic quotient の存在から compiler がその quotient を計算できるとは結論しない。

## 6. actual receipt と凍結済み証拠

future actual entry の保護導入は元の entry/profile 規則のままとする。新たに保護された occurrence の proof label は T4 が返す元座標と trace による。既存 scope を輸送した occurrence には、**既存 Origin への参照**を残し、新しい σ/β で Origin を書き換えない。proof trace はこの参照を説明するものであり、scope の再発行ではない。

future output entry の表生成では、recipe 行にそのときの lexical `ρ(k)=b` と元 receiver r を結び、同じ tuple に provenance 条件と path predicate を保持する。Match はその一行の元 provenance、actual b,r、path を同時に照合する。従って同じ instantiated family/型であっても、別 b' はその行に一致しない。新しい call は新しい actual entry の規則だけが b' を作る。

**定理 T5（捕捉非干渉と recipe matching）。** T3 の type application/template substitution 自体は、既存 b,r,t,Origin,B_t,L,H を変更しない。新しい recipe から actual entry で生成した表について、T4 の matching は元成分別表の tagged union と一致する。従って同じ actual target の grouped release は、前稿の実 crossing/query 保存へ接続できる。

証明。Sub と Walk の入力/出力には動的 store の書換え操作がない。S-AllE の核規則も receiver を確保せず、既存 capture を共有する。既存証拠を読む場合は同じ Origin pointer と同じ凍結 B_t を読む。新しい表の各行は T4 の実際の trace と ρ の一つの actual binding から作る。存在量化を元成分ごとの行へ分配すれば tagged union の Match が得られ、別 receipt/receiver/元座標の列を直積で結合する余地はない。前稿の保存に必要な同一 tuple の前提をこれで与える。□

ここには重要な限界がある。捕捉済み B_t が未具体化の template/path descriptor を含む場合、後の使用はその**保存された descriptor と正当に与えられた使用引数**を解釈する。型の自由変数の environment を勝手に差し替えない。S-AllI の環境自由変数条件は既存 shared capture の再型付けを防ぐ。古い単なる文字列 path の表しかなく、後の挿入 path を元 origin へ戻す descriptor が残っていなければ、T5 はその表からの復元を保証しない。その場合は次節の消去境界であり、captured B_t を後付けで再構築して修復したことにしない。

raw resume は新しい AllE/entry を作る規則ではない。同じ保存 code の必要な template 使用を実行する場合も旧 receipt/target を保持し、現在の world に再結合する。T5 は foreign continuation の導入適合性を証明するものではない。

## 7. 三つの falsifier と消去の不可能性

1. **旧 class の再使用。** 元位置 p に a,b が共起していても、σ(a) と σ(b) が違う構造を持てば descendant の位置は違いうる。例えば同じ共変 row 位置の a,b に、a 側では x を record field f、b 側では y を field g に持つ well-formed な成分を入れると、子位置 p.f と p.g は異なる。元 class のまま x,y を統合する判定は誤り。具体の型 kind がこの例の record を許さない場合も、対応する admitted な異なる child constructor を選ぶ必要があり、kind 不整合を source 反例として使わない。T1/T4 は個々の右辺 trace を保持し、この誤りをしない。
2. **反変挿入。** 元の a が Function argument の下にあり sign=−、σ(a) 内の b がさらに Function argument にあれば `−·−=+`。挿入前の a の符号だけを b へコピーする規則は誤り。T1 の積はこの b を正位置として数える。
3. **family の偶然一致。** a,b を同じ concrete family/型へ代入しても、別元座標・別 receipt b₁,b₂ は同一でない。b₁ の route のみが実際に crossing した状態で b₂ の保護は残る。Rσ の endpoint equality を Origin equality に使う方式は失敗する。

消去の正確な障害は、`(元 formal/component occurrence, AllE/template 接続履歴, actual origin への参照)` である。これらを忘れた compact class c とその denotation だけを入力にする復元関数は一般には存在しない。同じ消去結果になる二つの decorated 入力を、a 側の contribution が b₁ に由来する場合と b₂ に由来する場合として作れる。Match(t,s) は t が b₁ だけを捕捉したとき二入力で異なる。復元関数は同じ入力に同じ出力を返すため、両者に正答できない。これは抽象表現に関する識別不能性の証明であり、現 compiler が実際にこの情報を消したという source-qualified 反例ではない。

本稿の enriched-source construction は情報を最初から有限導出に付けるためこの障害を回避する。その情報が既存 compiler のどの変数・edge・weight・origin に符号化されるかは別の実対応義務である。新しい並列表の導入を既定実装として要求しない。

## 8. R S1–S5 と候補 core への適用

| 元の義務 | 本稿で具体化したもの | 残る範囲 |
|---|---|---|
| R-S1 の位置 query | T1/T2 により arbitrary well-formed σ と非正則 template の任意有限 path を解釈 | 非正則な全位置言語 equality の算法は未構成 |
| R-S2 の class recipe | 置換後 Iσ⁺ を再定義した飽和性と元成分別 schema の tagged union | general qσ の計算と全 class 列挙 |
| R-S3 の origin matching | T3/T4 で挿入 provenance を実導出から生成、T5 で actual tuple と結合 | 既存 native representation からの対応、既捕捉表の descriptor 所有 |
| R-S4 の release 保存 | 同じ actual target の表に前稿の crossing/query 定理を適用 | 元の全 source constructor/native consumer の対応 |
| R-S5 の freshening | 単射改名は Sub の特殊場合。任意代入は T1–T5 の trace 接合で扱う | 古い quotient の使い回しを正当化しない |

candidate core の V1/V5 の AllE/template-use は元の構文的型代入を使い、今回 T3 により source provenance も同じ導出から構成できる。G の recipe を使う命令には Rσ の有限 descriptor と query を渡せる。I2 の finite interface は現在の有限 path/query の結果を観測するため、この schema が定義する実値をその欄へ入れられる。無限個の type instance を cell 色に列挙する必要はない。

一方 G1 が全一般 instance の共起 class を計算済み recipe として要求する箇所は、T4 と I2 だけで閉じない。regular instance または別途正当に生成された class certificate の場合に R-S2 と本稿を適用できるが、これを親の source 領域制限にしない。general class-generation の義務を OPEN として保持する。non-enumerative BuildLocal、自然な ordinary inference、A/B、主型性、停止性も独立のままである。

## 9. 次の owner と有限な証拠要求

| TODO | owner / 次に必要なもの | exact falsifier |
|---|---|---|
| SUB-PROV-NATIVE | source AllE/FreshUse/generalization と compact rewrite の producer/consumer。導出座標 o、接続 trace、既存 Origin 参照がどこに残るかの一つの往復対応 | 同じ compact 入力から異なる required Match が出る二実 source 導出 |
| SUB-CLASS-GEN | co-occurrence construction owner。一般 instance の正確な class 生成、または元の承認領域を保つ別の finite representation 論証 | 同位置の有限 sampling が一致するが後の有限 path で異なる二 endpoint |
| SUB-CAPTURE | R-Capture/R-Match と template-use consumer。捕捉済み descriptor の環境所有と後の合法な引数供給の対応 | AllE が旧 B_t/Origin を書き換える、または保存 descriptor 不足を family equality で補う |

以上は証拠要求であり、実装許可ではない。minimal provisional instrumentation が必要なら Luna が別途 exact lease と出力を指定する。本 packet は既存 source/compiler を変更しない。

## 10. 固定依存、検査、停止

契約と以下9依存の現 bytes SHA-256 は全て照合一致した。

| input | SHA-256 |
|---|---|
| cooccurrence-source-recipes | `ee99b45dbc49c3563220335b350814ed422bf0fbe7edfcb4cfaef476da986cdb` |
| cooccurrence-release-preservation | `0c5731f1b287c1016d08b645707533a482832aa44dce6b93aae899375c721c84` |
| source-core-finite-interface | `d37a30f1f59ad327ebcba129db5b069f4eed1f839d1733230863fdb711a16488` |
| corrected-core-value-continuation | `4d8ffd63cbb65cd6917145fa31a4cb3f04656a19f7b71fd0e3fdd6cecaabfbeb` |
| source-core-action-coverage | `36672ef591f42a281a04f14fb7ddc4c5283c119de20fee15168e37cbbf13201a` |
| source-type-safety-ja.tex | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| dot-selection-safety-ja.tex | `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b` |
| whole-language-semantics-ja-expanded-20261023.tex | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |
| cooccurrence-release-clarification | `c9eb9b8d274172f02bc82088896c30dd92e219a02adf6ba22418b2cc34207d12` |

R と値継続稿の著者は primary、有限 interface 稿と G の初稿は `/root/astra_corrected_machine`、G の既査読 repair は primary、前稿の著者と修正帰属はその frozen bytes を保持する。本稿をそれらの独立査読と数えない。S-AllI/S-AllE、source 使用共有、D の template 閉包、I の nonregular query 境界、V1 の同時代入を直接読んだ。過去の単射改名証明はその前提内で再利用し、任意代入への無条件拡張、旧 quotient、A_all、stale world、receipt の再実行は再利用しない。

三段階: annotated substitution、path/recipe 構成、AllE/template と親への適用。190秒/三段階の grant。正確な active duration は UNKNOWN、未観測時間を返却しない。検査は hash 照合と紙上の導出/trace 帰納法。tests、build、compiler、network、Git、子 agent はなし。新規/変更/scratch path は本稿だけ。最終メッセージが単一 handoff。r1 の全書込みを停止して凍結し、独立レビューへ渡す。worker STOPPED、親は OPEN、次の作業は Luna の所有割当による。
