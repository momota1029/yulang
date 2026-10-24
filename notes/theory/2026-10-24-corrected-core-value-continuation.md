# 修正核の値型・継続導入・繰返し再開の健全性

Revision CV1。著者 `/root`。独立査読前の構成的証明。実装変更なし。
対象は有限の名前解決済み source 導出から作る修正候補核であり、全 frontend の正しさ、推論器の完全性・主型性、候補政策の採用とは区別する。

## 1. 固定入力と主張

| 入力 | SHA-256 |
| --- | --- |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| `docs/yulang-dot-selection-safety-ja.tex` | `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b` |
| `notes/theory/2026-10-24-source-core-action-coverage.md` | `36672ef591f42a281a04f14fb7ddc4c5283c119de20fee15168e37cbbf13201a` |
| `notes/theory/2026-10-24-corrected-machine-simulation.md` | `fffb4f1540739020a0702d4f7b07d41cd9b68a9063f36d24292914b84e6b606d` |

以下 O/S/D は順に操作稿・source 稿・選択稿、G は source-core-action-coverage を指す。基準 commit は `59057b660a5a46f448d4c6feda041cb3df3bb38f`。O の型付け規則・primitive の有限値上の定義を用い、その旧健全性定理を前提にすることなく、S の修正 lifetime と D の eabs/eapp、G の結果 adapter 接続を含む核で証明し直す。effect inclusion 自体は G5 の別の結論である。

宣言表 Δ は O:103–244 の全 constructor/operation/primitive/template signature を持つ有限の表である。各 body には **構文的**な有限型導出がある。recursive body は既登録 label を参照し、他 body の実行安全性を型規則の前提にしない。型・項の同時相互再帰はこの有限環境の下で検査する。

値 graph H と参照型環境 Ξ の整合性を `Δ;Ξ ⊢ H` とする。各 node の型が Ξ の対応型であり、alias・View・roll・型証拠だけを循環する経路を持たない。実際の data/lambda/delay を通る再帰は許す。D の eabs は実行を一段経る code 値であり、呼出し時の計算再帰を禁止しない。これは原稿の guard 条件を引き継ぐ。

追加実行型は `Kont(Q,A)` と `D ⇒e^k A`。後者は source Function `C(D,A)` と別 constructor で、eapp だけが除去する。精密な効果・profile を忘れる射影でも nominal/family/型引数の identity と payload/response 型は残す。以下では型導出の finiteness を仮定するが、計算の停止・型の単相性・continuation の単回使用を仮定しない。

## 2. 代入と graph 拡張

**補題 V1。** (a) 同じ Γ における `v:A` を `Γ,x:A ⊢ M:B` へ capture-avoiding に代入すると `M[v/x]:B`。(b) 一つの型代入 σ を環境、宣言 instance、全 payload/response、結果、body に同時に施すと型導出が保たれる。(c) 新しい実行 control/activation 名の選択は値型に影響しない。既存の immutable evidence、family、State scope、resource、型引数は改名しない。(d) 既存 node と型を固定した well-typed な graph 拡張は既存導出を保存する。

**証明。** (a)(b) は値・計算・handler・continuation・evidence abstraction の有限型導出への同時帰納法を使う。変数 x は与えられた導出、それ以外は元の lookup。構造導入・除去は全子への同じ代入で label/presence/arity を維持する。Value lambda の formal は A、Computation lambda は UA のまま。let、lambda、continuation の項 binder、Λ の型 binder、polymorphic arm の rigid binder、eabs の evidence binder を先に fresh にする。`α∉fv(Δ,Γ)` の全称導入条件は shared resource の型も含むので、外側共有値を use ごとに再型付けしない。handler の payload と response には同じ σ を使う。wrap、mapop、template、direct evidence の両端と全子も同じ σ である。rec の全 node/body は同じ再帰環境への同時代入で処理する。guard は参照 identity の capture-avoiding 置換で保たれる。これで全型規則を尽くす。

(c) は型規則が control 名を型 constructor として除去しないことから各規則に帰納する。S の L-Enter は過去の evidence を変更せず、View は同じ underlying value を保持する。(d) は reference 規則が既存 Ξ(r) を読むことによる帰納法。rec allocation では fresh r_i と `Ξ'=Ξ[r_i:A_i]` を先に作り、各 RHS の `x_i:A_i` を `r_i:A_i` へ同時置換する。古い node を書き換えず、新たな cycle は検査済み RHS の guard を通るので `Δ;Ξ'⊢H'`。body も(a)で型付く。□

非正則な多相使用でも、各実際の使用で σ は有限な構文代入である。この補題は異なる使用の instance を同一視せず、有限個の全 instance を列挙する必要もない。

## 3. canonical forms と全 primitive

**補題 V2（必要な値 constructor）。** well-typed graph 下の閉じた値を指定型の elimination に使うと、有限の外側参照/View/型適用処理の後、次の対応する constructor が得られる。

| 入力型 | 得る値/証拠 |
| --- | --- |
| base、tuple、record、variant、D⟨T̄⟩ | その base constructor、正しい arity の tuple、全 required field を持つ可視 record、同じ tag/nominal constructor と同じ instance の payload |
| UA | delay と保持された body |
| C(A,B) | Value/Computation lambda、または型付き wrap |
| Kont(Q,A) | 同じ Q response hole と A result を持つ保存計画 |
| D ⇒e^k A | 同じ k の eabs |
| A∨B、A∧B、μα.A、∀α.A | 明示 injection、同じ underlying value の両証拠、roll、型抽象 |
| ⊥ | 閉じた値は存在しない |

**証明。** 最後の introduction を反転する。暗黙 subsumption や endpoint 型一致だけで任意値を callable にする規則はない。View は値を変えず、type application は V1 に戻る。外側 graph 参照は guard により無限 alias/型証拠 cycle を形成しない。構造 constructor に到達するまでの各段階は有限である。⊥ の introduction はなく、guard のない cycle による偽の底値も作れない。intersection は元の同一値に関する証拠を選ぶだけであり、異なる値を生成しない。□

**補題 V3（primitive）。** O:883–925 の各 primitive は宣言 signature と同じ型の引数に対して、宣言結果型の Ret または列挙済み Fail を返す。

**証明。** V2 で arity と raw 入力 constructor の照合は成功する。以下は同表の全62個を尽くす分類である。

- BoolNot/BoolEq/BoolToString は bool/bool/string。
- ListEmpty/ListSingleton は同じ A の有限 vector、ListLen は int、ListMerge は同じ A の連結。ListIndex は bounds 検査後の既存 A、ListIndexRange/Raw は部分 vector、ListSplice/Raw は同じ A の連結。ListViewRaw は宣言された empty または head:A と tail:List A の constructor。
- StringLen/LineCount は int、StringIndex は規定の grapheme char、StringIndexRange/Raw と StringSplice/Raw は string。StringLineRange は int payload の既定 Range constructor。StringEq は bool、StringConcat は string、StringToBytes は byte vector。
- IntAdd/Sub/Mul は数学的整数。IntDiv/Mod は分母0で DivideByZero、それ以外は整数商・剰余。IntEq/Lt/Le/Gt/Ge は bool。IntToString/Hex/UpperHex は string、IntToFloat は binary64。
- FloatAdd/Sub/Mul/Div は NaN/無限大も含む binary64 に閉じる。FloatEq/Lt/Le/Gt/Ge は bool、FloatToString は string。
- CharEq/IsWhitespace/IsPunctuation/IsWord は bool、CharToString は string。
- BytesLen は int、BytesEq は bool、BytesConcat/IndexRange は byte vector、BytesIndex は0–255の int。BytesToUtf8Raw は有効 string と byte 長 int の tuple、BytesToPath は path、PathToBytes は byte vector。
- YadaYada は Unimplemented のみ。全 bounds 操作は不正範囲なら BoundsError。正常型の値を捏造する failure はない。

grapheme/line 分割、range 正規化、formatting、character predicate は O が指定する有限列上の全域 helper の任意の選択に一様である。これらの戻り値の型は上の定義から得られ、任意の Yulang body の安全性を helper の条件に隠していない。未指定の byte-for-byte formatting 選択を固定する定理ではない。□

## 4. frame と continuation を構文から導入する

`F:A⇒B` を、A 型の計算穴を一つ持ち B 型の計算を作る構文的導出とする。

| frame | 穴と全体の型/保存するデータ |
| --- | --- |
| let x←[] in N | hole:A、x:A⊢N:B、全体B |
| scope、View、release | hole:A、全体A。metadata は constructor を変えない |
| Handle_h [] | hole:A、h:A⇒B、全体B |
| mapop_w [] | hole:A、全体A。w は同じ operation の P→P' と Q'→Q の型付き code |
| wait_h(q,p,K;…;[]) | hole:1∨B、全体B。pending p:P_o(T̄)、K:Kont(Q_o(T̄),A)、h:A⇒B と remaining arms を保持 |

**補題 V4（plugging と切出し）。** F:A⇒B、M:A なら F[M]:B。逆に F[M]:B の導出を active hole へ反転すると同じ中間型と両導出が得られる。型 A の対象計算からの request `(o,T̄,p,K)` は、payload `p:P_o(T̄)` と `K:Kont(Q_o(T̄),A)` を持つ。

**証明。** plugging/inversion は上の有限 frame 列への帰納法で、各行の型規則を一つずつ適用・反転する。perform は response hole `x:Q ⊢ Ret x:Q` から恒等 K を作る。request propagation の長さに帰納する。bind は型付き suffix を K の body に追加する。scope/View/release は同じ result 型を保つ frame を追加する。選択されなかった handle は A⇒B を追加し Kont(Q,B) を作る。選択された shallow handler の arm に渡す時は、その frame を追加せず Kont(Q,A) のままとする。

wait の attempt が別 request q' を出す場合、その continuation の result は `1∨B`。これに型付き wait を追加すると result は B となり、元の p,K は閉じた typed data として残る。mapop の一致 case は payload adapter a:P→P' を実行し、response hole z:Q' に対して `let z'←r(z) in mapop_w M[z'/x]` を作る。r:Q'→Q と元の x:Q⊢M:A に V1/let を適用して Kont(Q',A) を得る。同じ w の両方向を使用する。不一致 case は元 instance と frame を保存する。a/r が request を出す場合は、通常の bind/wait の帰納 case であり無視しない。これで七 frame を尽くす。□

V4 は source から生じた K の **導入契約**を構成する。K が安全だという外部仮定から型を得るものではない。再帰する continuation body も有限 code label と有限 frame 列の導出で型付く。

## 5. 修正機械の一段保存

**定理 V5。** 閉じた `Δ;Ξ⊢H` と `Δ;Ξ⊢M:A` から修正核が一段進み `(H',M',world')` になれば、既存 node 型を固定する Ξ'⊇Ξ があり `Δ;Ξ'⊢H'`、`Δ;Ξ'⊢M':A`。値型については eligibility の任意の全域 Boolean 選択に一様である。実際の効果・衛生性は固定した W-Eligible と G5 を別に用いる。

**証明。** step 導出の高さに帰納し、最後の規則を列挙する。

1. let-return、Force-delay、split、switch の選択、unioncase は V1。field は required presence、optional lookup は present の A payload または unit injection。choose/unroll は同じ値の明示証拠を除去する。type application は全 occurrence への V1(b)。値の graph/View 参照処理は V2 の underlying constructor を保つ。
2. rec は V1(d) の fresh graph 拡張。template は formal への同時型・項置換で登録済み body に移る。eapp は同じ k の eabs body に evidence 値を代入し、admin.effect の View で囲む。admin.result も同じ結果型。eapp は source Call entry を実行しない。
3. primitive は V3、perform は V4 の恒等 continuation と同じ operation instance。Fail は全 result 型を持つ列挙済み failure のまま伝播する。G4 が許す失敗後の world 抽象化は値型や failure tag を変更しない。
4. `Call(f,t)` で f:C(A,B)、t:UA。fresh owner と scope は値型を変えない。wrap(f,a,r):C(A',B') を剥がす際は、t:UA' に対して `Delay(let z←Force t in a(z)):UA` を構成する。内側 enter の result B は r:B→B' へ通常 bind で渡る。同じ owner を維持する。最内の Value entry は receipt/view を付けた t_u:UA を Force して x:A に束縛する。Computation entry は t_u:UA を x:UA へ代入する。body、declared result consumer、全 result adapter はそれぞれ実際の導出に従う通常計算であり、各自の request/failure も上記 frame 規則を通る。
5. Handle の Ret は A 型の値を value arm に渡す。Req は V4 の p,K を、同じ T̄ で instance 化した operation arm に渡す。polymorphic arm の rigid schema を payload と response で別々に具体化しない。false eligibility は同じ型の残り候補、true は `1∨B` 型の attempt。正常 body result A_i はその arm の実際の直接結果 adapter A_i→B へ bind され、正常 adapter result だけが Yes(B) になる。adapter の request/failure は ordinary bind の場合。Yes はB、No は同じBの残り検索、operation exhaustion は `Req(q,p,H_hK):B`、value exhaustion は MatchFailure:B。attempt request の wait capture は V4。
6. Raw Resume の `K:Kont(Q,A)` は保存 body `x:Q⊢N:A` の構文導出を持つ。現在の v:Q を V1 で代入する。S の L-Enter は captured control slot を借用または fresh owner に結び、code の型を変更しない。過去の receipt/receiver/scope/target は固定する。raw resume に source receipt の再実行はない。同じ saved body は変更されず、次の resume でも同じ型導出を使える。public resumption callable の Value force は通常 Call の場合であり、raw Resume と混同しない。
7. mapop の正常値は同じ型。matching request と response は V4 の a/r の導出、不一致 request は同じ instance。a/r 自身の効果は通常 frame 内で型付く。release の target 導入、Ret の view、Req の R-Cross と ReleaseCont は、payload/response/result 型を変えない。scope の own/borrow completion、View enter/leave、現在の L/activity の観測、No の current-world 再接続も underlying typed data を変えない。新しい route/evidence は既存の型付き path に付く metadata であり、値の payload を偽造しない。
8. 子の一段を持ち上げる context 規則は帰納仮説と V4 plugging を使う。以上が通常構文、eapp と七 frame の全 principal/context case である。Bad が生じる不正 arity/constructor/field/call/response は V2 と同じ instance の規則に反する。□

## 6. 進行、開いた protocol、source-defined code

**定理 V6（有限 prefix の値安全性）。** 閉じた well-typed な初期 graph/plan からの各有限実行 prefix の末尾は、A 型の Ret、同じ instance の型付き Req、列挙済み Fail、または次の一段を持つ計算である。外へ露出した request に外部から応答する場合、応答はその同じ `Q_o(T̄)` の構文的型導出を持ち、必要な新 graph は既存 node を変更しない well-typed な拡張であることを要求する。任意回の同じ K の resume を許す。

**証明。** 進行は active context の有限深さを辿る。redex の値引数には V2 を適用する。primitive は V3、rec/template は有限一段の構成、handler の候補列と各 metadata query は指定された有限入力上の全域規則である。候補を決定してから実行する guard の発散は、その計算の次の一段を許す。Ret/Req/Fail の child には V4/V5 の全 frame case があり、空 context なら三終端の一つ。absurd は閉じた⊥値が存在しないので起こらない。これで stuck/Bad の場合はない。

prefix 長の帰納法で内部 step は V5。外部 response の場合、V4 が供給した K:Kont(Q,A) と応答 v:Q、V1 の graph weakening/代入で次の plan:A が得られる。各 resume は saved K を変更せず同じ導出を再使用するので、単回使用や snapshot 復元は不要。任意の無限実行に最初の Bad があれば、その有限 prefix への結論と矛盾する。□

**系 V7（内部導入を foreign 条件から外す）。** source 内の lambda/delay/eabs/wrap の全 body、値 graph、captured K が持つ値型契約は、有限 source/evidence 導出と V1–V6 から得られる。内部 callback や runtime が切り出した continuation の安全性を host に仮定する必要はない。

**証明。** closure の導入規則は body の構文導出と同じ lexical capture を持ち、各 force/call/eapp は V5 の対応 case へ入る。保存 K の導出は V4 が実際の capture frame 列から構成する。generalization は既存 shared Γ を固定した全称導入、use は一つの全体代入であり、V1 の範囲に入る。G の型付き body-result adapter 接続も V5(5) に含む。したがって、有限 source/evidence 導出から得た各内部導入へ V6 を適用できる。□

精密な **効果**導入には各 body の Gen(d) inclusion がさらに必要である。内部 code に対しては G の body/latent/reentry port と実 capture grammar によりその契約を検査する。外部 host が返す任意 code は source の子導出ではないため、その精密な導入契約を独立に要求する。値型だけの callback に小さい効果契約を自動的に付ける結論は出ない。

外部 protocol は実際の仮定である。例えば operation が int 応答を要求するのに host が callable を返せば、続く int primitive の raw constructor 検査は失敗しうる。Yulang 内部の証明から任意 host の契約遵守を導くことはできない。逆に、閉じた核の実行は typed request で停止でき、host が常に応答することも要しない。失敗後の host 再入や終端 world cleanup の選択は本稿で追加しない。

## 7. 主定理への戻し方と査読境界

V1–V7 が G5 の独立した「value safety/Bad 排除」の前提を、この明示候補核について構成する。finite-interface の前提は別稿の担当である。両者が独立査読を通り、それぞれの実際の前提を満たせば、G5 と合わせて値・効果・型付き繰返し再開の resolved-core 定理を得る。任意の推論受理 source や任意の外部 code に範囲を拡大しない。

残項は全表層からこの source 導出への構成、source policy と承認済み観測の対応、推論の元の A/B・自然性・主型性・停止性、および実 native 対応である。native の実装作業は今回除外されている。host が守るべき精密 protocol と、内部導入から本稿が証明した契約を同じ未解決項に戻さない。

静的な定義・全規則の読取りと紙上帰納法のみ。テスト・build・compiler 実行なし。固定入力 hash は記録した bytes と照合した。著者はprimary、独立査読は未実施。子agent/実装/scratch pathなし。
