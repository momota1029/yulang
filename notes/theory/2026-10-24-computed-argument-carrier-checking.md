# 実際の computed argument の whole-carrier checking

LET-FREE-CARRIER-20261024/r1。著者 `/root`。独立査読前。元の source 定理を変更せず、[FO2](2026-10-24-finite-observation-source-bridge.md) の χ_e を具体的な actual source family で構成する。

## 1. 証明対象と固定入力

[TU](2026-10-24-two-input-recursive-source-use.md) の **同じ実際の** h₀=λz.0、f=λx.λy.{first=h₀ x,next=f {a=y}}、全 actual inner gκ を使う。U=Int|Bool、A=Record(a:U)、Q=Record(first:Int,next:G_U)。H₀/F_U/G_U の完成した hereditary membership は TU2/TU3 の結論であり、本稿の χ_e を前提にして得られたものではない。そこで必要だった argument は Name x と Record(a:Name y) だけで、元 Name/Record/Return constructors が既に証明したものだった。

I_U/I_A は TU の同じ Value-entry interfaces とする。元の pure Comp(empty,U/A) の whole checking は TU/NR の identity-compatible instance のもの。別の固定 inlet、追加の hard guard、別の received carrier へはその等式を使わない。full original kernel、raw allocator/transitions、current-world compatibility、scope/profile/reify licenses、independent arm laws をそのまま保持する。

本稿では二つの主張を区別する。

* **actual source carrier の構成**: 指定された code/capture/origin の Delay が、すべての合法な指定 Force と後の利用に対し元 Comp(empty,X) の full carrier criterion を満たす。実コードと同じ complete tuple に対する finite proof を作る。
* **任意の抽象 interface 全体の包含**: 独立に与えられた R_e のすべての代替が Comp(empty,X) に入る。この強い主張は raw code の計算だけからは出ない。元 source checking が R_e からの包含を要求するなら、R_e の独立代替も以下の §6 に従って検査する。

この区別により、実際の Delay の導入に必要な証拠を与えつつ、意味を選んでいない computed Call result R_c を暗黙に pure に置き換えない。

## 2. 有限 source grammar と定理の量化

FO の source grammar のうち、まず次を取る。全 binder は元の monomorphic Bind、Name はその actual binding を読む。

```text
F ::= Name f | F-sort の immutable alias
G ::= Call(F,Delay(Record(a:P))) | Select(Qnode,next) | G-sort alias
Qnode ::= Call(G,Delay(P)) | Q-sort alias
P ::= Int literal | true | false | Select(Qnode,first) | U-sort alias
Aggregate ::= Record(l₁:E₁,...,lₙ:Eₙ)
E ::= F | G | Qnode | P | Aggregate | Bind(E,a,E)
```

各 alias の sort はその実際の RHS Return に従い、Bind は有限で非循環な client derivation を形成する。依存先は元の lexical scope に存在する。順序付き Record の各 field を元の順序で評価する。P を carrier の形成時に評価しない。すべての source guards と licensed introductions は元の rule の前提であり、code の純粋性から authority を作らない。

succ は §6 でその **complete primitive contract** により拡張する。FO の succ を含む元 grammar を削除・変更したわけではない。ここで構成した部分と、元のより広い義務を明記する。

結論は全 actual compatible environments/current demand events、全 actual gκ、全有限 client derivations について一つの証明関数として成り立つ。特定の成功 trace を見てから別の witnesses を選ぶ主張ではない。actual registry にまだない future g を先に登録しない。

## 3. 実 code の局所的な評価補題

以下の「request-free」は source code 自身が outward Request を生成しないという意味である。allocation、receipt、Force、actual Return/rebind、scope entry、current-world transition を消す意味ではない。環境から任意の追加 Call を挿入した全 future histories が無作用という意味でもない。future の latent membership は TU の完成した証拠を用いる。

### CA1（同じ raw h₀/f/g と純粋な引数）

同じ指定 Force code の全 prefix/Return の元 pure computation 証拠がある carrier c を与える。元の actual challenge、receipt、guards を持つ各実 invocation について、次を構成できる。

1. h₀ に A carrier を渡すと、その entry はまず c を Force する。その actual Return でのみ fresh z を作り、その後 literal 0 を返す。c 自身が request-free なら、この invocation の source branch も request-free。
2. f に A carrier を渡すと、同じ順に Force、fresh x@κ、inner Lambda allocation を行い、新しい gκ を返す。返した gκ は TU3 の G_U membership を持ち、捕捉 x はその actual A value。
3. gκ に U carrier を渡すと、Force と fresh y@λ の後、h₀(Name xκ)、f(Record(a:Name yλ))、Record construction の順に進む。内部の h₀ と f の引数は既に完成した immutable bindings の Name/Record code なので元の pure checking を持つ。1,2 を適用し、actual Q value を返す。

証明。raw closure inversion を行い、元 ValueEntry/Bind/Name/Lambda/Record/Return の各 transition を一つずつ使用する。1 の body は literal 一つ。2 の body は inner closure の creation だけで、その invocation ではない。3 の body で呼ぶものは h₀ と f だけであり、生成した次の g は Record の field に置くだけで実行しない。従って 3 は 1,2 の既に構成した局所関数を使い、自分自身を再帰呼出しする必要がない。

completed value の型付けは TU1 の ground inclusion、TU3 の actual returned closure certificate、同じ current world の Record introduction により供給する。各 incomplete/admin/zero prefix ではまだ存在しない Return を作らず、未実行の元 suffix と実際の current-world fields を保持する。carrier が有限に完了する場合、各 body は有限個の元 constructor transitions で完了する。元 kernel が stuttering prefix を持つ場合も、その全 finite prefixes は同じ proof function に入り、ここでは kernel の公平性を主張しない。

重要なのは、これは F_U/G_U の任意の abstract inhabitant について「pure input なら pure output」とする契約の逆算ではないこと。本当に指定された raw h₀/f/g にだけ closure inversion を使う。別の callable が同じ endpoint を持ってもこの証明には入らない。□

### CA2（有限 client の actual computation 証拠）

§2 の有限導出の各 node E から、元 raw computation の全 prefix と actual Return に対する証拠関数 π_E を構成できる。E の source branch は request-free であり、actual Return は指定された F_U/G_U/Q/U/Record endpoint の元 hereditary certificate を持つ。

証明。finite client derivation への同時構造帰納を行う。帰納仮定は code の **実行前に証明関数として**構成するもので、子の計算を先に実行することではない。

* Literal/Bool は独立 primitive Return law と TU1。Name/alias は元 immutable telescope の同じ binding/certificate を demand の current event に restrict する。f と g の provider を取り替えない。
* Call(F,Delay(Record(a:P))) では、まず callee を評価する。その actual CalRet の後にだけ inert argument carrier を形成する。receiver の designated Force が開いた時に、P の帰納関数と Record introduction を適用する。その actual A Return を CA1.2 へ接続する。callee と引数の双方が request-free であり、CA1.2 は actual returned G_U を供給する。
* Call(G,Delay(P)) は同様に G の actual CalRet を待つ。G は computed Select でもよく、選ばれた actual gκ/root を保持する。その後の Force に P の帰納関数を適用し、CA1.3 が Q を供給する。Name callee への書換えは行わない。
* Select は operand の computation 証拠の後、actual Record の元 designated field を選ぶ。first は Int の元証拠を TU1 で U へ、next は同じ actual gκ の G_U certificate を返す。選択した latent function を余分に Force しない。
* Record は各 child の帰納関数を元 ordered Bind で合成し、実際の Return fields がそろった current world で構築する。alias Bind も RHS が Return した時だけ fresh monomorphic binding を作り、同じ value/provider の証拠を suffix の環境へ入れる。複数の alias reads は一つの binding を共有する。

いずれの局所 source transition にも外部 Request を発行する code constructor はない。CA1 が呼び出された関数の実 body についてこの点を補っているため、Call という構文を見ただけで効果を消したわけではない。すべての途中 prefix は元 constructor の admin/pending-suffix interface のままであり、real Return の証拠を前倒しにしない。各 world の更新と合法 restriction を同じ tuple 上で合成する。これで全 finite source client derivations を尽くす。□

CA2 はこの actual code family の局所的な evaluation 証明であり、独立に固定された任意の result descriptor への DescMem 定理ではない。外部から latent g に渡す arbitrary carrier の発散や Request は TU3 の元 contract のまま許される。

## 4. 元 Delay criterion への直接構成

[元 carrier 定義](2026-10-08-call-semantic-input-realization.md#43-inert-delay-and-all-execution-observations) は inert formation と **全 independently compatible demand における designated one-layer execution** の両方を要求する。CA2 からこの両成分を実際に作る。

### CA3（computed pure argument の actual χ）

§2 の argument code E=P または Record(a:P) と、その元の licensed Delay introduction を固定する。その actual carrier c_E に対し、元の Comp(empty,U) または Comp(empty,A) の full carrier membership を構成できる。TU の identity-compatible inlet へ同じ証拠を運ぶ写像を χ_E^src とする。

証明。

1. **inert formation。** 元 Delay/reify license、original code E、同じ捕捉 references、provider/origin、scope/authority と dependent witnesses を入れる。形成時には E を実行せず、current configuration を将来の Force に代用しない。PF が構成する package の static law と、その実 license evidence を区別する。
2. **任意の指定 demand。** independently compatible な actual demand event とその current world を固定する。元 immutable restriction により同じ capture certificates をその event へ運ぶ。Force は本当に E の code を開くので、CA2 の π_E をその event に適用する。
3. **全 execution observations。** zero/admin/incomplete prefix は CA2 の same-tuple prefix function。Return の時は同じ actual returned value/provider/current world と TU1 の U/A inclusion。source branch の outward Request がないことは CA1/CA2 が code から証明済みであり、返却型から推定しない。scope/receipt/entry/return の internal fields は残す。
4. **future と自然性。** 返した値の latent/future fields は同じ hereditary certificate であり、将来の invocation はその元 full domain についての certificate を使用する。今の一層の Force を二度実行しない。二つの合法 restriction の合成に対して各 constructor map が元自然性を満たすので、π_E と inert package も同じ合成に従う。

これは有限 client derivation への fold が作る finite proof scheme であり、任意の demand ごとに成功した run を探す oracle ではない。元 source §3.1 の Delay rule の universal designated-execution premise と §3.2 の same-computation checking に、この構成済み関数と identity/Union/Record inclusion を入れる。χ_E^src は実 code/capture/origin の tuple をそのまま運ぶ。□

同じ sort の任意の carrier や、既に選ばれた別の abstract R_e への identity inclusion を証明したわけではない。CIncl(R_e,Comp(empty,X)) が要求される場面では、R_e の全生成子についての checking が別途必要である。CA3 は Delay の actual-source constructor が直接供給する証拠であり、その distinction は FO2 の χ を使う位置で保持する。

## 5. FO の元義務への適用

CA3 は FO2 が不足していた「computed first を含む同じ argument code の全 designated execution」という **source carrier 成分** を供給する。選ばれた actual callee の pure computation、argument code の全 source observations、receiver の full TU certificate を用い、FO1 の全 source phases を構成できる。Name-only ReadInvoke への cast、先行 argument execution、返却 endpoint だけからの checking は不要になる。

全 complete χ_e を必要とする FO2 への適用は、actual carrier 成分に加えて、その edge に本当に付く独立 alternatives の checking がそろった場合に行う。その alternatives は次節の同じ有限 checking constructor で結合する。独立 alternative がない actual-source-only constructor の場合は CA3 だけでその成分の全 criterion を尽くす。存在する alternatives を「ない」と置く許可ではない。

また、computed Call 自体の最終 `DescMem(R_c,O,w;ξ)` はここで定義していない。FO §6 の独立 result constructor の残項、native/source monomorphic binding 対応、一般 primitive/effectful source、local-let publication、intrusion の actual receiving incidence は元の親義務のまま。

## 6. independent arms と succ を含む元 grammar の検査

元 complete source interface が structural branch と independent W/Z 等を持つ場合、その tagged union/conjunction を保持する。構造 branch の π_E/χ_E^src は他の arm の実証拠ではない。

### CA4（元 clause grammar に沿った whole checking の合成）

各 genuine independent primitive/arm clause に対し、その **指定 target inlet** へ入る有限 full inclusion proof が与えられた時、CA3 とそれらから、その edge の全 complete χ_e を構成できる。

証明。元 relation/checking の有限 constructor derivation に帰納する。primitive/arm は指定 target への実証拠、source clause は CA3。Union は actual branch tag による有限 case elimination、Conjunction は同じ whole tuple の projections と元 introduction を使用する。Bind は actual RHS Return/current-world を共有し、Request は `Request(q,w,k) >>= S = Request(q,w,(a,w′).k(a,w′) >>= S)` で元未実行 suffix の checking を運ぶ。Scope/whole Rename は元の binder telescope と自然性に従う。登録再帰 references は元同時証明の既に証明された nodes を参照し、未証明の inclusion を ref という名前だけで完成させない。この client grammar の有限 source fold で新しい再帰 inclusion 仮定は不要である。各 map は同じ executable code、provider、world、guard、arm witness を保持する。従って全 complete interface の checking を得る。□

これは primitive の未知の full inclusion を新たに仮定して「一般 χ が閉じた」とする主張ではない。元の独立 arm 契約が何を供給すべきかを、actual target で正確に指定した構成である。型付き contract が存在することだけでは、この特定 target への包含を供給しない。

succ を追加するには、元 primitive contract が指定する argument/entry/body/return の full observations をそのまま CA2 の局所 Call case に入れる。actual succ に独立な request-free/Comp(empty,Int) realization law があり、全 applicable independent arms も同じ target を満たすなら、CA1 相当の局所補題が得られ、CA2/CA3 の構造帰納に一 case を加えるだけで全 FO grammar の χ_e を得る。実際に request がある場合は、その request/response/continuation を含む target の checking を作る必要がある。元 I_U/I_A がそれを認めなければ、その edge への χ_e は存在しない。

本稿は frozen builtin succ の complete operational declaration を供給したとはしない。`Int→Int` の印刷型も native Primitive identity も、必要な effect/arm law の代わりにはならない。この primitive case と独立 arm の target-specific checking は未解決の入力として残る。FO2 の元 unconditional closure は依然として宣言しない。

## 7. Receipt と親への差分

契約 [LET-FREE-CARRIER](../../tasks/agent-loop/sprints/let-free-carrier-20261024.md)、SHA-256 `8c1c7f1d4141984b6bb4799cd8aaca6a6cf365b530f3c18cd4fc5d17de65c4d7`。原 proofs/constructors の静的読取りと構造帰納による構成。実装・tests・build・probes・compiler run はない。

今回新たに構成したのは、literal/Name にとどまらない actual computed argument の全 source execution proof と、その actual Delay carrier の full criterion。CA4 は独立 arm の target-specific leaves を残す明示的な条件付き合成。全 abstract-interface 包含、computed-result descriptor、未知 primitive/arm laws、全 source/native/scoped-strategy 親を閉じたとはしない。独立査読待ち。


## 独立査読の受理範囲

査読対象 SHA-256 `c1b6a9d50831df355af771fe953654e23e15d3af1181e1c91814894151554b65`。`/root/astra_semantics_review` は、CA1–CA3 を実 h₀/f/g と succ を含まない source-carrier の範囲で受理した。CA4 は target-specific arm inclusions を前提とする条件付き合成として受理した。FO2 の無条件閉鎖ではない。 BLOCKING/MAJOR 指摘なし。本文の独立査読前表記は producer freeze の履歴。primary の査読後変更はこの status/receipt の追記のみ。[outcome](../../tasks/agent-loop/sprints/let-free-carrier-20261024-outcome.md) に元の未完了義務を保持する。
